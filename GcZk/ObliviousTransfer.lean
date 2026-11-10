/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.Commitment

/-!
# JKO with the Chou–Orlandi OT: zero knowledge

The ideal OT is replaced by the oblivious transfer of Chou and Orlandi [CO15] in a group `Gp` with
a generator `g` (every element is `b • g` for a unique `b : ZMod q`). For each input `j` the
verifier, as sender, sends `A = a • g`; the prover, as receiver with choice bit `w`, sends
`B = b • g + w A`; the verifier sends the pair of labels masked with the keys `HK(a • B)` and
`HK(a • (B - A))`, and the prover unmasks the label of `w` with `HK(b • A)`. When it opens its
seed, the verifier also opens its OT secrets `a`, so the prover checks both masked labels, not
only its own (there is no selective failure).

## Main result

* `GcZk.OT.zk_ot`: for every malicious verifier and every witness of a circuit that reads only the
  inputs `j < k`, the probabilities that the verifier outputs `1` in the real execution (with the
  real OT and the hash commitment) and with the simulator differ by at most
  `(q₀ + q₁ + q₂ + q₃) / |R|`. The simulator chooses the receiver messages `B` uniformly.

## Proof

The receiver's message `B = b • g + w A` is uniform in `Gp` whatever `w` is (`rmsg_bijective`).
For a fixed `B`, the prover's unmasked label is a function of the verifier's messages and `B`
(`recv_eq_mOf`), so the real OT is an ideal OT whose pairs depend on `B`, and the verifier is a
verifier of `GcZk.Com` (`toCom`). The prover's check, with the opened secrets, is sound
(`checkSound_ot`), and `GcZk.Com.zk_count` applies for each `B`.

## References

* [CO15] T. Chou, C. Orlandi, *The simplest protocol for oblivious transfer*, LATINCRYPT 2015.
-/

namespace GcZk.OT

open Com Jko

/-! ### Evaluation reads only the inputs that the circuit uses -/

section Locality

variable {V : Type*} [AddCommGroup V]

/-- Every input node of `C` reads an input `j < k`. -/
def InputsBelow (k : ℕ) (C : Circuit) : Prop := ∀ j, Node.input j ∈ C → j < k

theorem evalAux_congr_inp (H : ℕ → V → V) (k : ℕ) {inp inp' : ℕ → Wire V}
    (h : ∀ j < k, inp j = inp' j) :
    ∀ (C : Circuit) (M : List (Material V)) (ws : List (Wire V)), InputsBelow k C →
      evalAux H inp C M ws = evalAux H inp' C M ws
  | [], M, ws, _ => by cases M <;> rfl
  | _ :: _, [], ws, _ => rfl
  | n :: ns, m :: ms, ws, hC => by
    have hn : evalNode H inp ws n m = evalNode H inp' ws n m := by
      cases n with
      | input j => simp [evalNode, h j (hC j (by simp))]
      | _ => cases m <;> rfl
    simp only [evalAux, hn]
    exact evalAux_congr_inp H k h ns ms _ fun j hj ↦ hC j (by simp [hj])

end Locality

/-! ### The Chou–Orlandi OT -/

section Group

variable {q : ℕ} {Gp : Type*} [AddCommGroup Gp] [Module (ZMod q) Gp] (g : Gp)
  (hg : Function.Bijective fun b : ZMod q ↦ b • g)

/-- The discrete logarithm in base `g`. -/
noncomputable def dlog : Gp → ZMod q := (Equiv.ofBijective _ hg).symm

theorem dlog_smul (b : ZMod q) : dlog g hg (b • g) = b :=
  (Equiv.ofBijective _ hg).symm_apply_apply b

theorem smul_dlog (X : Gp) : dlog g hg X • g = X :=
  (Equiv.ofBijective _ hg).apply_symm_apply X

/-- The receiver's message for the secret `b` and the choice `w`. -/
def rmsg (b : ZMod q) (w : Bool) (A : Gp) : Gp := b • g + if w then A else 0

include hg in
/-- **Receiver privacy.** For every `A` and `w`, the receiver's message is a bijective function of
its secret, hence uniform. -/
theorem rmsg_bijective (w : Bool) (A : Gp) : Function.Bijective fun b : ZMod q ↦ rmsg g b w A :=
  (Equiv.addRight (if w then A else 0)).bijective.comp hg

variable {V : Type*} [AddCommGroup V] (HK : Gp → V)

/-- The receiver unmasks the label of its choice. -/
def recv (b : ZMod q) (A : Gp) (e : V × V) (w : Bool) : V :=
  (if w then e.2 else e.1) - HK (b • A)

/-- The label of the choice `c`, unmasked with the key that a receiver with message `B` would
have; a function of the sender's messages and `B` only. -/
noncomputable def mOf (A B : Gp) (e : V × V) (c : Bool) : V :=
  (if c then e.2 else e.1) - HK (dlog g hg (B - if c then A else 0) • A)

theorem recv_eq_mOf (b : ZMod q) (A : Gp) (e : V × V) (w : Bool) :
    recv HK b A e w = mOf g hg HK A (rmsg g b w A) e w := by
  simp [recv, mOf, rmsg, dlog_smul]

/-- With the sender's secret `a` (`A = a • g`), the labels are unmasked with the sender's keys. -/
theorem mOf_of_secret (a : ZMod q) (A B : Gp) (e : V × V) (c : Bool) (hA : A = a • g) :
    mOf g hg HK A B e c = (if c then e.2 else e.1) - HK (a • (B - if c then A else 0)) := by
  rw [mOf, hA, smul_comm, smul_dlog, ← hA]

end Group

/-! ### Verifiers with the real OT -/

/-- A deterministic malicious verifier for `k` inputs with the real OT and the hash commitment.
Phase 0: `q₀` queries, then the OT messages `A`. Phase 1: after the receiver messages `B`, `q₁`
queries, then the material and the masked label pairs. Phases 2 and 3 as in `GcZk.Com`; the
opening also contains the OT secrets. -/
structure OTVer (k q : ℕ) (V R D Gp : Type*) where
  q₀ : ℕ
  Q₀ : List D → V × R
  msgA : List D → Fin k → Gp
  q₁ : ℕ
  Q₁ : List D → (Fin k → Gp) → List D → V × R
  first : List D → (Fin k → Gp) → List D → List (Material V) × (Fin k → V × V)
  q₂ : ℕ
  Q₂ : List D → (Fin k → Gp) → List D → D → List D → V × R
  opening : List D → (Fin k → Gp) → List D → D → List D → Seed V × (Fin k → ZMod q)
  q₃ : ℕ
  Q₃ : List D → (Fin k → Gp) → List D → D → List D → Option (V × R) → List D → V × R
  out : List D → (Fin k → Gp) → List D → D → List D → Option (V × R) → List D → Bool

section Protocol

variable {k q : ℕ} {V R D Gp : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup Gp] [Module (ZMod q) Gp] (g : Gp) (hg : Function.Bijective fun b : ZMod q ↦ b • g)
  (HK : Gp → V) (Ve : OTVer k q V R D Gp)

/-- For fixed receiver messages `B`, the verifier is a verifier of `GcZk.Com`, whose OT pairs are
the labels unmasked with the receiver keys. -/
noncomputable def toCom (B : Fin k → Gp) : MalV V R D where
  q₁ := Ve.q₀ + Ve.q₁
  q₂ := Ve.q₂
  q₃ := Ve.q₃
  Q₁ a := if a.length < Ve.q₀ then Ve.Q₀ a else Ve.Q₁ (a.take Ve.q₀) B (a.drop Ve.q₀)
  first a := ((Ve.first (a.take Ve.q₀) B (a.drop Ve.q₀)).1, fun j ↦
    if h : j < k then
      (mOf g hg HK (Ve.msgA (a.take Ve.q₀) ⟨j, h⟩) (B ⟨j, h⟩)
          ((Ve.first (a.take Ve.q₀) B (a.drop Ve.q₀)).2 ⟨j, h⟩) false,
        mOf g hg HK (Ve.msgA (a.take Ve.q₀) ⟨j, h⟩) (B ⟨j, h⟩)
          ((Ve.first (a.take Ve.q₀) B (a.drop Ve.q₀)).2 ⟨j, h⟩) true)
    else (0, 0))
  Q₂ a c a₂ := Ve.Q₂ (a.take Ve.q₀) B (a.drop Ve.q₀) c a₂
  opening a c a₂ := (Ve.opening (a.take Ve.q₀) B (a.drop Ve.q₀) c a₂).1
  Q₃ a c a₂ f a₃ := Ve.Q₃ (a.take Ve.q₀) B (a.drop Ve.q₀) c a₂ f a₃
  out a c a₂ f a₃ := Ve.out (a.take Ve.q₀) B (a.drop Ve.q₀) c a₂ f a₃

/-- The prover's check after the opening, with the opened OT secrets: every `A` is `a • g`, the
material is the garbling of the opened seed, and both masked labels of every input unmask, with
the sender's keys, to `(L, L + Δ)`. It does not use the witness. -/
def chkOT (H : ℕ → V → V) (C : Circuit) (B : Fin k → Gp) (a : List D) (c : D) (a₂ : List D) :
    Prop :=
  (∀ j, Ve.msgA (a.take Ve.q₀) j =
      (Ve.opening (a.take Ve.q₀) B (a.drop Ve.q₀) c a₂).2 j • g) ∧
    (Ve.first (a.take Ve.q₀) B (a.drop Ve.q₀)).1 =
      (garble H (Ve.opening (a.take Ve.q₀) B (a.drop Ve.q₀) c a₂).1 C).2 ∧
    ∀ j : Fin k,
      (((Ve.first (a.take Ve.q₀) B (a.drop Ve.q₀)).2 j).1 -
          HK ((Ve.opening (a.take Ve.q₀) B (a.drop Ve.q₀) c a₂).2 j • B j),
        ((Ve.first (a.take Ve.q₀) B (a.drop Ve.q₀)).2 j).2 -
          HK ((Ve.opening (a.take Ve.q₀) B (a.drop Ve.q₀) c a₂).2 j •
            (B j - Ve.msgA (a.take Ve.q₀) j))) =
        ((Ve.opening (a.take Ve.q₀) B (a.drop Ve.q₀) c a₂).1.input j,
          (Ve.opening (a.take Ve.q₀) B (a.drop Ve.q₀) c a₂).1.input j +
            (Ve.opening (a.take Ve.q₀) B (a.drop Ve.q₀) c a₂).1.delta)

/-- **The check is sound.** If the circuit reads only the inputs `j < k` and `w` is a witness,
then whenever the check passes, the honest prover's label is the `1`-label computed from the
opened seed. -/
theorem checkSound_ot (H : ℕ → V → V) (C : Circuit) (o : ℕ) (w : ℕ → Bool)
    (hw : (plain w C).getD o false = true) (hC : InputsBelow k C) (B : Fin k → Gp) :
    CheckSound H C o w (toCom g hg HK Ve B) (chkOT g HK Ve H C B) := by
  intro a c a₂ ⟨hA, hM, hP⟩
  set σ := (Ve.opening (a.take Ve.q₀) B (a.drop Ve.q₀) c a₂).1
  have hpairs : ∀ j < k, otReceive ((toCom g hg HK Ve B).first a).2 w j = activeInputs σ w j := by
    intro j hj
    have hAj := hA ⟨j, hj⟩
    have e0 := mOf_of_secret g hg HK _ _ (B ⟨j, hj⟩)
      ((Ve.first (a.take Ve.q₀) B (a.drop Ve.q₀)).2 ⟨j, hj⟩) false hAj
    have e1 := mOf_of_secret g hg HK _ _ (B ⟨j, hj⟩)
      ((Ve.first (a.take Ve.q₀) B (a.drop Ve.q₀)).2 ⟨j, hj⟩) true hAj
    simp only [Bool.false_eq_true, ↓reduceIte, sub_zero] at e0
    simp only [↓reduceIte] at e1
    have hPj := hP ⟨j, hj⟩
    simp only [Prod.mk.injEq] at hPj
    simp only [otReceive, toCom, dite_eq_left hj, activeInputs, lab, e0, e1, hPj.1, hPj.2]
    cases w j <;> simp [σ, add_comm]
  have hev : eval H (otReceive ((toCom g hg HK Ve B).first a).2 w) C
      ((toCom g hg HK Ve B).first a).1 = eval H (activeInputs σ w) C (garble H σ C).2 := by
    rw [show ((toCom g hg HK Ve B).first a).1 = (garble H σ C).2 from hM]
    exact evalAux_congr_inp H k hpairs C _ [] hC
  simp only [zw, msg, hev, eval_garble, hw, lab_true]
  rfl

/-! ### The real execution and the simulator -/

variable (H : ℕ → V → V) (C : Circuit) (o : ℕ) (w : ℕ → Bool)
variable [DecidableEq V] [DecidableEq R]

/-- The receiver messages for the secrets `b`, against the `A` the verifier sends after its first
`q₀` queries to `G`. -/
def bof (b : Fin k → ZMod q) (G : V × R → D) : Fin k → Gp :=
  fun j ↦ rmsg g (b j) (w j) (Ve.msgA (ans G Ve.Q₀ Ve.q₀) j)

/-- The real execution with the real OT and the hash commitment: the prover's messages are
`B = b • g + w A`, it unmasks the label of its choice (`recv_eq_mOf`), commits with `G`, and
checks the opening with `chkOT`. -/
noncomputable def realOT (b : Fin k → ZMod q) (G : V × R → D) (r : R) : Bool :=
  real H C o w (toCom g hg HK Ve (bof g Ve w b G)) (chkOT g HK Ve H C (bof g Ve w b G)) G r

/-- The simulator: it chooses the receiver messages `B` uniformly and runs the simulator of
`GcZk.Com`. It does not use the witness. -/
noncomputable def simOT (B : Fin k → Gp) (G : V × R → D) (c : D) (r : R) : Bool :=
  sim H C o (toCom g hg HK Ve B) (chkOT g HK Ve H C B) G c r

variable [Fintype V] [Fintype R] [Fintype D] [Fintype Gp] [NeZero q]

omit [Module (ZMod 2) V] in
open Classical in
/-- The real wins, summed over the receiver secrets, are the wins of `GcZk.Com.real` summed over
uniform receiver messages. -/
theorem sum_realOT :
    ∑ b : Fin k → ZMod q, ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
        realOT g hg HK Ve H C o w b x.1 r).card =
      ∑ B : Fin k → Gp, ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
        real H C o w (toCom g hg HK Ve B) (chkOT g HK Ve H C B) x.1 r).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin k → Gp)))]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin k → Gp)))]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  refine Fintype.sum_bijective (fun b ↦ bof g Ve w b x.1) ?_ _ _ fun b ↦ rfl
  exact Function.Bijective.piMap (f := fun (j : Fin k) (b : ZMod q) ↦
    rmsg g b (w j) (Ve.msgA (ans x.1 Ve.Q₀ Ve.q₀) j)) fun j ↦ rmsg_bijective g hg (w j) _

open Classical in
/-- **Zero knowledge with the real OT and the hash commitment.** For every malicious verifier and
every witness of a circuit that reads only the inputs `j < k`, the probabilities that the verifier
outputs `1` in the real execution and with the simulator differ by at most
`(q₀ + q₁ + q₂ + q₃) / |R|`. -/
theorem zk_ot [Nonempty R] [Nonempty D] (hw : (plain w C).getD o false = true)
    (hC : InputsBelow k C) :
    |((∑ b : Fin k → ZMod q, ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
          realOT g hg HK Ve H C o w b x.1 r).card : ℕ) : ℝ) /
        (Fintype.card (Fin k → Gp) * Fintype.card ((V × R → D) × D) * Fintype.card R) -
      ((∑ B : Fin k → Gp, ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
          simOT g hg HK Ve H C o B x.1 x.2 r).card : ℕ) : ℝ) /
        (Fintype.card (Fin k → Gp) * Fintype.card ((V × R → D) × D) * Fintype.card R)| ≤
      ((Ve.q₀ + Ve.q₁ + Ve.q₂ + Ve.q₃ : ℕ) : ℝ) / Fintype.card R := by
  rw [sum_realOT]
  set X := Fintype.card ((V × R → D) × D)
  set NB := Fintype.card (Fin k → Gp)
  set Q := Ve.q₀ + Ve.q₁ + Ve.q₂ + Ve.q₃
  set Sr := ∑ B : Fin k → Gp, ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
    real H C o w (toCom g hg HK Ve B) (chkOT g HK Ve H C B) x.1 r).card
  set Ss := ∑ B : Fin k → Gp, ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
    simOT g hg HK Ve H C o B x.1 x.2 r).card
  have hq : ∀ B : Fin k → Gp, (toCom g hg HK Ve B).q₁ + (toCom g hg HK Ve B).q₂ +
      (toCom g hg HK Ve B).q₃ = Q := fun B ↦ by simp only [toCom, Q, Nat.add_assoc]
  have h1 : Sr ≤ Ss + NB * (Q * X) := by
    calc Sr ≤ ∑ B : Fin k → Gp, (∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
          simOT g hg HK Ve H C o B x.1 x.2 r).card + Q * X) :=
          Finset.sum_le_sum fun B _ ↦ by
            have := (zk_count H C o w (toCom g hg HK Ve B) (chkOT g HK Ve H C B)
              (checkSound_ot g hg HK Ve H C o w hw hC B)).1
            rw [hq] at this; exact this
      _ = Ss + NB * (Q * X) := by simp [Finset.sum_add_distrib, Ss, NB]
  have h2 : Ss ≤ Sr + NB * (Q * X) := by
    calc Ss ≤ ∑ B : Fin k → Gp, (∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
          real H C o w (toCom g hg HK Ve B) (chkOT g HK Ve H C B) x.1 r).card + Q * X) :=
          Finset.sum_le_sum fun B _ ↦ by
            have := (zk_count H C o w (toCom g hg HK Ve B) (chkOT g HK Ve H C B)
              (checkSound_ot g hg HK Ve H C o w hw hC B)).2
            rw [hq] at this; exact this
      _ = Sr + NB * (Q * X) := by simp [Finset.sum_add_distrib, Sr, NB]
  have pX : (0 : ℝ) < X := by exact_mod_cast Fintype.card_pos
  have pB : (0 : ℝ) < NB := by exact_mod_cast Fintype.card_pos
  have pR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have key : |(Sr : ℝ) - Ss| ≤ NB * (Q * X) := by
    have e1 : (Sr : ℝ) ≤ Ss + NB * (Q * X) := by exact_mod_cast h1
    have e2 : (Ss : ℝ) ≤ Sr + NB * (Q * X) := by exact_mod_cast h2
    rw [abs_sub_le_iff]; constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos (mul_pos (mul_pos pB pX) pR)]
  calc |(Sr : ℝ) - Ss| / (NB * X * Fintype.card R) ≤ NB * (Q * X) / (NB * X * Fintype.card R) :=
        div_le_div_of_nonneg_right key (mul_pos (mul_pos pB pX) pR).le
    _ = Q / Fintype.card R := by field_simp

end Protocol

end GcZk.OT
