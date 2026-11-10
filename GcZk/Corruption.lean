/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.PVWDDH
import GcZk.PVWSound
import GcZk.ObliviousTransfer

/-!
# Ingredients for adaptive corruptions

Against adaptive corruptions a simulator produces the prover's messages without the witness and,
when the prover is corrupted later, explains them: it produces internal randomness consistent with
the actual witness [GKPS18, Sect. 1.2]. In the protocol of [JKO13] the verifier has no input
and every step of the prover after the oblivious transfers is independent of the witness, so with
an ideal commitment what must be explained is the prover's view of the oblivious transfers
[GKPS18, Sect. 3.2]. With the hash commitment of the library, a prover corrupted after committing
also reveals the opening, and the simulator must equivocate the commitment. This file proves these
facts for the primitives of the library. It does not define adaptive security itself, which
belongs to a framework such as universal composability.

## Main results

* `GcZk.AC.ReceiverEquivocal`: the receiver's message of an OT can be produced without the choice
  bit, and its randomness explained for either bit, by bijections of the randomness
  [GKPS18, Sect. 3, Definition 3.1].
* `GcZk.AC.pvw_dec_equivocal`: the PVW receiver in decryption mode is receiver equivocal
  [GKPS18, Sect. 3.3, Theorem 3.2], exactly (the explained randomness is uniform).
* `GcZk.AC.pvw_messy_not_equivocal`: in messy mode it is not, which is why decryption mode is
  needed.
* `GcZk.AC.pvw_explain_dec`: the explained secret decrypts the branch of the actual choice, so the
  explained state is consistent with the labels the prover receives.
* `GcZk.AC.co_equivocal`: the Chou–Orlandi receiver is receiver equivocal for a party that knows
  the sender's secret `a`.
* `GcZk.AC.explain_prover`: with a receiver-equivocal OT, the prover's OT messages and its revealed
  view, for any witness and the explained randomness, are the simulated ones.
* `GcZk.AC.equivocate_rom`: the hash commitment can be equivocated by programming the oracle: a
  prover corrupted after committing reveals `(Z_w, r)`, and a simulator that committed to a
  uniform value and programs `G(Z_w, r)` at the corruption is off by at most `(q₁ + q₂) / |R|`.
* `GcZk.AC.prob_accept_dec_le`: soundness with the PVW OT in decryption mode, the mode in which it
  is receiver equivocal: averaged over decryption-mode strings, the acceptance probability is at
  most the messy-mode bound plus the DDH advantage of an explicit distinguisher plus `3 / q`.

## References

* [PVW08] C. Peikert, V. Vaikuntanathan, B. Waters, *A framework for efficient and composable
  oblivious transfer*, CRYPTO 2008.
* [GKPS18] C. Ganesh, Y. Kondi, A. Patra, P. Sarkar, *Efficient adaptively secure zero-knowledge
  from garbled circuits*, PKC 2018.
* [JKO13] M. Jawurek, F. Kerschbaum, C. Orlandi, *Zero-knowledge using garbled circuits: how to
  prove non-algebraic statements efficiently*, CCS 2013.
-/

namespace GcZk.AC

/-! ### Receiver equivocality -/

/-- The receiver of an OT, with message `msg σ r` for the choice `σ` and randomness `r`, is
*receiver equivocal* with simulated message `sim` and explanations `e` if each `e σ` is a bijection
of the randomness and `msg σ (e σ r) = sim r`. A simulator sends `sim r` for a uniform `r`; told the
choice `σ` later, it explains its message by the randomness `e σ r`, which is uniform because `e σ`
is a bijection. -/
def ReceiverEquivocal {Rr M : Type*} (msg : Bool → Rr → M) (sim : Rr → M) (e : Bool → Rr → Rr) :
    Prop :=
  (∀ σ, Function.Bijective (e σ)) ∧ ∀ σ r, msg σ (e σ r) = sim r

section PVW

open PVW

variable {q : ℕ} [Fact q.Prime] {Gp : Type*} [AddCommGroup Gp] [Module (ZMod q) Gp]

/-- **The PVW receiver in decryption mode is receiver equivocal.** If `g₁ = y g₀` with `y ≠ 0` and
`h_b = x g_b`, the key of the choice `0` with randomness `r` is also the key of the choice `1` with
randomness `y⁻¹ r`. -/
theorem pvw_dec_equivocal (c : Crs Gp) {x y : ZMod q} (hy0 : y ≠ 0)
    (hy : c.g true = y • c.g false) (hh : ∀ b, c.h b = x • c.g b) :
    ReceiverEquivocal (keyGen c) (keyGen c false) (fun σ r ↦ if σ then y⁻¹ * r else r) := by
  refine ⟨fun σ ↦ ?_, fun σ r ↦ ?_⟩
  · cases σ
    · exact Function.bijective_id
    · simp only [↓reduceIte]
      exact (mulLeft_bijective₀ _ (inv_ne_zero hy0))
  · cases σ
    · rfl
    · simp only [↓reduceIte]
      rw [keyGen_dec c hy hh, ← mul_assoc, mul_inv_cancel₀ hy0, one_mul]

/-- The PVW receiver is receiver equivocal on every decryption-mode common string. -/
theorem pvw_dec_equivocal' (c : Crs Gp) (hc : c.Dec q) :
    ∃ e : Bool → ZMod q → ZMod q, ReceiverEquivocal (keyGen c) (keyGen c false) e := by
  obtain ⟨x, y, hy0, hy, hh⟩ := hc
  exact ⟨_, pvw_dec_equivocal c hy0 hy hh⟩

/-- **In messy mode the PVW receiver is not receiver equivocal.** On a messy common string the
keys of the two choices meet only at the secret `0`: from `r₀ g₀ = r₁ g₁` and
`r₀ x₀ g₀ = r₁ x₁ g₁` follows `(x₀ - x₁) r₀ g₀ = 0`, so `r₀ = 0`. Hence no explanation of the
choice `0` is a bijection. This is why decryption mode is needed for receiver equivocality. -/
theorem pvw_messy_not_equivocal (c : Crs Gp) {t : Bool → ZMod q} (hc : c.Messy t)
    (sim : ZMod q → Gp × Gp) (e : Bool → ZMod q → ZMod q) :
    ¬ ReceiverEquivocal (keyGen c) sim e := by
  rintro ⟨hb, he⟩
  have h0 : ∀ r, e false r = 0 := by
    intro r
    have k := (he false r).trans (he true r).symm
    simp only [keyGen, Prod.mk.injEq, hc.h_eq] at k
    obtain ⟨k1, k2⟩ := k
    have h : (t false - t true) • (e false r • c.g false) = 0 := by
      rw [sub_smul, sub_eq_zero]
      calc t false • (e false r • c.g false) = e false r • t false • c.g false := smul_comm _ _ _
        _ = e true r • t true • c.g true := k2
        _ = t true • (e true r • c.g true) := smul_comm _ _ _
        _ = t true • (e false r • c.g false) := by rw [k1]
    rcases smul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hc.x_ne
    · exact (smul_eq_zero.1 h).resolve_right (hc.g_ne false)
  exact zero_ne_one ((hb false).1 ((h0 0).trans (h0 1).symm))

end PVW

section PVWExplain

open PVW

variable {q : ℕ} {Gp : Type*} [AddCommGroup Gp] [Module (ZMod q) Gp]

/-- **The explained secret decrypts.** If the explanations make the PVW receiver equivocal, then
the explained secret `e σ r` decrypts what the sender encrypts on branch `σ` under the simulated
key: the explained state is consistent with the label the prover receives. -/
theorem pvw_explain_dec {c : Crs Gp} {e : Bool → ZMod q → ZMod q}
    (hRE : ReceiverEquivocal (keyGen c) (keyGen c false) e) (σ : Bool) (r : ZMod q) (m : Gp)
    (st : ZMod q × ZMod q) :
    dec (e σ r) (enc c (keyGen c false r) σ m st) = m := by
  rw [← hRE.2 σ r]
  exact dec_enc c σ (e σ r) m st

end PVWExplain

section CO

variable {q : ℕ} {Gp : Type*} [AddCommGroup Gp] [Module (ZMod q) Gp] (g : Gp)

/-- **The Chou–Orlandi receiver is receiver equivocal for a party that knows the sender's
secret.** With `A = a g`, the message `b g + w A` of the choice `w` with randomness `b` is
`b' g` for `b' = b + w a`, and the explanation subtracts `w a`. -/
theorem co_equivocal (a : ZMod q) :
    ReceiverEquivocal (fun w b ↦ OT.rmsg g b w (a • g)) (fun b ↦ b • g)
      (fun w b ↦ if w then b - a else b) := by
  refine ⟨fun w ↦ ?_, fun w b ↦ ?_⟩
  · cases w
    · exact Function.bijective_id
    · simp only [↓reduceIte]
      exact (Equiv.subRight a).bijective
  · cases w
    · simp [OT.rmsg]
    · simp only [OT.rmsg, ↓reduceIte, sub_smul]
      abel

end CO

/-! ### Explaining the prover -/

section Explain

open Jko

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Rr M : Type*}
  {msg : Bool → Rr → M} {sim : Rr → M} {e : Bool → Rr → Rr}

/-- The explanation of the simulated randomness `rs` for the witness `w`. -/
def explainRand (e : Bool → Rr → Rr) (w : ℕ → Bool) (rs : ℕ → Rr) : ℕ → Rr :=
  fun j ↦ e (w j) (rs j)

omit [AddCommGroup V] [Module (ZMod 2) V] in
/-- The explained randomness is uniform: explaining is a bijection of the randomness. -/
theorem explainRand_bijective (hRE : ReceiverEquivocal msg sim e) (w : ℕ → Bool) :
    Function.Bijective (explainRand e w) := by
  refine ⟨fun rs rs' h ↦ funext fun j ↦ (hRE.1 (w j)).1 (congrFun h j), fun t ↦ ?_⟩
  refine ⟨fun j ↦ Function.surjInv (hRE.1 (w j)).2 (t j), funext fun j ↦ ?_⟩
  exact Function.surjInv_eq (hRE.1 (w j)).2 (t j)

/-- **Explaining the prover.** Let the OT receiver be receiver equivocal, and let the verifier
choose its messages `Ver B` as a function of the prover's OT messages `B`. For a witness `w`, the
prover with the explained randomness sends the simulated OT messages, and the verifier's view of it
(the opened label, or an abort) is the simulator's. With an ideal commitment this is everything a
simulator must explain when the prover is corrupted [GKPS18, Sect. 3.2]. -/
theorem explain_prover (hRE : ReceiverEquivocal msg sim e) (H : ℕ → V → V) (C : Circuit)
    (out : ℕ) {w : ℕ → Bool} (hw : (plain w C).getD out false = true)
    (Ver : (ℕ → M) → VerifierMsg V) (rs : ℕ → Rr) :
    (fun j ↦ msg (w j) (explainRand e w rs j)) = (fun j ↦ sim (rs j)) ∧
      view H C out w (Ver fun j ↦ msg (w j) (explainRand e w rs j)) =
        Jko.sim H C out (Ver fun j ↦ sim (rs j)) := by
  have hm : (fun j ↦ msg (w j) (explainRand e w rs j)) = (fun j ↦ sim (rs j)) :=
    funext fun j ↦ hRE.2 (w j) (rs j)
  refine ⟨hm, ?_⟩
  rw [hm]
  exact zk H C out hw _

end Explain

/-! ### Equivocating the hash commitment -/

section Commitment

open Com Jko

variable {V R D : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (H : ℕ → V → V) (C : Circuit) (o : ℕ) (w : ℕ → Bool) (A : MalV V R D)

/-- The check that always passes. With it, the last message `GcZk.Com.realFin` of the games of
`GcZk.Com` is always `(Z_w, r)`: the prover's state after the commitment (its output label and its
commitment randomness), which a corrupted prover reveals. -/
def noCheck : List D → D → List D → Prop := fun _ _ _ ↦ True

variable [DecidableEq V] [DecidableEq R]

/-- The simulator against a prover corrupted after committing: it commits to a uniform `c`, answers
the oracle queries with `G` until the corruption, and then, knowing the witness, reveals
`(Z_w, r)` and programs `G(Z_w, r) := c`. -/
noncomputable def simC (G : V × R → D) (c : D) (r : R) : Bool :=
  play A G G (fun _ ↦ Function.update G (point H C o w A G r) c) c
    (realFin H C o w A noCheck r)

omit [Module (ZMod 2) V] in
/-- Off the bad events, the hybrid of `GcZk.Com` and the corruption simulator agree: they differ
only in the oracle of the second phase, which is programmed in the hybrid. -/
theorem hyb_eq_simC (G : V × R → D) (c : D) (r : R)
    (h : ¬ Bad₂₃ H C o w A noCheck G c r) :
    hyb H C o w A noCheck G c r = simC H C o w A G c r := by
  simp only [Bad₂₃, not_or] at h
  have e2 := ans_update G (A.Q₂ (ans G A.Q₁ A.q₁) c) A.q₂ (point H C o w A G r) c h.1
  unfold hyb simC play
  rw [e2]

omit [Module (ZMod 2) V] [DecidableEq V] [DecidableEq R] in
/-- With `noCheck` the last message is never an abort, so the bad event of the second and third
phases is a query of the second phase at the commitment point. -/
theorem bad₂₃_noCheck (G : V × R → D) (c : D) (r : R) :
    Bad₂₃ H C o w A noCheck G c r ↔
      Hits G (A.Q₂ (ans G A.Q₁ A.q₁) c) A.q₂ (point H C o w A G r) := by
  simp [Bad₂₃, realFin, noCheck]

section Counting

variable [Fintype V] [Fintype R] [Fintype D]

omit [Module (ZMod 2) V] in
open Classical in
theorem card_realC_le (r : R) :
    (Finset.univ.filter fun x : (V × R → D) × D ↦ real H C o w A noCheck x.1 r).card ≤
      (Finset.univ.filter fun x : (V × R → D) × D ↦ simC H C o w A x.1 x.2 r).card +
        (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
        (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A noCheck x.1 x.2 r).card := by
  have h1 : (Finset.univ.filter fun x : (V × R → D) × D ↦ real H C o w A noCheck x.1 r).card ≤
      (Finset.univ.filter fun x : (V × R → D) × D ↦
        ¬ Bad₁ H C o w A x.1 r ∧ real H C o w A noCheck x.1 r).card +
      (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card := by
    refine (Finset.card_le_card fun x hx ↦ ?_).trans (Finset.card_union_le _ _)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    by_cases hb : Bad₁ H C o w A x.1 r
    · exact Or.inr hb
    · exact Or.inl ⟨hb, hx⟩
  have h2 : (Finset.univ.filter fun x : (V × R → D) × D ↦
        ¬ Bad₁ H C o w A x.1 r ∧ hyb H C o w A noCheck x.1 x.2 r).card ≤
      (Finset.univ.filter fun x : (V × R → D) × D ↦ simC H C o w A x.1 x.2 r).card +
      (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A noCheck x.1 x.2 r).card := by
    refine (Finset.card_le_card fun x hx ↦ ?_).trans (Finset.card_union_le _ _)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    by_cases hb : Bad₂₃ H C o w A noCheck x.1 x.2 r
    · exact Or.inr hb
    · exact Or.inl ((hyb_eq_simC H C o w A x.1 x.2 r hb) ▸ hx.2)
  rw [← card_hyb_eq_card_real] at h1
  omega

omit [Module (ZMod 2) V] in
open Classical in
theorem card_simC_le (r : R) :
    (Finset.univ.filter fun x : (V × R → D) × D ↦ simC H C o w A x.1 x.2 r).card ≤
      (Finset.univ.filter fun x : (V × R → D) × D ↦ real H C o w A noCheck x.1 r).card +
        (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
        (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A noCheck x.1 x.2 r).card := by
  have h1 : (Finset.univ.filter fun x : (V × R → D) × D ↦ simC H C o w A x.1 x.2 r).card ≤
      (Finset.univ.filter fun x : (V × R → D) × D ↦
        ¬ Bad₁ H C o w A x.1 r ∧ hyb H C o w A noCheck x.1 x.2 r).card +
      ((Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
      (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A noCheck x.1 x.2 r).card) := by
    refine (Finset.card_le_card fun x hx ↦ ?_).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    by_cases hb : Bad₁ H C o w A x.1 r
    · exact Or.inr (Or.inl hb)
    by_cases hb' : Bad₂₃ H C o w A noCheck x.1 x.2 r
    · exact Or.inr (Or.inr hb')
    exact Or.inl ⟨hb, (hyb_eq_simC H C o w A x.1 x.2 r hb').symm ▸ hx⟩
  have h2 : (Finset.univ.filter fun x : (V × R → D) × D ↦
        ¬ Bad₁ H C o w A x.1 r ∧ real H C o w A noCheck x.1 r).card ≤
      (Finset.univ.filter fun x : (V × R → D) × D ↦ real H C o w A noCheck x.1 r).card :=
    Finset.card_le_card fun x hx ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (Finset.mem_filter.1 hx).2.2⟩
  rw [card_hyb_eq_card_real] at h1
  omega

omit [Module (ZMod 2) V] in
open Classical in
/-- **Equivocating the hash commitment.** A malicious verifier corrupts the prover after its
commitment and receives the prover's state `(Z_w, r)`. In the real execution the commitment is
`G(Z_w, r)`. The simulator commits to a uniform `c` without the witness and, at the corruption,
reveals `(Z_w, r)` and programs `G(Z_w, r) := c` (`simC`). Over `G`, `c` and `r` uniform, the
probabilities that the verifier outputs `1` differ by at most `(q₁ + q₂) / |R|`: the queries made
after the corruption cost nothing, since both games then answer with the programmed oracle. -/
theorem equivocate_rom [Nonempty R] [Nonempty D] :
    |((∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
        real H C o w A noCheck x.1 r).card : ℕ) : ℝ) /
        (Fintype.card ((V × R → D) × D) * Fintype.card R) -
      ((∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
          simC H C o w A x.1 x.2 r).card : ℕ) : ℝ) /
        (Fintype.card ((V × R → D) × D) * Fintype.card R)| ≤
      ((A.q₁ + A.q₂ : ℕ) : ℝ) / Fintype.card R := by
  set Sr := ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
    real H C o w A noCheck x.1 r).card
  set Ss := ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦ simC H C o w A x.1 x.2 r).card
  set B₁ := ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card
  set B₂ := ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
    Bad₂₃ H C o w A noCheck x.1 x.2 r).card
  set X := Fintype.card ((V × R → D) × D)
  set n := A.q₁ + A.q₂
  have hB : B₁ + B₂ ≤ n * X := by
    -- The same verifier without the queries of the third phase has the same bad events.
    have h := sum_bad_le H C o w ({ A with q₃ := 0 } : MalV V R D) noCheck
    have e : B₂ = ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
        Bad₂₃ H C o w ({ A with q₃ := 0 } : MalV V R D) noCheck x.1 x.2 r).card := by
      refine Finset.sum_congr rfl fun r _ ↦ congrArg Finset.card
        (Finset.filter_congr fun x _ ↦ ?_)
      rw [bad₂₃_noCheck, bad₂₃_noCheck]
      rfl
    rw [e]
    simp only [add_zero] at h
    exact h
  have hr : Sr ≤ Ss + B₁ + B₂ := by
    calc Sr ≤ ∑ r : R, ((Finset.univ.filter fun x : (V × R → D) × D ↦
            simC H C o w A x.1 x.2 r).card +
          (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
          (Finset.univ.filter fun x : (V × R → D) × D ↦
            Bad₂₃ H C o w A noCheck x.1 x.2 r).card) :=
          Finset.sum_le_sum fun r _ ↦ card_realC_le H C o w A r
      _ = Ss + B₁ + B₂ := by simp only [Finset.sum_add_distrib, Ss, B₁, B₂]
  have hs : Ss ≤ Sr + B₁ + B₂ := by
    calc Ss ≤ ∑ r : R, ((Finset.univ.filter fun x : (V × R → D) × D ↦
            real H C o w A noCheck x.1 r).card +
          (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
          (Finset.univ.filter fun x : (V × R → D) × D ↦
            Bad₂₃ H C o w A noCheck x.1 x.2 r).card) :=
          Finset.sum_le_sum fun r _ ↦ card_simC_le H C o w A r
      _ = Sr + B₁ + B₂ := by simp only [Finset.sum_add_distrib, Sr, B₁, B₂]
  have hX : (0 : ℝ) < X := by exact_mod_cast Fintype.card_pos
  have hS : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have key : |(Sr : ℝ) - Ss| ≤ (n : ℝ) * X := by
    have h1 : (Sr : ℝ) ≤ Ss + n * X := by exact_mod_cast (hr.trans (by omega))
    have h2 : (Ss : ℝ) ≤ Sr + n * X := by exact_mod_cast (hs.trans (by omega))
    rw [abs_sub_le_iff]
    constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos (mul_pos hX hS)]
  calc |(Sr : ℝ) - Ss| / (X * Fintype.card R) ≤ (n * X) / (X * Fintype.card R) :=
        div_le_div_of_nonneg_right key (mul_pos hX hS).le
    _ = n / Fintype.card R := by field_simp

end Counting

end Commitment

/-! ### Soundness in decryption mode -/

section Dec

open PVW Finset

variable {q : ℕ} [Fact q.Prime] {Gp : Type*} [AddCommGroup Gp] [Module (ZMod q) Gp] [Fintype Gp]
  [DecidableEq Gp] {k : ℕ} {V R D : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Fintype V] [Fintype R] [Fintype D]

/-- The messy common strings of `GcZk.PVW.crsM` are messy, with trapdoor `(x₀, x₁)`. -/
theorem crsM_messy (p : Gp × Gp × ZMod q × ZMod q) (hp : p ∈ (parM : Finset _)) :
    (crsM p).Messy (fun b ↦ cond b p.2.2.2 p.2.2.1) := by
  simp only [parM, nz, nzq, mem_product, mem_filter, mem_univ, true_and, mem_offDiag] at hp
  refine ⟨fun b ↦ ?_, hp.2.2.2.2, fun b ↦ ?_⟩
  · cases b
    · exact hp.1
    · exact hp.2.1
  · cases b <;> rfl

open Classical in
/-- The probability that the verifier accepts the cheating prover `P` on the common string `c`
(the left side of `GcZk.PVW.prob_accept_le`). -/
noncomputable def pAcc (C : Circuit) (out : ℕ) (ι : V → Gp) (c : Crs Gp)
    (P : PVW.Prover k q V R D Gp) : ℝ :=
  ((∑ Δ ∈ univ.filter (· ≠ (0 : V)), ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V,
      ∑ H : Fin C.length → V → V, ∑ rnd : Coins k q,
        (univ.filter fun G : V × R → D ↦ RealAccept C out k c ι P Δ H Lin Lc G rnd).card : ℕ) :
      ℝ) /
    (Fintype.card (Coins k q) * ((univ.filter (· ≠ (0 : V))).card *
      Fintype.card (Fin k → V) * Fintype.card (Fin C.length → V) *
      Fintype.card (Fin C.length → V → V) * Fintype.card (V × R → D)))

omit [Fintype Gp] [DecidableEq Gp] [Module (ZMod 2) V] in
theorem pAcc_nonneg (C : Circuit) (out : ℕ) (ι : V → Gp) (c : Crs Gp)
    (P : PVW.Prover k q V R D Gp) : 0 ≤ pAcc (R := R) (D := D) C out ι c P := by
  unfold pAcc; positivity

omit [Fintype Gp] [DecidableEq Gp] [Module (ZMod 2) V] in
open Classical in
theorem pAcc_le_one (C : Circuit) (out : ℕ) (ι : V → Gp) (c : Crs Gp)
    (P : PVW.Prover k q V R D Gp) : pAcc (R := R) (D := D) C out ι c P ≤ 1 := by
  unfold pAcc
  apply div_le_one_of_le₀ _ (by positivity)
  have h : (∑ Δ ∈ univ.filter (· ≠ (0 : V)), ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V,
      ∑ H : Fin C.length → V → V, ∑ rnd : Coins k q,
        (univ.filter fun G : V × R → D ↦ RealAccept C out k c ι P Δ H Lin Lc G rnd).card) ≤
      ∑ _Δ ∈ univ.filter (· ≠ (0 : V)), ∑ _Lin : Fin k → V, ∑ _Lc : Fin C.length → V,
        ∑ _H : Fin C.length → V → V, ∑ _rnd : Coins k q, Fintype.card (V × R → D) :=
    sum_le_sum fun _ _ ↦ sum_le_sum fun _ _ ↦ sum_le_sum fun _ _ ↦ sum_le_sum fun _ _ ↦
      sum_le_sum fun _ _ ↦ card_le_univ _
  simp only [sum_const, card_univ, smul_eq_mul] at h
  rw [← Nat.cast_le (α := ℝ)] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

variable (hcard : Fintype.card Gp = q)

include hcard in
/-- **Soundness in decryption mode.** The PVW OT is receiver equivocal in decryption mode
(`pvw_dec_equivocal`), but not in messy mode (`pvw_messy_not_equivocal`); in decryption mode the
sender is protected only computationally. A cheating prover
`Pc c` that sees the common string `c` and makes at most `N₁` and `N₂` oracle queries convinces the
verifier of an unsatisfiable circuit, on average over the decryption-mode strings, with probability
at most the messy-mode bound of `GcZk.PVW.prob_accept_le` plus the DDH advantage of the acceptance
probability plus `3 / q`. The switch between the modes is [PVW08, Theorem 5.2] (see
`GcZk.PVW.abs_modes_le`). -/
theorem prob_accept_dec_le [Nontrivial V] [Nonempty D] (hq : 2 < q) (C : Circuit) (out : ℕ)
    (ι : V → Gp) (hC : ∀ x : ℕ → Bool, (plain x C).getD out false = false)
    (Pc : Crs Gp → PVW.Prover k q V R D Gp) (N₁ N₂ : ℕ)
    (hN : ∀ c, (Pc c).n₁ ≤ N₁ ∧ (Pc c).n₂ ≤ N₂) :
    avg (parD : Finset (Gp × ZMod q × ZMod q))
        (fun p ↦ pAcc (R := R) (D := D) C out ι (crsD p) (Pc (crsD p))) ≤
      ((N₁ + 1 : ℕ) : ℝ) / (Fintype.card V - 1) + ((N₁ * N₁ + N₂ + 1 : ℕ) : ℝ) / Fintype.card D +
        advDDH (q := q) (fun c ↦ pAcc (R := R) (D := D) C out ι c (Pc c)) + 3 / q := by
  set F : Crs Gp → ℝ := fun c ↦ pAcc (R := R) (D := D) C out ι c (Pc c)
  set B : ℝ := ((N₁ + 1 : ℕ) : ℝ) / (Fintype.card V - 1) +
    ((N₁ * N₁ + N₂ + 1 : ℕ) : ℝ) / Fintype.card D
  have hV : (0 : ℝ) < Fintype.card V - 1 := by
    have : (1 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.one_lt_card
    linarith
  have hD : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hM : ∀ p ∈ (parM : Finset (Gp × Gp × ZMod q × ZMod q)), F (crsM p) ≤ B := by
    intro p hp
    refine (PVW.prob_accept_le C out k (crsM p) ι (Pc (crsM p)) hcard
      (fun b ↦ cond b p.2.2.2 p.2.2.1) (crsM_messy p hp)
      hC).trans ?_
    obtain ⟨h1, h2⟩ := hN (crsM p)
    have e1 : (((Pc (crsM p)).n₁ + 1 : ℕ) : ℝ) ≤ ((N₁ + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right h1 1
    have e2 : (((Pc (crsM p)).n₁ * (Pc (crsM p)).n₁ + (Pc (crsM p)).n₂ + 1 : ℕ) : ℝ) ≤
        ((N₁ * N₁ + N₂ + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul h1 h1) h2) 1
    exact add_le_add (div_le_div_of_nonneg_right e1 hV.le) (div_le_div_of_nonneg_right e2 hD.le)
  have hne := parM_nonempty hcard hq
  have hMavg : avg (parM : Finset (Gp × Gp × ZMod q × ZMod q)) (fun p ↦ F (crsM p)) ≤ B := by
    have ps : (0 : ℝ) < (parM : Finset (Gp × Gp × ZMod q × ZMod q)).card := by
      exact_mod_cast hne.card_pos
    rw [avg, div_le_iff₀ ps]
    calc ∑ p ∈ (parM : Finset (Gp × Gp × ZMod q × ZMod q)), F (crsM p) ≤
          ∑ _p ∈ (parM : Finset (Gp × Gp × ZMod q × ZMod q)), B := sum_le_sum hM
      _ = B * (parM : Finset (Gp × Gp × ZMod q × ZMod q)).card := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
  have hmodes := abs_modes_le hcard hq F (fun c ↦ pAcc_nonneg C out ι c (Pc c))
    (fun c ↦ pAcc_le_one C out ι c (Pc c))
  rw [abs_sub_le_iff] at hmodes
  linarith [hmodes.2]

end Dec

end GcZk.AC
