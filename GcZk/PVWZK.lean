/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.PVWSound
import GcZk.ObliviousTransfer

/-!
# Zero knowledge with the PVW oblivious transfer

The verifier, as sender of the OT of `GcZk.PVW`, receives the prover's keys
`pk_j = keyGen(w_j, r_j)`, sends the material and the ciphertexts of both branches of every input,
and in the opening sends the seed and all the coins of the OT, as in the open-all phase of
[JKO13, Appendix A]. The prover decrypts the label of its choice, decodes it with a left inverse of
the encoding `ι`, commits with the hash commitment, and checks the opening: the material is the
garbling of the opened seed and every ciphertext is the encryption of the right label with the
opened coins. Labels are encoded into the group by any `ι` with a left inverse `decode`.

## Main results

* `GcZk.PVW.checkSound_pvw`: when the check passes, the honest prover's label is the `1`-label of
  the opened seed.
* `GcZk.PVW.zk_pvw`: for every common string, every malicious verifier and every witness, the
  real execution and the simulator (which sends the keys of the choice `0` and runs the simulator
  of `GcZk.Com`) differ by at most `(q₁ + q₂ + q₃) / |R|` plus the difference
  `|pHyb w - pHyb 0|`, where `pHyb x` is the probability that the verifier outputs `1` when it
  receives the keys of the choice `x` and talks to the simulator.
* `GcZk.PVW.pHyb_dec`: in decryption mode `pHyb x` does not depend on `x`, because the keys of
  the two choices have the same distribution [PVW08, Theorem 5.2, trapdoor key generation].
* `GcZk.PVW.zk_pvw_modes`: averaged over a set of messy common strings, the zero-knowledge error
  is at most `Q / |R|`, with `Q` a bound on the verifier's queries `q₁ + q₂ + q₃`, plus the
  advantages of the two distinguishers `pHyb w` and `pHyb 0` between that set and a set of
  decryption-mode strings.

`pHyb x` is computed from the common string by sampling the keys of `x` and running the verifier
with the simulator; it uses neither the witness beyond the bits `x` nor any trapdoor. Its advantage
between the two modes is bounded by DDH advantages in `GcZk.PVWDDH` (`GcZk.PVW.abs_modes_le`,
`GcZk.PVW.zk_pvw_ddh`), following [PVW08, Theorem 5.2].

## References

* [PVW08] C. Peikert, V. Vaikuntanathan, B. Waters, *A framework for efficient and composable
  oblivious transfer*, CRYPTO 2008.
* [JKO13] M. Jawurek, F. Kerschbaum, C. Orlandi, *Zero-knowledge using garbled circuits*, CCS 2013.
-/

namespace GcZk.PVW

open Com Jko OT

/-- A deterministic malicious verifier against the PVW OT and the hash commitment. It sees the
prover's keys, then as in `GcZk.Com`; its first message contains the ciphertexts and its opening
contains the coins of the OT. -/
structure PVer (k q : ℕ) (V R D Gp : Type*) where
  q₁ : ℕ
  Q₁ : (Fin k → Gp × Gp) → List D → V × R
  first : (Fin k → Gp × Gp) → List D → List (Material V) × Cts k Gp
  q₂ : ℕ
  Q₂ : (Fin k → Gp × Gp) → List D → D → List D → V × R
  opening : (Fin k → Gp × Gp) → List D → D → List D → Seed V × Coins k q
  q₃ : ℕ
  Q₃ : (Fin k → Gp × Gp) → List D → D → List D → Option (V × R) → List D → V × R
  out : (Fin k → Gp × Gp) → List D → D → List D → Option (V × R) → List D → Bool

section Protocol

variable {k q : ℕ} {V R D Gp : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup Gp] [Module (ZMod q) Gp] (c : Crs Gp) (ι : V → Gp) (decode : Gp → V)
  (Ve : PVer k q V R D Gp)

/-- The receiver's keys for the choice bits `x` and the secrets `r`. -/
def keys (x : ℕ → Bool) (r : Fin k → ZMod q) : Fin k → Gp × Gp :=
  fun j ↦ keyGen c (x j) (r j)

/-- For fixed keys and secrets, the verifier as a verifier of `GcZk.Com`: the OT pairs are the
decrypted labels of both branches (the honest prover uses only the one of its choice). -/
def toCom (pk : Fin k → Gp × Gp) (r : Fin k → ZMod q) : MalV V R D where
  q₁ := Ve.q₁
  q₂ := Ve.q₂
  q₃ := Ve.q₃
  Q₁ := Ve.Q₁ pk
  first a := ((Ve.first pk a).1, fun j ↦
    if h : j < k then
      (decode (dec (r ⟨j, h⟩) ((Ve.first pk a).2 ⟨j, h⟩ false)),
        decode (dec (r ⟨j, h⟩) ((Ve.first pk a).2 ⟨j, h⟩ true)))
    else (0, 0))
  Q₂ := Ve.Q₂ pk
  opening a cc a₂ := (Ve.opening pk a cc a₂).1
  Q₃ := Ve.Q₃ pk
  out := Ve.out pk

/-- The prover's check after the opening: the material is the garbling of the opened seed, and
every ciphertext is the encryption, with the opened coins, of the label of its branch. It does not
use the witness. -/
def chkP (H : ℕ → V → V) (C : Circuit) (pk : Fin k → Gp × Gp) (a : List D) (cc : D)
    (a₂ : List D) : Prop :=
  (Ve.first pk a).1 = (garble H (Ve.opening pk a cc a₂).1 C).2 ∧
    ∀ j b, (Ve.first pk a).2 j b = enc c (pk j) b
      (ι ((Ve.opening pk a cc a₂).1.input j + if b then (Ve.opening pk a cc a₂).1.delta else 0))
      ((Ve.opening pk a cc a₂).2 j b)

/-- **The check is sound.** If the circuit reads only the inputs `j < k` and `w` is a witness,
then whenever the check passes, the honest prover's label is the `1`-label of the opened seed. -/
theorem checkSound_pvw (H : ℕ → V → V) (C : Circuit) (o : ℕ) (w : ℕ → Bool)
    (hι : ∀ v, decode (ι v) = v) (hw : (plain w C).getD o false = true) (hC : InputsBelow k C)
    (r : Fin k → ZMod q) :
    CheckSound H C o w (toCom decode Ve (keys c w r) r) (chkP c ι Ve H C (keys c w r)) := by
  intro a cc a₂ ⟨hM, hP⟩
  set σ := (Ve.opening (keys c w r) a cc a₂).1
  have hpairs : ∀ j < k, otReceive ((toCom decode Ve (keys c w r) r).first a).2 w j =
      activeInputs σ w j := by
    intro j hj
    have h0 := hP ⟨j, hj⟩ false
    have h1 := hP ⟨j, hj⟩ true
    simp only [keys] at h0 h1
    simp only [otReceive, toCom, dite_eq_left hj, activeInputs, lab]
    cases hwj : w j
    · simp only [hwj] at h0
      simp [h0, dec_enc, hι, σ]
    · simp only [hwj] at h1
      simp [h1, dec_enc, hι, σ]
  have hev : eval H (otReceive ((toCom decode Ve (keys c w r) r).first a).2 w) C
      ((toCom decode Ve (keys c w r) r).first a).1 =
        eval H (activeInputs σ w) C (garble H σ C).2 := by
    rw [show ((toCom decode Ve (keys c w r) r).first a).1 = (garble H σ C).2 from hM]
    exact evalAux_congr_inp H k hpairs C _ [] hC
  simp only [zw, msg, hev, eval_garble, hw, lab_true]
  rfl

/-! ### The real execution, the hybrids and the simulator -/

variable (H : ℕ → V → V) (C : Circuit) (o : ℕ) (w : ℕ → Bool)
variable [DecidableEq V] [DecidableEq R]

/-- The real execution: the prover sends the keys of `w` with secrets `r`, decrypts the labels of
its choice, commits with `G`, and checks the opening with `chkP`. -/
noncomputable def realP (r : Fin k → ZMod q) (G : V × R → D) (rr : R) : Bool :=
  real H C o w (toCom decode Ve (keys c w r) r) (chkP c ι Ve H C (keys c w r)) G rr

/-- The hybrid for the choice bits `x`: the keys of `x` are sent, and the verifier talks to the
simulator of `GcZk.Com`. With `x = 0` this is the simulator, which does not use the witness. -/
noncomputable def hybP (x : ℕ → Bool) (r : Fin k → ZMod q) (G : V × R → D) (cc : D) (rr : R) :
    Bool :=
  sim H C o (toCom decode Ve (keys c x r) r) (chkP c ι Ve H C (keys c x r)) G cc rr

omit [Module (ZMod 2) V] in
/-- The simulator does not use the decryption keys: `hybP` depends on the secrets only through
the keys. -/
theorem sim_toCom (pk : Fin k → Gp × Gp) (r r' : Fin k → ZMod q) (G : V × R → D) (cc : D)
    (rr : R) :
    sim H C o (toCom decode Ve pk r) (chkP c ι Ve H C pk) G cc rr =
      sim H C o (toCom decode Ve pk r') (chkP c ι Ve H C pk) G cc rr := by
  simp only [Com.sim, play, simFin, msg, toCom]
  rfl

variable [Fintype V] [Fintype R] [Fintype D] [NeZero q]

/-- The probability that the verifier outputs `1` in the real execution. -/
noncomputable def pReal : ℝ :=
  open Classical in
  ((∑ r : Fin k → ZMod q, ∑ rr : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
      realP c ι decode Ve H C o w r x.1 rr).card : ℕ) : ℝ) /
    (Fintype.card (Fin k → ZMod q) * Fintype.card ((V × R → D) × D) * Fintype.card R)

/-- The probability that the verifier outputs `1` in the hybrid for `x`. -/
noncomputable def pHyb (x : ℕ → Bool) : ℝ :=
  open Classical in
  ((∑ r : Fin k → ZMod q, ∑ rr : R, (Finset.univ.filter fun y : (V × R → D) × D ↦
      hybP c ι decode Ve H C o x r y.1 y.2 rr).card : ℕ) : ℝ) /
    (Fintype.card (Fin k → ZMod q) * Fintype.card ((V × R → D) × D) * Fintype.card R)

omit [Module (ZMod 2) V] in
theorem pHyb_nonneg (x : ℕ → Bool) : 0 ≤ pHyb c ι decode Ve H C o x := by
  unfold pHyb; positivity

open Classical in
/-- The real execution and the hybrid for the witness differ by at most `(q₁ + q₂ + q₃) / |R|`. -/
theorem real_hyb [Nonempty R] [Nonempty D] (hι : ∀ v, decode (ι v) = v)
    (hw : (plain w C).getD o false = true) (hC : InputsBelow k C) :
    |pReal c ι decode Ve H C o w - pHyb c ι decode Ve H C o w| ≤
      ((Ve.q₁ + Ve.q₂ + Ve.q₃ : ℕ) : ℝ) / Fintype.card R := by
  set X := Fintype.card ((V × R → D) × D)
  set N := Fintype.card (Fin k → ZMod q)
  set Q := Ve.q₁ + Ve.q₂ + Ve.q₃
  set Sr := ∑ r : Fin k → ZMod q, ∑ rr : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
      realP c ι decode Ve H C o w r x.1 rr).card
  set Sh := ∑ r : Fin k → ZMod q, ∑ rr : R, (Finset.univ.filter fun y : (V × R → D) × D ↦
      hybP c ι decode Ve H C o w r y.1 y.2 rr).card
  have h1 : Sr ≤ Sh + N * (Q * X) := by
    calc Sr ≤ ∑ r : Fin k → ZMod q, (∑ rr : R, (Finset.univ.filter fun y : (V × R → D) × D ↦
          hybP c ι decode Ve H C o w r y.1 y.2 rr).card + Q * X) :=
          Finset.sum_le_sum fun r _ ↦
            (zk_count H C o w _ _ (checkSound_pvw c ι decode Ve H C o w hι hw hC r)).1
      _ = Sh + N * (Q * X) := by simp [Finset.sum_add_distrib, Sh, N]
  have h2 : Sh ≤ Sr + N * (Q * X) := by
    calc Sh ≤ ∑ r : Fin k → ZMod q, (∑ rr : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
          realP c ι decode Ve H C o w r x.1 rr).card + Q * X) :=
          Finset.sum_le_sum fun r _ ↦
            (zk_count H C o w _ _ (checkSound_pvw c ι decode Ve H C o w hι hw hC r)).2
      _ = Sr + N * (Q * X) := by simp [Finset.sum_add_distrib, Sr, N]
  have pX : (0 : ℝ) < X := by exact_mod_cast Fintype.card_pos
  have pN : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
  have pR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have key : |(Sr : ℝ) - Sh| ≤ N * (Q * X) := by
    have e1 : (Sr : ℝ) ≤ Sh + N * (Q * X) := by exact_mod_cast h1
    have e2 : (Sh : ℝ) ≤ Sr + N * (Q * X) := by exact_mod_cast h2
    rw [abs_sub_le_iff]; constructor <;> linarith
  simp only [pReal, pHyb]
  rw [← sub_div, abs_div, abs_of_pos (mul_pos (mul_pos pN pX) pR)]
  calc |(Sr : ℝ) - Sh| / (N * X * Fintype.card R) ≤ N * (Q * X) / (N * X * Fintype.card R) :=
        div_le_div_of_nonneg_right key (mul_pos (mul_pos pN pX) pR).le
    _ = Q / Fintype.card R := by field_simp

/-- **Zero knowledge with the PVW OT, for a fixed common string.** The real execution and the
simulator differ by at most `(q₁ + q₂ + q₃) / |R|` plus `|pHyb w - pHyb 0|`. -/
theorem zk_pvw [Nonempty R] [Nonempty D] (hι : ∀ v, decode (ι v) = v)
    (hw : (plain w C).getD o false = true) (hC : InputsBelow k C) :
    |pReal c ι decode Ve H C o w - pHyb c ι decode Ve H C o fun _ ↦ false| ≤
      ((Ve.q₁ + Ve.q₂ + Ve.q₃ : ℕ) : ℝ) / Fintype.card R +
        |pHyb c ι decode Ve H C o w - pHyb c ι decode Ve H C o fun _ ↦ false| := by
  have h := real_hyb c ι decode Ve H C o w hι hw hC
  have t := abs_sub_le (pReal c ι decode Ve H C o w) (pHyb c ι decode Ve H C o w)
    (pHyb c ι decode Ve H C o fun _ ↦ false)
  linarith

omit [Module (ZMod 2) V] in
open Classical in
/-- **In decryption mode the hybrids coincide.** -/
theorem pHyb_dec [Fact q.Prime] (hc : c.Dec q) (x x' : ℕ → Bool) :
    pHyb c ι decode Ve H C o x = pHyb c ι decode Ve H C o x' := by
  obtain ⟨xx, y, hy0, hy, hh⟩ := hc
  -- Both are sums over the keys of the choice `0`.
  have h : ∀ x : ℕ → Bool, (∑ r : Fin k → ZMod q, ∑ rr : R,
      (Finset.univ.filter fun z : (V × R → D) × D ↦ hybP c ι decode Ve H C o x r z.1 z.2 rr).card) =
      ∑ r : Fin k → ZMod q, ∑ rr : R, (Finset.univ.filter fun z : (V × R → D) × D ↦
        hybP c ι decode Ve H C o (fun _ ↦ false) r z.1 z.2 rr).card := by
    intro x
    have hk : ∀ r : Fin k → ZMod q,
        keys c x r = keys c (fun _ ↦ false) fun j ↦ if x j then y * r j else r j := by
      intro r; funext j
      simp only [keys]
      cases x j
      · rfl
      · simp [keyGen_dec c hy hh]
    have hbij : Function.Bijective fun (r : Fin k → ZMod q) (j : Fin k) ↦
        if x j then y * r j else r j := by
      refine Function.Bijective.piMap (f := fun (j : Fin k) (s : ZMod q) ↦
        if x j then y * s else s) fun j ↦ ?_
      cases x j
      · exact Function.bijective_id
      · exact (Equiv.mulLeft₀ y hy0).bijective
    refine Fintype.sum_bijective _ hbij _ _ fun r ↦ Finset.sum_congr rfl fun rr _ ↦ ?_
    have e : ∀ z : (V × R → D) × D, hybP c ι decode Ve H C o x r z.1 z.2 rr =
        hybP c ι decode Ve H C o (fun _ ↦ false) (fun j ↦ if x j then y * r j else r j)
          z.1 z.2 rr := fun z ↦ by
      simp only [hybP, hk r]
      exact sim_toCom c ι decode Ve H C o _ _ _ z.1 z.2 rr
    simp only [e]
  simp only [pHyb, h]

/-! ### Averaging over the common string -/

/-- **Zero knowledge with the PVW OT in messy mode.** Let the verifier depend on the common string,
with at most `Q` queries. Averaged over a nonempty set `Sm` of common strings (the messy ones, in
the protocol), the real execution and the simulator differ by at most `Q / |R|` plus the
advantages of the distinguishers `pHyb w` and `pHyb 0` between `Sm` and any set `Sd` of
decryption-mode strings. Under DDH these advantages are negligible [PVW08, Theorem 5.2]. -/
theorem zk_pvw_modes [Fact q.Prime] [Nonempty R] [Nonempty D] (Ve : Crs Gp → PVer k q V R D Gp)
    (Q : ℕ) (hQ : ∀ c, (Ve c).q₁ + (Ve c).q₂ + (Ve c).q₃ ≤ Q) (Sm Sd : Finset (Crs Gp))
    (hm : Sm.Nonempty) (hdec : ∀ c ∈ Sd, c.Dec q)
    (hι : ∀ v, decode (ι v) = v) (hw : (plain w C).getD o false = true) (hC : InputsBelow k C) :
    |(∑ c ∈ Sm, pReal c ι decode (Ve c) H C o w) / Sm.card -
        (∑ c ∈ Sm, pHyb c ι decode (Ve c) H C o fun _ ↦ false) / Sm.card| ≤
      (Q : ℝ) / Fintype.card R +
        |(∑ c ∈ Sm, pHyb c ι decode (Ve c) H C o w) / Sm.card -
          (∑ c ∈ Sd, pHyb c ι decode (Ve c) H C o w) / Sd.card| +
        |(∑ c ∈ Sd, pHyb c ι decode (Ve c) H C o fun _ ↦ false) / Sd.card -
          (∑ c ∈ Sm, pHyb c ι decode (Ve c) H C o fun _ ↦ false) / Sm.card| := by
  set R' : Crs Gp → ℝ := fun c ↦ pReal c ι decode (Ve c) H C o w
  set Hw : Crs Gp → ℝ := fun c ↦ pHyb c ι decode (Ve c) H C o w
  set H0 : Crs Gp → ℝ := fun c ↦ pHyb c ι decode (Ve c) H C o fun _ ↦ false
  have pm : (0 : ℝ) < Sm.card := by exact_mod_cast hm.card_pos
  have pR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  -- In decryption mode the two hybrids coincide.
  have hD : ∑ c ∈ Sd, Hw c = ∑ c ∈ Sd, H0 c :=
    Finset.sum_congr rfl fun c hc ↦ pHyb_dec c ι decode (Ve c) H C o (hdec c hc) _ _
  -- For each string, the real execution is close to the hybrid of the witness.
  have hRH : |(∑ c ∈ Sm, R' c) / Sm.card - (∑ c ∈ Sm, Hw c) / Sm.card| ≤ Q / Fintype.card R := by
    rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos pm, div_le_iff₀ pm]
    calc |∑ c ∈ Sm, (R' c - Hw c)| ≤ ∑ c ∈ Sm, |R' c - Hw c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _c ∈ Sm, (Q : ℝ) / Fintype.card R := Finset.sum_le_sum fun c _ ↦
          (real_hyb c ι decode (Ve c) H C o w hι hw hC).trans
            (div_le_div_of_nonneg_right (by exact_mod_cast hQ c) pR.le)
      _ = Q / Fintype.card R * Sm.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have e : (∑ c ∈ Sd, Hw c) / Sd.card = (∑ c ∈ Sd, H0 c) / Sd.card := by rw [hD]
  have t1 := abs_sub_le ((∑ c ∈ Sm, R' c) / Sm.card) ((∑ c ∈ Sm, Hw c) / Sm.card)
    ((∑ c ∈ Sm, H0 c) / Sm.card)
  have t2 := abs_sub_le ((∑ c ∈ Sm, Hw c) / Sm.card) ((∑ c ∈ Sd, Hw c) / Sd.card)
    ((∑ c ∈ Sm, H0 c) / Sm.card)
  have t3 : |(∑ c ∈ Sd, Hw c) / Sd.card - (∑ c ∈ Sm, H0 c) / Sm.card| =
      |(∑ c ∈ Sd, H0 c) / Sd.card - (∑ c ∈ Sm, H0 c) / Sm.card| := by rw [e]
  linarith

end Protocol

end GcZk.PVW
