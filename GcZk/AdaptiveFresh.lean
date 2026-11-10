/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.AdaptiveShift

/-!
# Adaptive authenticity: fresh labels

In the simulated game, the randomness for which the query at step `k` hits the active label of a
selector that is unknown at step `k`, with no earlier query at the active point of such a
selector, is at most a fraction `1 / |V|` of all of it (`card_freshHit_le`). The proof shifts
the randomness at the last atom of the selector (`GcZk.Adaptive.plab_shiftH`,
`GcZk.Adaptive.plab_shiftR`): the shift does not change the run up to step `k`, changes the
label by exactly the shift, and can be undone.
-/

namespace GcZk.Adaptive

open Auth RO Lin

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

section Shift

variable (C : Circuit) (m : ℕ)

open Classical in
/-- The last multiplexer atom of the linear part of `s`. -/
noncomputable def iStar (x : ℕ → Bool) (rq : ℕ → Bool) (s : ℕ) : ℕ :=
  Nat.findGreatest (fun i ↦ pl x rq C s (.inr i) ≠ 0) s

open Classical in
/-- The shift by `v` at the last atom of the linear part of `s`: the hash at the point read by
the last multiplexer atom, or, if there is none, the label of the first input atom. -/
noncomputable def shiftOf (x : ℕ → Bool) (rq : ℕ → Bool) (s : ℕ) (σ : Rand V m C.length)
    (v : V) : Rand V m C.length :=
  if ∃ i, i ≤ s ∧ pl x rq C s (.inr i) ≠ 0 then
    if hi : iStar C x rq s < C.length then
      match C[iStar C x rq s]? with
      | some (.mux s' _ _) => shiftH C m σ ⟨_, hi⟩ (rlab C m x σ (iStar C x rq s) s') v
      | _ => σ
    else σ
  else if hJ : ∃ j, j < m ∧ pl x rq C s (.inl j) ≠ 0 then
    shiftR C m σ ⟨Nat.find hJ, (Nat.find_spec hJ).1⟩ v
  else σ

omit [Module (ZMod 2) V] in
/-- The two cases of `shiftOf`. -/
theorem shiftOf_cases (x : ℕ → Bool) (rq : ℕ → Bool) (s : ℕ) (hs : pl x rq C s ≠ 0)
    (hrq : ∀ j, m ≤ j → rq j = true) :
    (∃ i, ∃ hi : i < C.length, ∃ s' z' o', C[i]? = some (.mux s' z' o') ∧
      pl x rq C s (.inr i) ≠ 0 ∧ (∀ i', i < i' → pl x rq C s (.inr i') = 0) ∧
      ∀ (σ : Rand V m C.length) v,
        shiftOf C m x rq s σ v = shiftH C m σ ⟨i, hi⟩ (rlab C m x σ i s') v) ∨
    (∃ j, ∃ hj : j < m, pl x rq C s (.inl j) ≠ 0 ∧ rq j = false ∧
      (∀ i', pl x rq C s (.inr i') = 0) ∧
      ∀ (σ : Rand V m C.length) v, shiftOf C m x rq s σ v = shiftR C m σ ⟨j, hj⟩ v) := by
  classical
  by_cases hI : ∃ i, i ≤ s ∧ pl x rq C s (.inr i) ≠ 0
  · left
    have hex := hI
    obtain ⟨i0, hi0, hp0⟩ := hI
    have hP : pl x rq C s (.inr (iStar C x rq s)) ≠ 0 :=
      Nat.findGreatest_spec (P := fun i ↦ pl x rq C s (.inr i) ≠ 0) hi0 hp0
    rcases pl_support x rq C s _ hP with ⟨j, hj, -⟩ | ⟨i', hi', -, s', z', o', hC, -⟩
    · cases hj
    · cases hi'
      have hi : iStar C x rq s < C.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hC; cases hC
      refine ⟨iStar C x rq s, hi, s', z', o', hC, hP, fun i' hlt ↦ ?_, fun σ v ↦ ?_⟩
      · by_contra hne
        have hle : i' ≤ s := by
          rcases pl_support x rq C s _ hne with ⟨j, hj, -⟩ | ⟨i'', hi'', hle, -⟩
          · cases hj
          · cases hi''; exact hle
        exact Nat.findGreatest_is_greatest hlt hle hne
      · unfold shiftOf
        simp only [hex, ↓reduceIte, hi, ↓reduceDIte, hC]
  · right
    have hno : ∀ i', pl x rq C s (.inr i') = 0 := by
      intro i'; by_contra hne
      rcases pl_support x rq C s _ hne with ⟨j, hj, -⟩ | ⟨i'', hi'', hle, -⟩
      · cases hj
      · cases hi''; exact hI ⟨i', hle, hne⟩
    have hJ : ∃ j, j < m ∧ pl x rq C s (.inl j) ≠ 0 := by
      obtain ⟨β, hβ⟩ := Finsupp.ne_iff.1 hs
      rcases pl_support x rq C s β hβ with ⟨j, rfl, hr⟩ | ⟨i', rfl, -⟩
      · refine ⟨j, ?_, hβ⟩
        by_contra h; rw [hrq j (by omega)] at hr; cases hr
      · exact absurd (hno i') hβ
    have hspec := Nat.find_spec hJ
    refine ⟨Nat.find hJ, hspec.1, hspec.2, ?_, hno, fun σ v ↦ ?_⟩
    · rcases pl_support x rq C s _ hspec.2 with ⟨j, hj, hr⟩ | ⟨i', hi', -⟩
      · cases hj; exact hr
      · cases hi'
    · unfold shiftOf
      simp only [hI, ↓reduceIte, hJ, ↓reduceDIte]

/-- What `shiftOf` changes and what it keeps. -/
theorem shiftOf_props (x : ℕ → Bool) (rq : ℕ → Bool) (s : ℕ) (hs : pl x rq C s ≠ 0)
    (hrq : ∀ j, m ≤ j → rq j = true) (σ : Rand V m C.length) (v : V) :
    plab C m x (shiftOf C m x rq s σ v) s = plab C m x σ s + v ∧
    (shiftOf C m x rq s σ v).1.2 = σ.1.2 ∧ (shiftOf C m x rq s σ v).2.2 = σ.2.2 ∧
    (∀ j, rq j = true → extL (shiftOf C m x rq s σ v).1.1 j = extL σ.1.1 j) ∧
    (∀ i y, extH (shiftOf C m x rq s σ v).2.1 i y ≠ extH σ.2.1 i y →
      ∃ s' z' o', C[i]? = some (.mux s' z' o') ∧ rl x rq C i s' ≠ 0 ∧ y = rlab C m x σ i s') ∧
    shiftOf C m x rq s (shiftOf C m x rq s σ v) (-v) = σ := by
  rcases shiftOf_cases (V := V) C m x rq s hs hrq with
    ⟨i, hi, s', z', o', hC, hP, hmax, hsh⟩ | ⟨j, hj, hP, hr, hno, hsh⟩
  · have hunk : rl x rq C i s' ≠ 0 := by
      rcases pl_support x rq C s _ hP with ⟨j, hj, -⟩ | ⟨i', hi', -, s'', z'', o'', hC', hs''⟩
      · cases hj
      · cases hi'; rw [hC] at hC'; cases hC'; exact hs''
    rw [hsh]
    refine ⟨plab_shiftH C m x rq σ s ⟨i, hi⟩ v hC hP hmax, rfl, rfl, fun _ _ ↦ rfl,
      fun i' y hne ↦ ?_, ?_⟩
    · by_cases hii : i' = i
      · subst hii
        refine ⟨s', z', o', hC, hunk, ?_⟩
        by_contra hy
        apply hne
        simp [extH, shiftH, hi, hy]
      · exact absurd (extH_shiftH_ne C m σ ⟨i, hi⟩ _ v hii y) hne
    · rw [hsh, rlab_shiftH_le C m x σ ⟨i, hi⟩ _ v le_rfl]
      ext i'' y
      · rfl
      · rfl
      · simp only [shiftH]
        split_ifs <;> simp
      · rfl
  · rw [hsh]
    refine ⟨plab_shiftR C m x rq σ s ⟨j, hj⟩ v hP hno, rfl, rfl, fun j' hj' ↦ ?_,
      fun i y hne ↦ absurd rfl hne, ?_⟩
    · have : j' ≠ j := fun he ↦ by rw [he, hr] at hj'; cases hj'
      simp only [extL, shiftR]
      split_ifs with h
      · rw [Function.update_of_ne (fun he ↦ this (congrArg Fin.val he))]
      · rfl
    · rw [hsh]
      simp only [shiftR, Function.update_self, Function.update_idem, add_neg_cancel_right,
        Function.update_eq_self]

end Shift

/-! ### The injection -/

section Inj

variable (C : Circuit) (m : ℕ) (A : AAdv V) (k : ℕ)

omit [AddCommGroup V] [Module (ZMod 2) V] in
/-- An input requested at an earlier step is requested at step `k`. -/
theorem reqAt_of_act (O : List (Act V) → Act V → V) (M : List (Material V))
    {t : ℕ} (ht : t < k) {j : ℕ} {b : Bool} (ha : A.act M (run O A M t).2 = .req j b) :
    reqAt m (run O A M k).1 j = true := by
  obtain ⟨rest, hr⟩ := run_prefix O A M (t + 1) (k - (t + 1))
  rw [show t + 1 + (k - (t + 1)) = k by omega] at hr
  rw [hr, run, ha]
  simp only [reqAt, Bool.or_eq_true, decide_eq_true_eq, bitOf_append]
  right
  cases bitOf (run O A M t).1 j <;> simp [bitOf]

/-- The input requested before step `k` of the simulated game. -/
def xS (σ : Rand V m C.length) : ℕ → Bool := xOf m (simRun C m A σ k).1

/-- The inputs requested before step `k` of the simulated game. -/
def rS (σ : Rand V m C.length) : ℕ → Bool := reqAt m (simRun C m A σ k).1

/-- The action at step `k` of the simulated game. -/
def actK (σ : Rand V m C.length) : Act V := A.act (simM C m σ) (simRun C m A σ k).2

/-- The query at step `k` hits the active label of a selector unknown at step `k`, and no
earlier query hits the active point of such a selector. -/
def FreshHit (σ : Rand V m C.length) : Prop :=
  ∃ i y s z o, actK C m A k σ = .query i y ∧ C[i]? = some (.mux s z o) ∧
    rl (xS C m A k σ) (rS C m A k σ) C i s ≠ 0 ∧ y = simX C m A σ k i s ∧ Fresh C m A σ k

/-- The shift at step `k`. -/
noncomputable def shiftAt (σ : Rand V m C.length) (v : V) : Rand V m C.length :=
  match actK C m A k σ with
  | .query i _ =>
    match C[i]? with
    | some (.mux s _ _) => shiftOf C m (xS C m A k σ) (rS C m A k σ) s σ v
    | _ => σ
  | .req _ _ => σ

theorem simX_eq (σ : Rand V m C.length) (i s : ℕ) :
    simX C m A σ k i s = rlab C m (xS C m A k σ) σ i s := by
  unfold simX rlab
  split_ifs with h
  · exact congrArg Prod.snd (simEval_getD C m (xS C m A k σ) σ s)
  · rfl

omit [Module (ZMod 2) V] in
theorem hrq_rS (σ : Rand V m C.length) : ∀ j, m ≤ j → rS C m A k σ j = true := by
  intro j hj; simp [rS, reqAt, hj]

/-- The data of a hit, and the shift as `shiftOf`. -/
theorem freshHit_shift {σ : Rand V m C.length} (h : FreshHit C m A k σ) :
    ∃ i y s z o, actK C m A k σ = .query i y ∧ C[i]? = some (.mux s z o) ∧
      pl (xS C m A k σ) (rS C m A k σ) C s ≠ 0 ∧ s < i ∧
      y = plab C m (xS C m A k σ) σ s ∧ Fresh C m A σ k ∧
      ∀ v, shiftAt C m A k σ v = shiftOf C m (xS C m A k σ) (rS C m A k σ) s σ v := by
  obtain ⟨i, y, s, z, o, ha, hC, hunk, hy, hf⟩ := h
  have hsi : s < i := by by_contra h'; simp [rl, h'] at hunk
  simp only [rl, hsi, ↓reduceIte] at hunk
  refine ⟨i, y, s, z, o, ha, hC, hunk, hsi, ?_, hf, fun v ↦ ?_⟩
  · rw [hy, simX_eq, rlab]; simp [hsi]
  · unfold shiftAt; rw [ha]; simp only [hC]

/-- **The shift does not change the run up to step `k`.** -/
theorem simRun_shiftAt {σ : Rand V m C.length} (h : FreshHit C m A k σ) (v : V) {j : ℕ}
    (hj : j ≤ k) : simRun C m A (shiftAt C m A k σ v) j = simRun C m A σ j := by
  obtain ⟨i, y, s, z, o, ha, hC, hs, hsi, hy, hf, hsh⟩ := freshHit_shift C m A k h
  obtain ⟨-, h1, h2, h3, h4, -⟩ := shiftOf_props C m (xS C m A k σ) (rS C m A k σ) s hs
    (hrq_rS C m A k σ) σ v
  rw [hsh]
  have hM : simM C m (shiftOf C m (xS C m A k σ) (rS C m A k σ) s σ v) = simM C m σ := by
    simp only [simM, h1, h2]
  unfold simRun
  rw [hM]
  apply run_congr
  intro t ht
  cases hat : A.act (simM C m σ) (run (simO C m σ.1.1 σ.2.1) A (simM C m σ) t).2 with
  | query i' y' =>
    simp only [simO]
    by_contra hne
    obtain ⟨s', z', o', hC', hunk', hy'⟩ := h4 i' y' hne
    exact hf t (by omega) i' y' s' z' o' hat hC' hunk' (by rw [hy', simX_eq])
  | req j' b =>
    simp only [simO]
    exact h3 j' (reqAt_of_act m A k _ _ (by omega) hat)

/-- What the shift at step `k` keeps, changes, and how to undo it. -/
theorem shiftAt_props {σ : Rand V m C.length} (h : FreshHit C m A k σ) (v : V) :
    actK C m A k (shiftAt C m A k σ v) = actK C m A k σ ∧
    xS C m A k (shiftAt C m A k σ v) = xS C m A k σ ∧
    (∀ i y s z o, actK C m A k σ = .query i y → C[i]? = some (.mux s z o) →
      plab C m (xS C m A k σ) (shiftAt C m A k σ v) s = y + v) ∧
    shiftAt C m A k (shiftAt C m A k σ v) (-v) = σ := by
  obtain ⟨i, y, s, z, o, ha, hC, hs, hsi, hy, hf, hsh⟩ := freshHit_shift C m A k h
  obtain ⟨hl, h1, h2, -, -, hundo⟩ := shiftOf_props C m (xS C m A k σ) (rS C m A k σ) s hs
    (hrq_rS C m A k σ) σ v
  have hr := simRun_shiftAt C m A k h v le_rfl
  have hM : simM C m (shiftAt C m A k σ v) = simM C m σ := by
    rw [hsh]; simp only [simM, h1, h2]
  have hact : actK C m A k (shiftAt C m A k σ v) = actK C m A k σ := by
    unfold actK; rw [hM, hr]
  have hx : xS C m A k (shiftAt C m A k σ v) = xS C m A k σ := by unfold xS; rw [hr]
  have hrS : rS C m A k (shiftAt C m A k σ v) = rS C m A k σ := by unfold rS; rw [hr]
  refine ⟨hact, hx, fun i' y' s' z' o' ha' hC' ↦ ?_, ?_⟩
  · rw [ha] at ha'; cases ha'; rw [hC] at hC'; cases hC'
    rw [hsh, hl, ← hy]
  · generalize hσ' : shiftAt C m A k σ v = σ' at hact hx hrS ⊢
    unfold shiftAt
    rw [hact, ha]
    simp only [hC, hx, hrS]
    rw [← hσ', hsh v]
    exact hundo

/-- **The shift is injective.** -/
theorem shiftAt_injOn :
    Set.InjOn (fun p : Rand V m C.length × V ↦ shiftAt C m A k p.1 p.2)
      {p | FreshHit C m A k p.1} := by
  rintro ⟨σ1, v1⟩ h1 ⟨σ2, v2⟩ h2 he
  simp only [Set.mem_ofPred_eq] at h1 h2
  simp only at he
  obtain ⟨a1, x1, l1, u1⟩ := shiftAt_props C m A k h1 v1
  obtain ⟨a2, x2, l2, u2⟩ := shiftAt_props C m A k h2 v2
  obtain ⟨i, y, s, z, o, ha, hC, -⟩ := h1
  have ha2 : actK C m A k σ2 = .query i y := by rw [← a2, ← he, a1, ha]
  have e1 := l1 i y s z o ha hC
  have e2 := l2 i y s z o ha2 hC
  have hxx : xS C m A k σ1 = xS C m A k σ2 := by rw [← x1, he, x2]
  rw [he, hxx, e2] at e1
  have hv : v1 = v2 := (add_left_cancel e1).symm
  subst hv
  rw [← u1, he, u2]

open Classical in
/-- **Fresh labels.** The randomness for which the query at step `k` hits the active label of a
selector unknown at step `k`, with no earlier query at the active point of such a selector, is
at most a fraction `1 / |V|` of all of it. -/
theorem card_freshHit_le [Fintype V] [DecidableEq V] :
    (Finset.univ.filter fun σ : Rand V m C.length ↦ FreshHit C m A k σ).card *
      Fintype.card V ≤ Fintype.card (Rand V m C.length) := by
  rw [← Finset.card_univ (α := V), ← Finset.card_product, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun p ↦ shiftAt C m A k p.1 p.2)
    (fun _ _ ↦ Finset.mem_univ _) ((shiftAt_injOn C m A k).mono fun p hp ↦ ?_)
  simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and,
    Finset.coe_univ, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true] at hp
  exact hp

end Inj

end GcZk.Adaptive
