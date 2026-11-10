/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.AdaptiveBad

/-!
# Adaptive authenticity: shifting an atom

In the simulated game, the active labels for an input `x` are computed position by position
(`plab`). Their change under a change of the randomness is a linear combination of the changes of
the atoms, with the linear part as coefficients (`plab_shift`). Shifting the randomness at a
suitable atom therefore changes the label of a given unknown wire by exactly the shift.
-/

namespace GcZk.Adaptive

open Auth RO Lin

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

section Labels

variable (C : Circuit) (m : ℕ)

/-- The simulated active label of a node, from the values `r` and labels `l` of the other
positions. -/
def labStep (σ : Rand V m C.length) (r : ℕ → Bool) (l : ℕ → V) (p : ℕ) : Option Node → V
  | some (.input j) => extL σ.1.1 j
  | some (.const _) => extL σ.1.2 p
  | some (.xor a b) => l a + l b
  | some (.mux s z o) =>
    extH σ.2.1 p (l s) + l (cand (r s) z o) + if r s then extL σ.2.2 p else 0
  | none => 0

/-- The simulated active label of position `p` for the input `x`. -/
def plab (x : ℕ → Bool) (σ : Rand V m C.length) (p : ℕ) : V :=
  labStep C m σ (rv x C p) (fun a ↦ if a < p then plab x σ a else 0) p C[p]?
termination_by p
decreasing_by assumption

/-- The label of position `a` as read from position `p`. -/
def rlab (x : ℕ → Bool) (σ : Rand V m C.length) (p a : ℕ) : V :=
  if a < p then plab C m x σ a else 0

omit [Module (ZMod 2) V] in
theorem plab_eq (x : ℕ → Bool) (σ : Rand V m C.length) (p : ℕ) :
    plab C m x σ p = labStep C m σ (rv x C p) (rlab C m x σ p) p C[p]? := by
  rw [plab]; rfl

/-- The input wires of the simulated game for the input `x`. -/
def simInp (x : ℕ → Bool) (σ : Rand V m C.length) : ℕ → Wire V := fun j ↦ (x j, extL σ.1.1 j)

theorem evalAux_getD (x : ℕ → Bool) (σ : Rand V m C.length) :
    ∀ (ns : Circuit) (ws : List (Wire V)) (pre : Circuit), pre.length = ws.length →
      C = pre ++ ns →
      (∀ i, ws.getD i (false, 0) = (rv x C ws.length i, rlab C m x σ ws.length i)) →
        ∀ i, (evalAux (extH σ.2.1) (simInp C m x σ) ns ((simM C m σ).drop ws.length) ws).getD i
          (false, 0) = (rv x C (ws.length + ns.length) i, rlab C m x σ (ws.length + ns.length) i)
  | [], ws, _, _, _, hv, i => by
    have : evalAux (extH σ.2.1) (simInp C m x σ) [] ((simM C m σ).drop ws.length) ws = ws := by
      cases (simM C m σ).drop ws.length <;> rfl
    simpa [this] using hv i
  | n :: ns, ws, pre, hpre, hC, hv, i => by
    have hk : ws.length < C.length := by rw [hC]; simp [hpre]
    have hn : C[ws.length] = n := by
      simp only [hC, ← hpre, List.getElem_append_right le_rfl, Nat.sub_self,
        List.getElem_cons_zero]
    have hd : (simM C m σ).drop ws.length =
        simNode (extL σ.1.2) (extL σ.2.2) ws.length n :: (simM C m σ).drop (ws.length + 1) := by
      rw [List.drop_eq_getElem_cons (by simp [simM, hk])]
      simp [simM, hn]
    have hnode : evalNode (extH σ.2.1) (simInp C m x σ) ws n
        (simNode (extL σ.1.2) (extL σ.2.2) ws.length n) =
        (pv x C ws.length, plab C m x σ ws.length) := by
      have hC' : C[ws.length]? = some n := by rw [List.getElem?_eq_getElem hk, hn]
      rw [pv_eq, plab_eq, hC']
      have hv1 : ∀ a, (ws.getD a (false, 0)).1 = rv x C ws.length a := fun a ↦ by rw [hv a]
      have hv2 : ∀ a, (ws.getD a (false, 0)).2 = rlab C m x σ ws.length a := fun a ↦ by rw [hv a]
      cases n with
      | input j => rfl
      | const b => rfl
      | xor a b => simp only [evalNode, hv1, hv2, valStep, labStep]
      | mux s z o =>
        simp only [evalNode, simNode, valStep, labStep, cand, hv1, hv2]
        cases rv x C ws.length s <;> simp
    have hv' : ∀ i, (ws ++ [(pv x C ws.length, plab C m x σ ws.length)]).getD i (false, 0) =
        (rv x C (ws.length + 1) i, rlab C m x σ (ws.length + 1) i) := by
      intro i
      rw [getD_snoc]
      rcases lt_trichotomy i ws.length with h | rfl | h
      · simp only [h, ↓reduceIte, hv i, rv, rlab, show i < ws.length + 1 by omega]
      · simp [rv, rlab]
      · simp [show ¬ i < ws.length by omega, h.ne', rv, rlab, show ¬ i < ws.length + 1 by omega]
    have := evalAux_getD x σ ns (ws ++ [(pv x C ws.length, plab C m x σ ws.length)])
      (pre ++ [n]) (by simp [hpre]) (by simp [hC]) (by simpa using hv') i
    simp only [List.length_append, List.length_singleton] at this
    rw [hd]
    simp only [evalAux, hnode]
    rw [this]
    simp only [List.length_cons]
    congr 2 <;> omega

/-- **The simulated wires, position by position.** -/
theorem simEval_getD (x : ℕ → Bool) (σ : Rand V m C.length) (p : ℕ) :
    (eval (extH σ.2.1) (simInp C m x σ) C (simM C m σ)).getD p (false, 0) =
      (pv x C p, plab C m x σ p) := by
  have := evalAux_getD C m x σ C [] [] rfl rfl (by simp [rv, rlab]) p
  rw [eval]
  simp only [List.length_nil, List.drop_zero, zero_add] at this
  rw [this]
  simp only [rv, rlab]
  split_ifs with h
  · rfl
  · rw [pv_eq, plab_eq, List.getElem?_eq_none (by omega)]; rfl

/-! ### The change of the labels -/

/-- The changes of the atoms from `σ` to `σ'`: of an input label, or of the hash value read at a
multiplexer. -/
def δα (x : ℕ → Bool) (σ σ' : Rand V m C.length) : Atom → V
  | .inl j => extL σ'.1.1 j - extL σ.1.1 j
  | .inr i =>
    match C[i]? with
    | some (.mux s _ _) => extH σ'.2.1 i (rlab C m x σ' i s) - extH σ.2.1 i (rlab C m x σ i s)
    | _ => 0

/-- **The change of a label is linear in its linear part.** If `σ'` has the same active constant
labels and ciphertexts as `σ`, the same labels at the requested inputs, and the same hash at the
multiplexers with a known selector, then the change of the label of every position is the
combination of the changes of the atoms with its linear part as coefficients. -/
theorem plab_shift (x : ℕ → Bool) (req : ℕ → Bool) (σ σ' : Rand V m C.length)
    (hA : σ'.1.2 = σ.1.2) (hT : σ'.2.2 = σ.2.2)
    (hR : ∀ j, req j = true → extL σ'.1.1 j = extL σ.1.1 j)
    (hH : ∀ i s z o, C[i]? = some (.mux s z o) → rl x req C i s = 0 →
      ∀ y, extH σ'.2.1 i y = extH σ.2.1 i y) (p : ℕ) :
    plab C m x σ' p - plab C m x σ p =
      Finsupp.linearCombination (ZMod 2) (δα C m x σ σ') (pl x req C p) := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  have hr : ∀ a, rlab C m x σ' p a - rlab C m x σ p a =
      Finsupp.linearCombination (ZMod 2) (δα C m x σ σ') (rl x req C p a) := by
    intro a
    by_cases ha : a < p
    · simp only [rlab, rl, ha, ↓reduceIte]; exact ih a ha
    · simp [rlab, rl, ha]
  rw [plab_eq, plab_eq, pl_eq]
  cases hC : C[p]? with
  | none => simp [labStep, linStep]
  | some n =>
    cases n with
    | input j =>
      by_cases hj : req j = true
      · simp [labStep, linStep, hj, hR j hj]
      · simp [labStep, linStep, hj, δα]
    | const b => simp [labStep, linStep, hA]
    | xor a b =>
      simp only [labStep, linStep, map_add, ← hr]
      abel
    | mux s z o =>
      simp only [labStep, linStep, hT]
      by_cases hs : rl x req C p s = 0
      · have e : rlab C m x σ' p s = rlab C m x σ p s := by
          have := hr s; rw [hs, map_zero] at this; exact sub_eq_zero.1 this
        simp only [hs, ↓reduceIte, ← hr, e, hH p s z o hC hs]
        abel
      · simp only [hs, ↓reduceIte, map_add, ← hr, Finsupp.linearCombination_single, one_smul,
          δα, hC]
        abel

/-! ### The two shifts -/

open Classical in
/-- Add `v` to the hash at the point `(i, P)`. -/
noncomputable def shiftH (σ : Rand V m C.length) (i : Fin C.length) (P v : V) : Rand V m C.length :=
  (σ.1, (fun i' y ↦ if i' = i ∧ y = P then σ.2.1 i' y + v else σ.2.1 i' y, σ.2.2))

/-- Add `v` to the label of the input `j`. -/
def shiftR (σ : Rand V m C.length) (j : Fin m) (v : V) : Rand V m C.length :=
  ((Function.update σ.1.1 j (σ.1.1 j + v), σ.1.2), σ.2)

omit [Module (ZMod 2) V] in
theorem extH_shiftH_ne (σ : Rand V m C.length) (i : Fin C.length) (P v : V) {i' : ℕ}
    (h : i' ≠ i) (y : V) : extH (shiftH C m σ i P v).2.1 i' y = extH σ.2.1 i' y := by
  simp only [extH, shiftH]
  split_ifs with h1 h2
  · exact absurd (congrArg Fin.val h2.1) h
  all_goals rfl

/-- Shifting the hash at gate `i` does not change the labels before `i`. -/
theorem plab_shiftH_lt (x : ℕ → Bool) (σ : Rand V m C.length) (i : Fin C.length) (P v : V)
    (p : ℕ) (hp : p < i) : plab C m x (shiftH C m σ i P v) p = plab C m x σ p := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  have hl : rlab C m x (shiftH C m σ i P v) p = rlab C m x σ p := by
    funext a
    by_cases ha : a < p
    · simp only [rlab, ha, ↓reduceIte]; exact ih a ha (by omega)
    · simp [rlab, ha]
  rw [plab_eq, plab_eq, hl]
  cases C[p]? with
  | none => rfl
  | some n =>
    cases n with
    | mux s z o =>
      simp only [labStep, extH_shiftH_ne C m σ i P v (show p ≠ i by omega)]
      rfl
    | _ => rfl

theorem rlab_shiftH_le (x : ℕ → Bool) (σ : Rand V m C.length) (i : Fin C.length) (P v : V)
    {p : ℕ} (hp : p ≤ i) (a : ℕ) :
    rlab C m x (shiftH C m σ i P v) p a = rlab C m x σ p a := by
  by_cases ha : a < p
  · simp only [rlab, ha, ↓reduceIte]; exact plab_shiftH_lt C m x σ i P v a (by omega)
  · simp [rlab, ha]

theorem zmod2_eq_one {t : ZMod 2} (h : t ≠ 0) : t = 1 := by
  revert t; decide

/-- **Shifting at the last multiplexer atom.** Let `i*` be the largest multiplexer whose atom
occurs in the linear part of `w`. Adding `v` to the hash at the point read by `i*` changes the
label of `w` by exactly `v`. -/
theorem plab_shiftH (x : ℕ → Bool) (req : ℕ → Bool) (σ : Rand V m C.length) (w : ℕ)
    (i : Fin C.length) (v : V) {s z o : ℕ} (hC : C[(i : ℕ)]? = some (.mux s z o))
    (hi : pl x req C w (.inr i) ≠ 0) (hmax : ∀ i' : ℕ, (i : ℕ) < i' → pl x req C w (.inr i') = 0) :
    plab C m x (shiftH C m σ i (rlab C m x σ i s) v) w = plab C m x σ w + v := by
  -- the selector of `i` is unknown
  have hunk : rl x req C i s ≠ 0 := by
    rcases pl_support x req C w _ hi with ⟨j, hj, -⟩ | ⟨i', hi', -, s', z', o', hC', hs'⟩
    · cases hj
    · cases hi'; rw [hC] at hC'; cases hC'; exact hs'
  have hsh := plab_shift C m x req σ (shiftH C m σ i (rlab C m x σ i s) v) rfl rfl (fun _ _ ↦ rfl)
    (fun i' s' z' o' hC' hk y ↦ by
    refine extH_shiftH_ne C m σ i _ v (fun he ↦ ?_) y
    subst he; rw [hC] at hC'; cases hC'; exact hunk hk) w
  rw [eq_add_of_sub_eq' hsh]
  congr 1
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_eq_single (Sum.inr (i : ℕ))]
  · rw [zmod2_eq_one hi, one_smul]
    simp only [δα, hC, rlab_shiftH_le C m x σ i _ v le_rfl]
    simp [shiftH, extH, i.2]
  · intro β hβ hne
    have hβ' : pl x req C w β ≠ 0 := Finsupp.mem_support_iff.1 hβ
    rcases pl_support x req C w β hβ' with ⟨j, rfl, -⟩ | ⟨i', rfl, -, s', z', o', hC', -⟩
    · simp [δα, shiftH]
    · have hlt : i' < i := by
        rcases lt_trichotomy i' i with h | h | h
        · exact h
        · exact absurd (by rw [h]) hne
        · exact absurd (hmax i' h) hβ'
      simp only [δα, hC', rlab_shiftH_le C m x σ i _ v hlt.le,
        extH_shiftH_ne C m σ i _ v hlt.ne, sub_self, smul_zero]
  · intro h; exact absurd (Finsupp.notMem_support_iff.1 h) hi

/-- **Shifting at an input atom.** If the linear part of `w` has no multiplexer atom and has the
input `j`, adding `v` to the label of `j` changes the label of `w` by exactly `v`. -/
theorem plab_shiftR (x : ℕ → Bool) (req : ℕ → Bool) (σ : Rand V m C.length) (w : ℕ)
    (j : Fin m) (v : V) (hj : pl x req C w (.inl j) ≠ 0)
    (hno : ∀ i' : ℕ, pl x req C w (.inr i') = 0) :
    plab C m x (shiftR C m σ j v) w = plab C m x σ w + v := by
  have hreq : req j = false := by
    rcases pl_support x req C w _ hj with ⟨j', hj', hr⟩ | ⟨i', hi', -⟩
    · cases hj'; exact hr
    · cases hi'
  have hsh := plab_shift C m x req σ (shiftR C m σ j v) rfl rfl (fun j' hj' ↦ by
    have : j' ≠ j := fun he ↦ by rw [he] at hj'; simp [hreq] at hj'
    simp only [extL, shiftR]
    split_ifs with h
    · rw [Function.update_of_ne (fun he ↦ this (by rw [← he]))]
    · rfl) (fun _ _ _ _ _ _ _ ↦ rfl) w
  rw [eq_add_of_sub_eq' hsh]
  congr 1
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_eq_single (Sum.inl (j : ℕ))]
  · rw [zmod2_eq_one hj, one_smul]
    simp [δα, extL, shiftR]
  · intro β hβ hne
    have hβ' : pl x req C w β ≠ 0 := Finsupp.mem_support_iff.1 hβ
    rcases β with j' | i'
    · have : j' ≠ j := fun he ↦ hne (by rw [he])
      simp only [δα, extL, shiftR]
      split_ifs with h
      · rw [Function.update_of_ne (fun he ↦ this (by rw [← he])), sub_self, smul_zero]
      · simp
    · exact absurd (hno i') hβ'
  · intro h; exact absurd (Finsupp.notMem_support_iff.1 h) hj

end Labels

end GcZk.Adaptive
