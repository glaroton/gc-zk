/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.Garbling

/-!
# The linear part of a label

For adaptive authenticity we need to know, at each step of the game, which labels the adversary
can know. A selector whose *value* is fixed by the bits requested so far does not qualify; the
right notion is a combinatorial *linear part* of each label, a vector over `ZMod 2` indexed by
*atoms*: `inl j` for an input `j` not yet requested, and `inr i` for the hash value read at a
multiplexer `i` with an unknown selector. A wire is *known* when its linear part is `0`.

Values and linear parts are defined position by position (`pv`, `pl`), by well-founded recursion:
a node reads the earlier positions, and an operand that is not earlier reads the default.

## Main results

* `GcZk.Lin.pv_add`: if `x'` agrees with `x` on the requested inputs, the change of the value of
  each wire is a linear function of its linear part.
* `GcZk.Lin.pv_eq_of_known`: a known wire has the same value on `x` and on `x'`.
* `GcZk.Lin.pl_mono`: when more inputs are requested (and `x'` agrees with `x` on the inputs
  requested before), the new linear parts are a linear image of the old ones.
* `GcZk.Lin.known_mono`: a wire known before stays known.
-/

namespace GcZk.Lin

/-- The atoms: an input (`inl j`) or the multiplexer at a position (`inr i`). -/
abbrev Atom := ℕ ⊕ ℕ

/-- Linear parts. -/
abbrev L := Atom →₀ ZMod 2

/-- A bit in `ZMod 2`. -/
def bz (t : Bool) : ZMod 2 := if t then 1 else 0

@[simp] theorem bz_xor (u w : Bool) : bz (u ^^ w) = bz u + bz w := by
  cases u <;> cases w <;> decide

@[simp] theorem bz_add_self (u : Bool) : bz u + bz u = 0 := by
  cases u <;> decide

theorem bz_add_eq_zero {u w : Bool} : bz u + bz w = 0 ↔ u = w := by
  cases u <;> cases w <;> decide

/-! ### Values -/

/-- The value of a node, from the values `r` of the other positions. -/
def valStep (x : ℕ → Bool) (r : ℕ → Bool) : Option Node → Bool
  | some (.input j) => x j
  | some (.const b) => b
  | some (.xor a b) => r a ^^ r b
  | some (.mux s z o) => if r s then r o else r z
  | none => false

/-- The value of the node at position `p` on the input `x`. -/
def pv (x : ℕ → Bool) (C : Circuit) (p : ℕ) : Bool :=
  valStep x (fun a ↦ if a < p then pv x C a else false) C[p]?
termination_by p
decreasing_by assumption

/-- The value of position `a` as read from position `p`. -/
def rv (x : ℕ → Bool) (C : Circuit) (p a : ℕ) : Bool := if a < p then pv x C a else false

theorem pv_eq (x : ℕ → Bool) (C : Circuit) (p : ℕ) : pv x C p = valStep x (rv x C p) C[p]? := by
  rw [pv]; rfl

/-! ### Linear parts -/

/-- The candidate selected at a multiplexer `mux s z o`, from the value `t` of its selector. -/
def cand (t : Bool) (z o : ℕ) : ℕ := if t then o else z

/-- The linear part of a node, from the values `r` and the linear parts `l` of the other
positions. `req j` says that the input `j` is requested. -/
noncomputable def linStep (req : ℕ → Bool) (r : ℕ → Bool) (l : ℕ → L) (p : ℕ) : Option Node → L
  | some (.input j) => if req j then 0 else Finsupp.single (Sum.inl j) 1
  | some (.const _) => 0
  | some (.xor a b) => l a + l b
  | some (.mux s z o) =>
    if l s = 0 then l (cand (r s) z o) else Finsupp.single (Sum.inr p) 1 + l (cand (r s) z o)
  | none => 0

/-- The linear part of the node at position `p`. -/
noncomputable def pl (x : ℕ → Bool) (req : ℕ → Bool) (C : Circuit) (p : ℕ) : L :=
  linStep req (rv x C p) (fun a ↦ if a < p then pl x req C a else 0) p C[p]?
termination_by p
decreasing_by assumption

/-- The linear part of position `a` as read from position `p`. -/
noncomputable def rl (x : ℕ → Bool) (req : ℕ → Bool) (C : Circuit) (p a : ℕ) : L :=
  if a < p then pl x req C a else 0

theorem pl_eq (x : ℕ → Bool) (req : ℕ → Bool) (C : Circuit) (p : ℕ) :
    pl x req C p = linStep req (rv x C p) (rl x req C p) p C[p]? := by
  rw [pl]; rfl

/-! ### Known wires are determined -/

/-- The coefficients of the change of value from `x` to `x'`. -/
noncomputable def φ (x x' : ℕ → Bool) (C : Circuit) : Atom → ZMod 2
  | .inl j => bz (x' j) + bz (x j)
  | .inr i =>
    match C[i]? with
    | some (.mux s z o) =>
      bz (pv x' C i) + bz (pv x C i) + bz (rv x' C i (cand (rv x C i s) z o)) +
        bz (rv x C i (cand (rv x C i s) z o))
    | _ => 0

/-- **The change of value is linear in the linear part.** If `x'` agrees with `x` on the
requested inputs, then for every position `p`, `v_p(x') + v_p(x)` is the linear combination of
the coefficients `φ` with the linear part of `p`. -/
theorem pv_add (x x' : ℕ → Bool) (req : ℕ → Bool) (C : Circuit)
    (hx : ∀ j, req j = true → x' j = x j) (p : ℕ) :
    bz (pv x' C p) + bz (pv x C p) =
      Finsupp.linearCombination (ZMod 2) (φ x x' C) (pl x req C p) := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  -- reading an earlier position
  have hr : ∀ a, bz (rv x' C p a) + bz (rv x C p a) =
      Finsupp.linearCombination (ZMod 2) (φ x x' C) (rl x req C p a) := by
    intro a
    by_cases ha : a < p
    · simp only [rv, rl, ha, ↓reduceIte]; exact ih a ha
    · simp [rv, rl, ha]
  rw [pv_eq, pv_eq, pl_eq]
  cases hC : C[p]? with
  | none => simp [valStep, linStep]
  | some n =>
    cases n with
    | input j =>
      by_cases hj : req j = true
      · simp [valStep, linStep, hj, hx j hj]
      · simp [valStep, linStep, hj, φ]
    | const b => simp [valStep, linStep]
    | xor a b =>
      simp only [valStep, linStep, bz_xor, map_add, ← hr a, ← hr b]
      abel
    | mux s z o =>
      have hA : ∀ y, valStep y (rv y C p) (some (.mux s z o)) = pv y C p := by
        intro y; rw [pv_eq, hC]
      simp only [linStep]
      by_cases hs : rl x req C p s = 0
      · have e : rv x' C p s = rv x C p s := by
          have := hr s
          rw [hs, map_zero] at this
          exact bz_add_eq_zero.1 this
        simp only [hs, ↓reduceIte, ← hr, valStep, e]
        cases rv x C p s <;> rfl
      · simp only [hs, ↓reduceIte, map_add, ← hr, Finsupp.linearCombination_single, smul_eq_mul,
          one_mul, φ, hC, hA]
        have key : ∀ A B c1 c2 : ZMod 2, A + B = (A + B + c1 + c2) + (c1 + c2) := by decide
        exact key _ _ _ _

/-- **Known wires are determined.** If `x'` agrees with `x` on the requested inputs, a position
with linear part `0` has the same value on `x` and on `x'`. -/
theorem pv_eq_of_known (x x' : ℕ → Bool) (req : ℕ → Bool) (C : Circuit)
    (hx : ∀ j, req j = true → x' j = x j) {p : ℕ} (h : pl x req C p = 0) :
    pv x' C p = pv x C p :=
  bz_add_eq_zero.1 (by rw [pv_add x x' req C hx p, h, map_zero])

theorem rv_eq_of_known (x x' : ℕ → Bool) (req : ℕ → Bool) (C : Circuit)
    (hx : ∀ j, req j = true → x' j = x j) {p a : ℕ} (h : rl x req C p a = 0) :
    rv x' C p a = rv x C p a := by
  by_cases ha : a < p
  · simp only [rl, ha, ↓reduceIte] at h
    simp only [rv, ha, ↓reduceIte, pv_eq_of_known x x' req C hx h]
  · simp [rv, ha]

theorem L_add_self (c : L) : c + c = 0 := by
  ext a
  simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

/-! ### Monotonicity -/

/-- The images of the atoms under the map from the old linear parts to the new ones. -/
noncomputable def ψb (x x' : ℕ → Bool) (req' : ℕ → Bool) (C : Circuit) : Atom → L
  | .inl t => if req' t then 0 else Finsupp.single (Sum.inl t) 1
  | .inr i =>
    match C[i]? with
    | some (.mux s z o) => pl x' req' C i + rl x' req' C i (cand (rv x C i s) z o)
    | _ => 0

/-- The map from the old linear parts to the new ones. -/
noncomputable def ψ (x x' : ℕ → Bool) (req' : ℕ → Bool) (C : Circuit) : L →ₗ[ZMod 2] L :=
  Finsupp.linearCombination (ZMod 2) (ψb x x' req' C)

/-- **Monotonicity.** When more inputs are requested (`req ≤ req'`) and the new input `x'` agrees
with the old one `x` on the inputs requested before, the new linear parts are the image of the
old ones under a linear map. -/
theorem pl_mono (x x' : ℕ → Bool) (req req' : ℕ → Bool) (C : Circuit)
    (hreq : ∀ j, req j = true → req' j = true) (hx : ∀ j, req j = true → x' j = x j) (p : ℕ) :
    pl x' req' C p = ψ x x' req' C (pl x req C p) := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  have hr : ∀ a, rl x' req' C p a = ψ x x' req' C (rl x req C p a) := by
    intro a
    by_cases ha : a < p
    · simp only [rl, ha, ↓reduceIte]; exact ih a ha
    · simp [rl, ha]
  rw [pl_eq, pl_eq]
  cases hC : C[p]? with
  | none => simp [linStep]
  | some n =>
    cases n with
    | input j =>
      by_cases hj : req j = true
      · simp [linStep, hj, hreq j hj]
      · simp [linStep, hj, ψ, ψb]
    | const b => simp [linStep]
    | xor a b => simp only [linStep, map_add, ← hr]
    | mux s z o =>
      simp only [linStep]
      by_cases hs : rl x req C p s = 0
      · have hs' : rl x' req' C p s = 0 := by rw [hr, hs, map_zero]
        simp only [hs, hs', ↓reduceIte, rv_eq_of_known x x' req C hx hs, ← hr]
      · have hA : linStep req' (rv x' C p) (rl x' req' C p) p (some (.mux s z o)) =
            pl x' req' C p := by rw [pl_eq, hC]
        simp only [hs, ↓reduceIte, map_add, ψ, Finsupp.linearCombination_single, one_smul]
        simp only [ψb, hC, ← hA]
        rw [← ψ, ← hr, add_assoc, L_add_self, add_zero]
        rfl

/-- **A wire known before stays known.** -/
theorem known_mono (x x' : ℕ → Bool) (req req' : ℕ → Bool) (C : Circuit)
    (hreq : ∀ j, req j = true → req' j = true) (hx : ∀ j, req j = true → x' j = x j) {p : ℕ}
    (h : pl x req C p = 0) : pl x' req' C p = 0 := by
  rw [pl_mono x x' req req' C hreq hx p, h, map_zero]

/-- A read that is known before stays known. -/
theorem rl_known_mono (x x' : ℕ → Bool) (req req' : ℕ → Bool) (C : Circuit)
    (hreq : ∀ j, req j = true → req' j = true) (hx : ∀ j, req j = true → x' j = x j) {p a : ℕ}
    (h : rl x req C p a = 0) : rl x' req' C p a = 0 := by
  by_cases ha : a < p
  · simp only [rl, ha, ↓reduceIte] at h ⊢; exact known_mono x x' req req' C hreq hx h
  · simp [rl, ha]

/-- **The support of a linear part.** Its atoms are inputs that are not requested, and
multiplexers at earlier or equal positions whose selector, as read there, is unknown. -/
theorem pl_support (x : ℕ → Bool) (req : ℕ → Bool) (C : Circuit) (p : ℕ) (β : Atom)
    (h : pl x req C p β ≠ 0) :
    (∃ j, β = .inl j ∧ req j = false) ∨
      (∃ i, β = .inr i ∧ i ≤ p ∧ ∃ s z o, C[i]? = some (.mux s z o) ∧ rl x req C i s ≠ 0) := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  have hr : ∀ a, rl x req C p a β ≠ 0 →
      (∃ j, β = .inl j ∧ req j = false) ∨
        (∃ i, β = .inr i ∧ i ≤ p ∧ ∃ s z o, C[i]? = some (.mux s z o) ∧ rl x req C i s ≠ 0) := by
    intro a ha
    by_cases hap : a < p
    · simp only [rl, hap, ↓reduceIte] at ha
      rcases ih a hap ha with h1 | ⟨i, h1, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨i, h1, by omega, h3⟩
    · simp [rl, hap] at ha
  rw [pl_eq] at h
  cases hC : C[p]? with
  | none => simp [hC, linStep] at h
  | some n =>
    rw [hC] at h
    cases n with
    | input j =>
      by_cases hj : req j = true
      · simp [linStep, hj] at h
      · simp only [linStep, hj, Bool.false_eq_true, ↓reduceIte] at h
        rw [Finsupp.single_apply] at h
        split_ifs at h with he
        · exact Or.inl ⟨j, he.symm, by simpa using hj⟩
        · exact absurd rfl h
    | const b => simp [linStep] at h
    | xor a b =>
      simp only [linStep, Finsupp.add_apply] at h
      by_cases ha : rl x req C p a β = 0
      · rw [ha, zero_add] at h; exact hr b h
      · exact hr a ha
    | mux s z o =>
      simp only [linStep] at h
      split_ifs at h with hs
      · exact hr _ h
      · rw [Finsupp.add_apply, Finsupp.single_apply] at h
        split_ifs at h with he
        · exact Or.inr ⟨p, he.symm, le_rfl, s, z, o, hC, hs⟩
        · rw [zero_add] at h; exact hr _ h

/-! ### The bridge with the list evaluation -/

theorem plainNode_eq (x : ℕ → Bool) (C : Circuit) {vs : List Bool}
    (hv : ∀ i, vs.getD i false = rv x C vs.length i) (n : Node) :
    plainNode x vs n = valStep x (rv x C vs.length) (some n) := by
  cases n <;> simp only [plainNode, valStep, hv]

theorem plainAux_getD (x : ℕ → Bool) (C : Circuit) :
    ∀ (ns : Circuit) (vs : List Bool) (pre : Circuit), pre.length = vs.length → C = pre ++ ns →
      (∀ i, vs.getD i false = rv x C vs.length i) →
        ∀ i, (plainAux x ns vs).getD i false = rv x C (vs.length + ns.length) i := by
  intro ns
  induction ns with
  | nil => intro vs pre _ _ hv i; simpa only [plainAux, List.length_nil, add_zero] using hv i
  | cons n ns ih =>
    intro vs pre hpre hC hv i
    have hn : C[vs.length]? = some n := by rw [hC, ← hpre]; simp
    have hnode : plainNode x vs n = pv x C vs.length := by
      rw [plainNode_eq x C hv, pv_eq, hn]
    have hv' : ∀ i, (vs ++ [pv x C vs.length]).getD i false =
        rv x C (vs ++ [pv x C vs.length]).length i := by
      intro i
      rw [getD_snoc]
      simp only [List.length_append, List.length_singleton, rv]
      rcases lt_trichotomy i vs.length with h | rfl | h
      · simp only [h, ↓reduceIte, hv i, rv, show i < vs.length + 1 by omega]
      · simp
      · simp [show ¬ i < vs.length by omega, h.ne', show ¬ i < vs.length + 1 by omega]
    have := ih (vs ++ [pv x C vs.length]) (pre ++ [n]) (by simp [hpre]) (by simp [hC]) hv' i
    simp only [plainAux, hnode]
    rw [this]
    congr 1
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- **The list evaluation is the positional one.** -/
theorem plain_getD (x : ℕ → Bool) (C : Circuit) (i : ℕ) : (plain x C).getD i false = pv x C i := by
  have := plainAux_getD x C C [] [] rfl (by simp) (by simp [rv]) i
  rw [plain, this]
  simp only [List.length_nil, zero_add, rv]
  split_ifs with h
  · rfl
  · rw [pv_eq, List.getElem?_eq_none (by omega)]; rfl

end GcZk.Lin
