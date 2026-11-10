/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.COSqDH
import GcZk.Binding

/-!
# Soundness with the Chou–Orlandi OT

The full cheating prover also has an opening phase: after the commitment it sees the seed and the
sender's secrets, makes `n₂` steps, and opens a point. The verifier accepts if the opened label is
the target and the commitment oracle maps the opened point to the commitment.

## Main results

* `GcZk.CO.accept_iff`, `GcZk.CO.ext_of_extWins`: for fixed randomness other than `G`, the prover
  is a prover of `GcZk.Bind`, and the extractor's success is the event `Ext`.
* `GcZk.CO.card_zero_le`: the secrets with a `0` are at most a fraction `k / q`.
* `GcZk.CO.prob_accept_le`: the verifier accepts with probability at most
  `(n₁² + n₂ + 1) / |D| + (Q + 1) / (|V| - 1) + Q / |V| + k / q + Adv`, where `Q = 2(k + n₁)`
  and `Adv` is the sum, over the inputs `j` and all pairs `i ≠ i'` of key query positions, of the
  advantages of the square Diffie–Hellman solvers `S_{j,i,i'}`, each averaged over `G` and `Δ`.
-/

namespace GcZk.CO

open Adaptive Auth RO

variable {V R D Gp : Type*} {q : ℕ}

/-- The verifier's opening: the seed and the sender's secrets. -/
abbrev Op (q : ℕ) (k : ℕ) (V : Type*) := Seed V × (Fin k → ZMod q)

/-- A cheating prover with an opening phase. -/
structure FullProver (q k : ℕ) (V R D Gp : Type*) extends Prover k V R D Gp where
  n₂ : ℕ
  step₂ : (Fin k → Gp) → List V → List (Material V) → (Fin k → V × V) → List (V × V × D) →
    Op q k V → List (V × V × D) → (ℕ × V) × (Fin k × Gp) × (V × R)
  opened : (Fin k → Gp) → List V → List (Material V) → (Fin k → V × V) → List (V × V × D) →
    Op q k V → List (V × V × D) → V × R

/-! ### Oracle runs -/

section Ans

variable {Pt A : Type*}

theorem ans_length (O : Pt → A) (Q : List A → Pt) (n : ℕ) : (Com.ans O Q n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Com.ans, ih]

theorem ans_prefix (O : Pt → A) (Q : List A → Pt) (m d : ℕ) :
    ∃ rest, Com.ans O Q (m + d) = Com.ans O Q m ++ rest := by
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    obtain ⟨rest, h⟩ := ih
    exact ⟨rest ++ [O (Q (Com.ans O Q (m + d)))], by
      rw [← add_assoc, Com.ans, h, List.append_assoc]⟩

theorem ans_take (O : Pt → A) (Q : List A → Pt) {m n : ℕ} (h : m ≤ n) :
    (Com.ans O Q n).take m = Com.ans O Q m := by
  obtain ⟨rest, hr⟩ := ans_prefix O Q m (n - m)
  rw [show m + (n - m) = n by omega] at hr
  rw [hr, List.take_left' (ans_length O Q m)]

theorem ans_getD (O : Pt → A) (Q : List A → Pt) {s n : ℕ} (h : s < n) (d : A) :
    (Com.ans O Q n).getD s d = O (Q (Com.ans O Q s)) := by
  obtain ⟨rest, hr⟩ := ans_prefix O Q (s + 1) (n - (s + 1))
  rw [show s + 1 + (n - (s + 1)) = n by omega] at hr
  rw [hr, Com.ans, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right (by rw [ans_length]), ans_length]
  simp

end Ans

section Game

variable [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup Gp] [Module (ZMod q) Gp]
  (g : Gp) (C : Circuit) (k : ℕ) (G : V × R → D) (P : FullProver q k V R D Gp)

/-- Rebuild the answers of a run from its answers to `G`, answering `H` and `H_K` with the given
oracles. -/
def rep (H : Fin C.length → V → V) (HK : Fin k → Gp → V)
    (st : List (V × V × D) → (ℕ × V) × (Fin k × Gp) × (V × R)) (gs : List D) :
    List (V × V × D) :=
  gs.foldl (fun acc d ↦ acc ++ [(extH H (st acc).1.1 (st acc).1.2, HK (st acc).2.1.1
    (st acc).2.1.2, d)]) []

omit [Module (ZMod 2) V] [AddCommGroup Gp] [Module (ZMod q) Gp] in
theorem rep_snoc (H : Fin C.length → V → V) (HK : Fin k → Gp → V)
    (st : List (V × V × D) → (ℕ × V) × (Fin k × Gp) × (V × R)) (gs : List D) (d : D) :
    rep C k H HK st (gs ++ [d]) = rep C k H HK st gs ++
      [(extH H (st (rep C k H HK st gs)).1.1 (st (rep C k H HK st gs)).1.2,
        HK (st (rep C k H HK st gs)).2.1.1 (st (rep C k H HK st gs)).2.1.2, d)] := by
  simp [rep, List.foldl_append]

omit [Module (ZMod 2) V] [AddCommGroup Gp] [Module (ZMod q) Gp] in
/-- The run against `G` alone, rebuilt, is the full run. -/
theorem rep_ans (H : Fin C.length → V → V) (HK : Fin k → Gp → V)
    (st : List (V × V × D) → (ℕ × V) × (Fin k × Gp) × (V × R)) (n : ℕ) :
    rep C k H HK st (Com.ans G (fun gs ↦ (st (rep C k H HK st gs)).2.2) n) =
      Com.ans (o₁ C k G H HK) st n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Com.ans, rep_snoc, ih, Com.ans]; rfl

/-- The real opening. -/
def opR (Δ : V) (ω : Ω q k C.length V Gp) : Op q k V :=
  (seed C k Δ ω.2.2.2.1.1 ω.2.2.2.1.2, ω.1)

/-- The first steps of the full prover, as a function of their answers. -/
def st₁ (Δ : V) (ω : Ω q k C.length V Gp) :
    List (V × V × D) → (ℕ × V) × (Fin k × Gp) × (V × R) :=
  P.step (msgA g k ω.1) (ans₀ g k P.toProver ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
    (masked g k P.toProver ω.1 ω.2.1 Δ ω.2.2.2.1.1)

/-- The verifier accepts the full prover. -/
def Accept (out : ℕ) (Δ : V) (ω : Ω q k C.length V Gp) : Prop :=
  let A := msgA g k ω.1
  let a₀ := ans₀ g k P.toProver ω.1 ω.2.1
  let M := realM C k Δ ω.2.2.2
  let e := masked g k P.toProver ω.1 ω.2.1 Δ ω.2.2.2.1.1
  let c₁ := ans₁ g C k G P.toProver Δ ω
  let c₂ := Com.ans (o₁ C k G ω.2.2.2.2.1 ω.2.1) (P.step₂ A a₀ M e c₁ (opR C k Δ ω)) P.n₂
  (P.opened A a₀ M e c₁ (opR C k Δ ω) c₂).1 = target C k out Δ ω.2.2.2 ∧
    G (P.opened A a₀ M e c₁ (opR C k Δ ω) c₂) = P.commit A a₀ M e c₁

/-- For fixed randomness other than `G`, the full prover as a prover of `GcZk.Bind`. -/
def toBind (Δ : V) (ω : Ω q k C.length V Gp) : Bind.Prover Unit (Op q k V) (V × R) D where
  q₁ := P.n₁
  q₂ := P.n₂
  Q₁ _ gs := (st₁ g C k P Δ ω (rep C k ω.2.2.2.2.1 ω.2.1 (st₁ g C k P Δ ω) gs)).2.2
  commit _ gs := P.commit (msgA g k ω.1) (ans₀ g k P.toProver ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
    (masked g k P.toProver ω.1 ω.2.1 Δ ω.2.2.2.1.1)
    (rep C k ω.2.2.2.2.1 ω.2.1 (st₁ g C k P Δ ω) gs)
  Q₂ _ gs op gs₂ :=
    let st₂ := P.step₂ (msgA g k ω.1) (ans₀ g k P.toProver ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
      (masked g k P.toProver ω.1 ω.2.1 Δ ω.2.2.2.1.1)
      (rep C k ω.2.2.2.2.1 ω.2.1 (st₁ g C k P Δ ω) gs) op
    (st₂ (rep C k ω.2.2.2.2.1 ω.2.1 st₂ gs₂)).2.2
  opened _ gs op gs₂ :=
    let st₂ := P.step₂ (msgA g k ω.1) (ans₀ g k P.toProver ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
      (masked g k P.toProver ω.1 ω.2.1 Δ ω.2.2.2.1.1)
      (rep C k ω.2.2.2.2.1 ω.2.1 (st₁ g C k P Δ ω) gs) op
    P.opened (msgA g k ω.1) (ans₀ g k P.toProver ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
      (masked g k P.toProver ω.1 ω.2.1 Δ ω.2.2.2.1.1)
      (rep C k ω.2.2.2.2.1 ω.2.1 (st₁ g C k P Δ ω) gs) op (rep C k ω.2.2.2.2.1 ω.2.1 st₂ gs₂)

omit [Module (ZMod 2) V] in
theorem a₁_toBind (Δ : V) (ω : Ω q k C.length V Gp) :
    rep C k ω.2.2.2.2.1 ω.2.1 (st₁ g C k P Δ ω) (Bind.a₁ (toBind g C k P Δ ω) () G) =
      ans₁ g C k G P.toProver Δ ω :=
  rep_ans C k G ω.2.2.2.2.1 ω.2.1 _ P.n₁

omit [Module (ZMod 2) V] in
/-- **The real acceptance is the acceptance of `GcZk.Bind`.** -/
theorem accept_iff (out : ℕ) (Δ : V) (ω : Ω q k C.length V Gp) :
    Accept g C k G P out Δ ω ↔ Bind.Accept (toBind g C k P Δ ω) () (opR C k Δ ω)
      (fun p ↦ p.1 = target C k out Δ ω.2.2.2) G := by
  unfold Accept Bind.Accept Bind.opn Bind.com
  have ha := a₁_toBind g C k G P Δ ω
  generalize Bind.a₁ (toBind g C k P Δ ω) () G = a1 at ha ⊢
  simp only [toBind]
  rw [ha, rep_ans]

omit [Module (ZMod 2) V] in
theorem qry₁_toBind (Δ : V) (ω : Ω q k C.length V Gp) (t : ℕ) :
    Bind.qry₁ (toBind g C k P Δ ω) () G t =
      (st₁ g C k P Δ ω (Com.ans (o₁ C k G ω.2.2.2.2.1 ω.2.1) (st₁ g C k P Δ ω) t)).2.2 := by
  unfold Bind.qry₁
  simp only [toBind]
  rw [rep_ans]

omit [Module (ZMod 2) V] in
/-- **The extractor's success is `Ext`.** -/
theorem ext_of_extWins (out : ℕ) (Δ : V) (ω : Ω q k C.length V Gp)
    (hw : Bind.ExtWins (toBind g C k P Δ ω) () (fun p ↦ p.1 = target C k out Δ ω.2.2.2) G) :
    Ext g C k G P.toProver out Δ ω := by
  classical
  obtain ⟨t, ht, hval, hmin, hacc⟩ := hw
  have ht : t < P.n₁ := ht
  have hcom : Bind.com (toBind g C k P Δ ω) () G = P.commit (msgA g k ω.1)
      (ans₀ g k P.toProver ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
      (masked g k P.toProver ω.1 ω.2.1 Δ ω.2.2.2.1.1) (ans₁ g C k G P.toProver Δ ω) := by
    unfold Bind.com
    have ha := a₁_toBind g C k G P Δ ω
    generalize Bind.a₁ (toBind g C k P Δ ω) () G = a1 at ha ⊢
    simp only [toBind]
    rw [ha]
  rw [hcom, qry₁_toBind] at hval
  rw [qry₁_toBind] at hacc
  have hmin' : ∀ l < t, G (st₁ g C k P Δ ω (Com.ans (o₁ C k G ω.2.2.2.2.1 ω.2.1)
      (st₁ g C k P Δ ω) l)).2.2 ≠ P.commit (msgA g k ω.1) (ans₀ g k P.toProver ω.1 ω.2.1)
        (realM C k Δ ω.2.2.2) (masked g k P.toProver ω.1 ω.2.1 Δ ω.2.2.2.1.1)
        (ans₁ g C k G P.toProver Δ ω) := fun l hl ↦ by
    have := hmin l hl; rwa [hcom, qry₁_toBind] at this
  have hc : ans₁ g C k G P.toProver Δ ω =
      Com.ans (o₁ C k G ω.2.2.2.2.1 ω.2.1) (st₁ g C k P Δ ω) P.n₁ := rfl
  have hget : ∀ s < P.n₁, ∀ d, ((ans₁ g C k G P.toProver Δ ω).getD s d).2.2 =
      G (st₁ g C k P Δ ω (Com.ans (o₁ C k G ω.2.2.2.2.1 ω.2.1) (st₁ g C k P Δ ω) s)).2.2 := by
    intro s hs d; rw [hc, ans_getD _ _ hs]; rfl
  have hlen : (ans₁ g C k G P.toProver Δ ω).length = P.n₁ := by rw [hc, ans_length]
  unfold Ext guessOf
  set cm := P.commit (msgA g k ω.1) (ans₀ g k P.toProver ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
    (masked g k P.toProver ω.1 ω.2.1 Δ ω.2.2.2.1.1) (ans₁ g C k G P.toProver Δ ω)
  have hex : ∃ s < P.n₁, ((ans₁ g C k G P.toProver Δ ω).getD s (0, 0, cm)).2.2 = cm ∧
      s < (ans₁ g C k G P.toProver Δ ω).length :=
    ⟨t, ht, by rw [hget t ht]; exact hval, by rw [hlen]; exact ht⟩
  have hfind : Nat.find hex = t := by
    refine le_antisymm (Nat.find_min' hex ⟨ht, by rw [hget t ht]; exact hval, by omega⟩) ?_
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hs, hv, -⟩ := Nat.find_spec hex
    rw [hget _ hs] at hv
    exact hmin' _ hlt hv
  simp only [hex, ↓reduceDIte, hfind]
  rw [hc, ans_take _ _ ht.le]
  exact hacc

/-! ### Counting -/

section Count

variable [Fintype V] [DecidableEq V] [Fintype Gp] [DecidableEq Gp] [NeZero q]

omit [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup Gp] [Module (ZMod q) Gp] in
open Classical in
/-- **A secret is `0`** for at most a fraction `k / q` of the randomness. -/
theorem card_zero_le :
    (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Zero C k ω).card * q ≤
      k * Fintype.card (Ω q k C.length V Gp) := by
  have hj : ∀ j : Fin k, (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ ω.1 j = 0).card * q ≤
      Fintype.card (Ω q k C.length V Gp) := by
    intro j
    have hq : (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ ω.1 j = 0).card * q =
        ((Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ ω.1 j = 0) ×ˢ
          (Finset.univ : Finset (ZMod q))).card := by
      rw [Finset.card_product, Finset.card_univ, ZMod.card]
    rw [hq, ← Finset.card_univ (α := Ω q k C.length V Gp)]
    refine Finset.card_le_card_of_injOn (fun p ↦ (Function.update p.1.1 j p.2, p.1.2))
      (fun _ _ ↦ Finset.mem_univ _) ?_
    rintro ⟨ω1, x1⟩ h1 ⟨ω2, x2⟩ h2 he
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and,
      Finset.coe_univ, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true] at h1 h2
    simp only [Prod.mk.injEq] at he
    have hx : x1 = x2 := by simpa using congrFun he.1 j
    have ha : ω1.1 = ω2.1 := by
      funext j'
      by_cases h : j' = j
      · subst h; rw [h1, h2]
      · simpa [Function.update_of_ne h] using congrFun he.1 j'
    rw [hx, show ω1 = ω2 from Prod.ext ha he.2]
  calc _ ≤ (∑ j : Fin k, (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ ω.1 j = 0).card) * q :=
        Nat.mul_le_mul_right _ ((Finset.card_le_card fun ω hω ↦ by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
          obtain ⟨j, hj⟩ := hω
          exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, by simpa using hj⟩).trans
            Finset.card_biUnion_le)
    _ = ∑ j : Fin k, (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ ω.1 j = 0).card * q :=
        Finset.sum_mul _ _ _
    _ ≤ ∑ _j : Fin k, Fintype.card (Ω q k C.length V Gp) := Finset.sum_le_sum fun j _ ↦ hj j
    _ = _ := by simp

open Classical in
omit [Module (ZMod 2) V] in
/-- **The event `Ext`** splits into the OT layer, both key points, and a secret `0`. -/
theorem card_ext_split [Fact q.Prime] (hg : Function.Bijective fun b : ZMod q ↦ b • g)
    (out : ℕ) (P : Prover k V R D Gp) (Δ : V) :
    (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Ext g C k G P out Δ ω).card ≤
      (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Ext g C k G P out Δ ω ∧
        ¬ Both g C k G P Δ ω ∧ ∀ j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j false ≠
          key g k ω.1 (msgB g k P ω.1 ω.2.1) j true).card +
      (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Both g C k G P Δ ω ∧
        ¬ Zero C k ω).card +
      (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Zero C k ω).card := by
  refine (Finset.card_le_card fun ω hω ↦ ?_).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hω ⊢
  by_cases hz : Zero C k ω
  · exact Or.inr hz
  · by_cases hb : Both g C k G P Δ ω
    · exact Or.inl (Or.inr ⟨hb, hz⟩)
    · exact Or.inl (Or.inl ⟨hω, hb, fun j ↦ key_ne g k hg _ fun h ↦ hz ⟨j, h⟩⟩)

end Count

end Game

/-! ### The bound -/

section Final

variable [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup Gp] [Module (ZMod q) Gp]
  [Fintype V] [DecidableEq V] [Fintype R] [Fintype D] [Fintype Gp] [DecidableEq Gp] [NeZero q]
  (g : Gp) (C : Circuit) (k : ℕ) (P : FullProver q k V R D Gp)

open Classical in
/-- The numerator of the square Diffie–Hellman term: over `G`, `Δ ≠ 0`, the input `j` and the
guesses `i ≠ i'`, the pairs `(x, σ)` on which the solver `S_{j,i,i'}` wins. -/
noncomputable def sqdhWins : ℕ :=
  ∑ G : V × R → D, ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), ∑ j : Fin k,
    ∑ ii ∈ (Finset.range (P.n₀ + P.n₁)).offDiag,
      (Finset.univ.filter fun xσ : ZMod q × Ω q k C.length V Gp ↦ xσ.2.1 j = 0 ∧
        SqDH.Wins g (solver g C k G P.toProver j ii.1 ii.2 Δ xσ.2) xσ.1).card

omit [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup Gp] [Module (ZMod q) Gp] [Fintype R]
  [Fintype D] [NeZero q] in
theorem card_Ω [Fintype (ZMod q)] :
    Fintype.card (Ω q k C.length V Gp) =
      Fintype.card (Γ q k V Gp) * Fintype.card (Rand V k C.length) := by
  simp only [Fintype.card_prod]; ring

open Classical in
/-- **Soundness with the Chou–Orlandi OT, counting form.** Summed over `Δ ≠ 0`, the real
randomness `ω` and the commitment oracle `G`, the accepting runs satisfy
`T |D| ≤ y |D| + (|V| - 1) |Ω| (n₁² + n₂ + 1) |G|` with
`y ≤ A + sqdhWins + |G| (|V| - 1) #Zero` and `|V| A ≤ |G| |Ω| (|V| + Q (2|V| - 1))`. -/
theorem card_accept_parts [Fact q.Prime] (hg : Function.Bijective fun b : ZMod q ↦ b • g)
    (out : ℕ) (hC : ∀ x, (plain x C).getD out false = false) :
    ∃ y A : ℕ,
      (∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), ∑ ω : Ω q k C.length V Gp,
        (Finset.univ.filter fun G : V × R → D ↦ Accept g C k G P out Δ ω).card) *
          Fintype.card D ≤
        y * Fintype.card D + (Fintype.card V - 1) * Fintype.card (Ω q k C.length V Gp) *
          ((P.n₁ * P.n₁ + P.n₂ + 1) * Fintype.card (V × R → D)) ∧
      y ≤ A + sqdhWins g C k P + Fintype.card (V × R → D) * ((Fintype.card V - 1) *
        (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Zero C k ω).card) ∧
      Fintype.card V * A ≤ Fintype.card (V × R → D) * (Fintype.card (Ω q k C.length V Gp) *
        (Fintype.card V + (2 * k + 2 * P.n₁) * (Fintype.card V + (Fintype.card V - 1)))) := by
  have hS : (Finset.univ.filter (· ≠ (0 : V))).card = Fintype.card V - 1 := by
    rw [Finset.filter_ne' Finset.univ (0 : V), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
  set S := Finset.univ.filter (· ≠ (0 : V))
  set E := (P.n₁ * P.n₁ + P.n₂ + 1) * Fintype.card (V × R → D)
  set y := ∑ Δ ∈ S, ∑ ω : Ω q k C.length V Gp,
    (Finset.univ.filter fun G : V × R → D ↦ Ext g C k G P.toProver out Δ ω).card
  set A := ∑ G : V × R → D, ∑ Δ ∈ S,
    (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Ext g C k G P.toProver out Δ ω ∧
      ¬ Both g C k G P.toProver Δ ω ∧ ∀ j, key g k ω.1 (msgB g k P.toProver ω.1 ω.2.1) j false ≠
        key g k ω.1 (msgB g k P.toProver ω.1 ω.2.1) j true).card
  refine ⟨y, A, ?_, ?_, ?_⟩
  · -- binding, for each `Δ` and `ω`
    have hb : ∀ Δ (ω : Ω q k C.length V Gp),
        (Finset.univ.filter fun G : V × R → D ↦ Accept g C k G P out Δ ω).card *
          Fintype.card D ≤
        (Finset.univ.filter fun G : V × R → D ↦ Ext g C k G P.toProver out Δ ω).card *
          Fintype.card D + E := by
      intro Δ ω
      have h1 := Bind.card_accept_le (toBind g C k P Δ ω) () (opR C k Δ ω)
        (fun p ↦ p.1 = target C k out Δ ω.2.2.2)
      have h2 : (Finset.univ.filter fun G : V × R → D ↦ Accept g C k G P out Δ ω).card ≤
          (Finset.univ.filter fun G : V × R → D ↦ Ext g C k G P.toProver out Δ ω).card +
          (Finset.univ.filter fun G : V × R → D ↦ Bind.Accept (toBind g C k P Δ ω) ()
            (opR C k Δ ω) (fun p ↦ p.1 = target C k out Δ ω.2.2.2) G ∧
            ¬ Bind.ExtWins (toBind g C k P Δ ω) () (fun p ↦ p.1 = target C k out Δ ω.2.2.2)
              G).card := by
        refine (Finset.card_le_card fun G hG ↦ ?_).trans (Finset.card_union_le _ _)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hG ⊢
        by_cases he : Bind.ExtWins (toBind g C k P Δ ω) ()
          (fun p ↦ p.1 = target C k out Δ ω.2.2.2) G
        · exact Or.inl (ext_of_extWins g C k G P out Δ ω he)
        · exact Or.inr ⟨(accept_iff g C k G P out Δ ω).1 hG, he⟩
      have := Nat.mul_le_mul_right (Fintype.card D) h2
      rw [Nat.add_mul] at this
      exact this.trans (Nat.add_le_add_left h1 _)
    calc _ = ∑ Δ ∈ S, ∑ ω : Ω q k C.length V Gp,
          (Finset.univ.filter fun G : V × R → D ↦ Accept g C k G P out Δ ω).card *
            Fintype.card D := by simp only [Finset.sum_mul]
      _ ≤ ∑ Δ ∈ S, ∑ ω : Ω q k C.length V Gp,
          ((Finset.univ.filter fun G : V × R → D ↦ Ext g C k G P.toProver out Δ ω).card *
            Fintype.card D + E) :=
          Finset.sum_le_sum fun Δ _ ↦ Finset.sum_le_sum fun ω _ ↦ hb Δ ω
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, Finset.card_univ,
            smul_eq_mul, hS, y]
          ring
  · -- the event `Ext`, for each `G` and `Δ`
    have hswap : y = ∑ G : V × R → D, ∑ Δ ∈ S,
        (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦
          Ext g C k G P.toProver out Δ ω).card := by
      simp only [y, Finset.card_filter]
      exact (Finset.sum_congr rfl fun Δ _ ↦ Finset.sum_comm).trans Finset.sum_comm
    rw [hswap]
    calc _ ≤ ∑ G : V × R → D, ∑ Δ ∈ S,
          ((Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Ext g C k G P.toProver out Δ ω ∧
            ¬ Both g C k G P.toProver Δ ω ∧ ∀ j, key g k ω.1 (msgB g k P.toProver ω.1 ω.2.1) j
              false ≠ key g k ω.1 (msgB g k P.toProver ω.1 ω.2.1) j true).card +
          ∑ j : Fin k, ∑ ii ∈ (Finset.range (P.n₀ + P.n₁)).offDiag,
            (Finset.univ.filter fun xσ : ZMod q × Ω q k C.length V Gp ↦ xσ.2.1 j = 0 ∧
              SqDH.Wins g (solver g C k G P.toProver j ii.1 ii.2 Δ xσ.2) xσ.1).card +
          (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Zero C k ω).card) :=
          Finset.sum_le_sum fun G _ ↦ Finset.sum_le_sum fun Δ _ ↦
            (card_ext_split g C k G hg out P.toProver Δ).trans (Nat.add_le_add_right
              (Nat.add_le_add_left (card_both_le g C k G P.toProver hg Δ) _) _)
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, hS, smul_eq_mul, Finset.card_univ,
            A, sqdhWins, S]
  · -- the OT layer, for each `G`
    calc Fintype.card V * A = ∑ G : V × R → D, Fintype.card V * ∑ Δ ∈ S,
          (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Ext g C k G P.toProver out Δ ω ∧
            ¬ Both g C k G P.toProver Δ ω ∧ ∀ j, key g k ω.1 (msgB g k P.toProver ω.1 ω.2.1) j
              false ≠ key g k ω.1 (msgB g k P.toProver ω.1 ω.2.1) j true).card := by
          rw [Finset.mul_sum]
      _ ≤ ∑ _G : V × R → D, Fintype.card (Γ q k V Gp) * (Fintype.card V *
          Fintype.card (Rand V k C.length) + (2 * k + 2 * P.n₁) * ((Fintype.card V +
            (Fintype.card V - 1)) * Fintype.card (Rand V k C.length))) :=
          Finset.sum_le_sum fun G _ ↦ card_ext_le g C k G P.toProver out hC
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, card_Ω]
          ring

open Classical in
/-- **Soundness with the Chou–Orlandi OT.** For an unsatisfiable circuit, with `Δ` uniform on
`V \ {0}` and the secrets, the key hash, the seed, the garbling hash and the commitment oracle
uniform, the verifier accepts the cheating prover with probability at most
`(n₁² + n₂ + 1) / |D| + (Q + 1) / (|V| - 1) + Q / |V| + k / q + Adv`, where `Q = 2(k + n₁)` and
`Adv` is the sum over `j` and `i ≠ i'` of the advantages of the square Diffie–Hellman solvers
`S_{j,i,i'}`, each averaged over `G` and `Δ` (`sqdhWins`, normalized). The group order `q` is
prime. -/
theorem prob_accept_le [Nontrivial V] [Nonempty D] [Fact q.Prime]
    (hg : Function.Bijective fun b : ZMod q ↦ b • g) (out : ℕ)
    (hC : ∀ x, (plain x C).getD out false = false) :
    ((∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), ∑ ω : Ω q k C.length V Gp,
      (Finset.univ.filter fun G : V × R → D ↦ Accept g C k G P out Δ ω).card : ℕ) : ℝ) /
        ((Fintype.card V - 1) * Fintype.card (Ω q k C.length V Gp) *
          Fintype.card (V × R → D)) ≤
      ((P.n₁ * P.n₁ + P.n₂ + 1 : ℕ) : ℝ) / Fintype.card D +
        ((2 * k + 2 * P.n₁ : ℕ) + 1 : ℝ) / (Fintype.card V - 1) +
        ((2 * k + 2 * P.n₁ : ℕ) : ℝ) / Fintype.card V + (k : ℝ) / q +
        (sqdhWins g C k P : ℝ) / ((Fintype.card V - 1) * Fintype.card (Ω q k C.length V Gp) *
          Fintype.card (V × R → D)) := by
  obtain ⟨y, A, h1, h2, h3⟩ := card_accept_parts g C k P hg out hC
  have hz := card_zero_le (V := V) (Gp := Gp) (q := q) C k
  have hΩ : 0 < Fintype.card (Ω q k C.length V Gp) := Fintype.card_pos
  have hG : 0 < Fintype.card (V × R → D) := Fintype.card_pos
  have hDpos : 0 < Fintype.card D := Fintype.card_pos
  have hV1 : 1 < Fintype.card V := Fintype.one_lt_card
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  generalize (∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), ∑ ω : Ω q k C.length V Gp,
      (Finset.univ.filter fun G : V × R → D ↦ Accept g C k G P out Δ ω).card) = T at h1 ⊢
  generalize sqdhWins g C k P = W at h2 ⊢
  generalize (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Zero C k ω).card = Z at h2 hz
  generalize Fintype.card V = n at h1 h2 h3 hV1 ⊢
  generalize Fintype.card (Ω q k C.length V Gp) = NΩ at h1 h3 hz hΩ ⊢
  generalize Fintype.card (V × R → D) = NG at h1 h2 h3 hG ⊢
  generalize Fintype.card D = Dn at h1 hDpos ⊢
  generalize 2 * k + 2 * P.n₁ = Q at h3 ⊢
  generalize P.n₁ * P.n₁ + P.n₂ + 1 = E at h1 ⊢
  -- to the reals
  have h1r : (T : ℝ) * Dn ≤ y * Dn + (n - 1) * NΩ * (E * NG) := by
    have := (Nat.cast_le (α := ℝ)).2 h1; push_cast [Nat.cast_sub hV1.le] at this; linarith
  have h2r : (y : ℝ) ≤ A + W + NG * ((n - 1) * Z) := by
    have := (Nat.cast_le (α := ℝ)).2 h2; push_cast [Nat.cast_sub hV1.le] at this; linarith
  have h3r : (n : ℝ) * A ≤ NG * (NΩ * (n + Q * (n + (n - 1)))) := by
    have := (Nat.cast_le (α := ℝ)).2 h3; push_cast [Nat.cast_sub hV1.le] at this; linarith
  have hzr : (Z : ℝ) * q ≤ k * NΩ := by exact_mod_cast hz
  have hn : (1 : ℝ) < n := by exact_mod_cast hV1
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hΩr : (0 : ℝ) < NΩ := by exact_mod_cast hΩ
  have hGr : (0 : ℝ) < NG := by exact_mod_cast hG
  have hDr : (0 : ℝ) < Dn := by exact_mod_cast hDpos
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hden : (0 : ℝ) < (n - 1) * NΩ * NG := by positivity
  have a1 : (T : ℝ) ≤ y + (E : ℝ) * (n - 1) * NΩ * NG / Dn := by
    have : (T : ℝ) - y ≤ (E : ℝ) * (n - 1) * NΩ * NG / Dn := by
      rw [le_div_iff₀ hDr]; nlinarith
    linarith
  have a3 : (A : ℝ) ≤ (Q + 1) * NΩ * NG + Q * (n - 1) * NΩ * NG / n := by
    have e : (Q + 1 : ℝ) * NΩ * NG + Q * (n - 1) * NΩ * NG / n =
        NG * (NΩ * (n + Q * (n + (n - 1)))) / n := by field_simp; ring
    rw [e, le_div_iff₀ hn0]; linarith
  have a4 : (NG : ℝ) * ((n - 1) * Z) ≤ k * (n - 1) * NΩ * NG / q := by
    have hZ : (Z : ℝ) ≤ k * NΩ / q := by rw [le_div_iff₀ hqr]; linarith
    have e : (k : ℝ) * (n - 1) * NΩ * NG / q = NG * ((n - 1) * (k * NΩ / q)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ hn1.le) hGr.le
  rw [div_le_iff₀ hden]
  have eq : ((E : ℝ) / Dn + ((Q : ℝ) + 1) / (n - 1) + (Q : ℝ) / n + (k : ℝ) / q +
      (W : ℝ) / ((n - 1) * NΩ * NG)) * ((n - 1) * NΩ * NG) =
      (E : ℝ) * (n - 1) * NΩ * NG / Dn + (Q + 1) * NΩ * NG + Q * (n - 1) * NΩ * NG / n +
        k * (n - 1) * NΩ * NG / q + W := by
    field_simp
  rw [eq]
  linarith

end Final

end GcZk.CO
