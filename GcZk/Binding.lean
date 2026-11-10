/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.Commitment

/-!
# JKO with a hash commitment: soundness by extraction

A cheating prover commits with the random oracle `G : P → D` (points `P = V × R`) before the
verifier opens its seed. It sees some view `v` of the garbling, makes `q₁` adaptive queries to
`G`, and commits to `c`. After the opening it makes `q₂` more queries and opens a point
`(Z, r)`. The verifier accepts if `G(Z, r) = c` and `Z` is the target `T` (the `1`-label of the
output, which the opening determines).

The *extractor* reads the prover's first-phase queries and returns the label of the first query
answered with `c`. It does not see the opening, so it is an adversary for the authenticity game
of the garbling.

## Main result

* `GcZk.Bind.card_accept_le`: summed over all oracles, the prover is accepted without the
  extractor returning `T` for at most `(q₁² + q₂ + 1) |D|^{|P|} / |D|` oracles. That is,
  `Pr[accept] ≤ Pr[extractor outputs T] + (q₁² + q₂ + 1) / |D|`.

Combined with the authenticity bound `GcZk.Sec.garble_rom_bound` (in `GcZk.EndToEnd`), the
extractor's success is bounded by the authenticity advantage. The extractor answers the
commitment oracle itself, so it makes the prover's queries to the garbling hash and no others.

## Proof

If the prover is accepted but the extractor does not return `T`, then one of three things
happened: two distinct first-phase queries got the same answer (a collision), a fresh
second-phase query was answered with `c`, or the opened point was never queried and its value is
`c`. In each case a value of `G` at a fresh point equals a value fixed before it. Reprogramming
that point gives `|D|` oracles with the same run, so such oracles are at most a `1/|D|` fraction.
-/

namespace GcZk.Bind

open Com

variable {P D : Type*} [DecidableEq P]

/-! ### Fresh points -/

/-- **The fiber bound.** Let `p G` be a point and `f G` a value, both unchanged when `G` is
reprogrammed at `p G` (on the oracles satisfying `good`). Then the oracles
with `G (p G) = f G` are at most a `1/|D|` fraction. -/
theorem card_fresh_le [Fintype P] [Fintype D] (ev good : (P → D) → Prop) [DecidablePred ev]
    (p : (P → D) → P) (f : (P → D) → D) (hev : ∀ G, ev G ↔ good G ∧ G (p G) = f G)
    (hp : ∀ G v, good G → p (Function.update G (p G) v) = p G)
    (hf : ∀ G v, good G → f (Function.update G (p G) v) = f G) :
    (Finset.univ.filter ev).card * Fintype.card D ≤ Fintype.card (P → D) := by
  rw [← Finset.card_univ (α := D), ← Finset.card_product, ← Finset.card_univ (α := P → D)]
  refine Finset.card_le_card_of_injOn (fun x ↦ Function.update x.1 (p x.1) x.2)
    (fun _ _ ↦ Finset.mem_univ _) ?_
  rintro ⟨G₁, v₁⟩ h₁ ⟨G₂, v₂⟩ h₂ e
  simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and,
    Set.mem_prod, Set.mem_ofPred_eq, Finset.coe_univ, Set.mem_univ, and_true] at h₁ h₂ e
  rw [hev] at h₁ h₂
  have ep : p G₁ = p G₂ := by
    rw [← hp G₁ v₁ h₁.1, ← hp G₂ v₂ h₂.1, e]
  have ef : f G₁ = f G₂ := by
    rw [← hf G₁ v₁ h₁.1, ← hf G₂ v₂ h₂.1, e]
  have eG : G₁ = G₂ := by
    funext y
    by_cases hy : y = p G₁
    · subst hy; rw [h₁.2, ef, ← h₂.2, ep]
    · have := congrFun e y
      rwa [Function.update_of_ne hy, Function.update_of_ne (ep ▸ hy)] at this
  subst eG
  have := congrFun e (p G₁)
  simp only [Function.update_self] at this
  simp [this]

/-- Queries before `n` avoid `p`: then reprogramming `p` changes no answer before `n`. -/
theorem ans_update_of_avoid (O : P → D) (Q : List D → P) (n : ℕ) (p : P) (v : D)
    (h : ∀ k < n, Q (ans O Q k) ≠ p) : ans (Function.update O p v) Q n = ans O Q n :=
  ans_update O Q n p v fun ⟨k, hk, e⟩ ↦ h k hk e

/-! ### The cheating prover -/

/-- A deterministic cheating prover with view type `W` and opening type `S`. -/
structure Prover (W S P D : Type*) where
  q₁ : ℕ
  q₂ : ℕ
  Q₁ : W → List D → P
  commit : W → List D → D
  Q₂ : W → List D → S → List D → P
  opened : W → List D → S → List D → P

variable {W S : Type*} (B : Prover W S P D) (v : W) (s : S)

/-- The first-phase answers. -/
def a₁ (G : P → D) : List D := ans G (B.Q₁ v) B.q₁

/-- The `k`-th first-phase query. -/
def qry₁ (G : P → D) (k : ℕ) : P := B.Q₁ v (ans G (B.Q₁ v) k)

/-- The commitment. -/
def com (G : P → D) : D := B.commit v (a₁ B v G)

/-- The `k`-th second-phase query. -/
def qry₂ (G : P → D) (k : ℕ) : P :=
  B.Q₂ v (a₁ B v G) s (ans G (B.Q₂ v (a₁ B v G) s) k)

/-- The opened point. -/
def opn (G : P → D) : P := B.opened v (a₁ B v G) s (ans G (B.Q₂ v (a₁ B v G) s) B.q₂)

/-- The verifier accepts the opening for the target point set `acc` (in JKO, the points with
first coordinate the target label). -/
def Accept (acc : P → Prop) (G : P → D) : Prop :=
  acc (opn B v s G) ∧ G (opn B v s G) = com B v G

/-- The extractor's success: some first-phase query, the first one answered with the
commitment, lies in the target set. -/
def ExtWins (acc : P → Prop) (G : P → D) : Prop :=
  ∃ k < B.q₁, G (qry₁ B v G k) = com B v G ∧ (∀ l < k, G (qry₁ B v G l) ≠ com B v G) ∧
    acc (qry₁ B v G k)

/-! ### The three bad events -/

/-- A collision: a fresh first-phase query gets the answer of an earlier, different one. -/
def Coll (G : P → D) (i j : ℕ) : Prop :=
  (∀ l < j, qry₁ B v G l ≠ qry₁ B v G j) ∧ qry₁ B v G i ≠ qry₁ B v G j ∧ i < j ∧
    G (qry₁ B v G j) = G (qry₁ B v G i)

/-- A fresh second-phase query is answered with the commitment. -/
def Hit₂ (G : P → D) (k : ℕ) : Prop :=
  ((∀ l < B.q₁, qry₁ B v G l ≠ qry₂ B v s G k) ∧ (∀ l < k, qry₂ B v s G l ≠ qry₂ B v s G k)) ∧
    G (qry₂ B v s G k) = com B v G

/-- The opened point was never queried and its value is the commitment. -/
def HitOpen (G : P → D) : Prop :=
  ((∀ l < B.q₁, qry₁ B v G l ≠ opn B v s G) ∧ (∀ l < B.q₂, qry₂ B v s G l ≠ opn B v s G)) ∧
    G (opn B v s G) = com B v G

/-! ### Invariance under reprogramming a fresh point -/

theorem qry₁_update (G : P → D) (j : ℕ) (p : P) (x : D) (h : ∀ l < j, qry₁ B v G l ≠ p)
    {k : ℕ} (hk : k ≤ j) : qry₁ B v (Function.update G p x) k = qry₁ B v G k := by
  unfold qry₁
  rw [ans_update_of_avoid G _ k p x fun l hl ↦ h l (by omega)]

theorem a₁_update (G : P → D) (p : P) (x : D) (h : ∀ l < B.q₁, qry₁ B v G l ≠ p) :
    a₁ B v (Function.update G p x) = a₁ B v G :=
  ans_update_of_avoid G _ _ p x h

theorem qry₂_update (G : P → D) (k : ℕ) (p : P) (x : D) (h₁ : ∀ l < B.q₁, qry₁ B v G l ≠ p)
    (h₂ : ∀ l < k, qry₂ B v s G l ≠ p) {m : ℕ} (hm : m ≤ k) :
    qry₂ B v s (Function.update G p x) m = qry₂ B v s G m := by
  unfold qry₂
  rw [a₁_update B v G p x h₁, ans_update_of_avoid G _ m p x fun l hl ↦ h₂ l (by omega)]

theorem opn_update (G : P → D) (p : P) (x : D) (h₁ : ∀ l < B.q₁, qry₁ B v G l ≠ p)
    (h₂ : ∀ l < B.q₂, qry₂ B v s G l ≠ p) :
    opn B v s (Function.update G p x) = opn B v s G := by
  unfold opn
  rw [a₁_update B v G p x h₁, ans_update_of_avoid G _ B.q₂ p x h₂]

/-! ### Each bad event has probability at most `1 / |D|` -/

section Card

variable [Fintype P] [Fintype D]


open Classical in
theorem card_coll_le (i j : ℕ) :
    (Finset.univ.filter fun G : P → D ↦ Coll B v G i j).card * Fintype.card D ≤
      Fintype.card (P → D) := by
  refine card_fresh_le _ (fun G ↦ (∀ l < j, qry₁ B v G l ≠ qry₁ B v G j) ∧
      qry₁ B v G i ≠ qry₁ B v G j ∧ i < j)
    (fun G ↦ qry₁ B v G j) (fun G ↦ G (qry₁ B v G i)) (fun G ↦ by unfold Coll; tauto)
    ?_ ?_
  · intro G x hG
    exact qry₁_update B v G j _ x hG.1 le_rfl
  · intro G x hG
    show Function.update G (qry₁ B v G j) x (qry₁ B v (Function.update G (qry₁ B v G j) x) i) =
      G (qry₁ B v G i)
    rw [qry₁_update B v G j _ x hG.1 hG.2.2.le, Function.update_of_ne hG.2.1]

open Classical in
theorem card_hit₂_le (k : ℕ) :
    (Finset.univ.filter fun G : P → D ↦ Hit₂ B v s G k).card * Fintype.card D ≤
      Fintype.card (P → D) := by
  refine card_fresh_le _ (fun G ↦ (∀ l < B.q₁, qry₁ B v G l ≠ qry₂ B v s G k) ∧
      (∀ l < k, qry₂ B v s G l ≠ qry₂ B v s G k))
    (fun G ↦ qry₂ B v s G k) (fun G ↦ com B v G) (fun G ↦ Iff.rfl) ?_ ?_
  · intro G x hG
    exact qry₂_update B v s G k _ x hG.1 hG.2 le_rfl
  · intro G x hG
    show com B v _ = com B v G
    simp only [com]
    rw [a₁_update B v G _ x hG.1]

open Classical in
theorem card_hitOpen_le :
    (Finset.univ.filter fun G : P → D ↦ HitOpen B v s G).card * Fintype.card D ≤
      Fintype.card (P → D) := by
  refine card_fresh_le _ (fun G ↦ (∀ l < B.q₁, qry₁ B v G l ≠ opn B v s G) ∧
      (∀ l < B.q₂, qry₂ B v s G l ≠ opn B v s G))
    (fun G ↦ opn B v s G) (fun G ↦ com B v G) (fun G ↦ Iff.rfl) ?_ ?_
  · intro G x hG
    exact opn_update B v s G _ x hG.1 hG.2
  · intro G x hG
    show com B v _ = com B v G
    simp only [com]
    rw [a₁_update B v G _ x hG.1]

open Classical in
omit [Fintype P] [Fintype D] [DecidableEq P] in
/-- An accepted prover, without the extractor winning, triggers one of the bad events. -/
theorem bad_of_accept (acc : P → Prop) (G : P → D) (ha : Accept B v s acc G)
    (hx : ¬ ExtWins B v acc G) :
    (∃ ij ∈ Finset.range B.q₁ ×ˢ Finset.range B.q₁, Coll B v G ij.1 ij.2) ∨
      (∃ k ∈ Finset.range B.q₂, Hit₂ B v s G k) ∨ HitOpen B v s G := by
  obtain ⟨hacc, hval⟩ := ha
  by_cases hA : ∃ m, m < B.q₁ ∧ qry₁ B v G m = opn B v s G
  · -- the opened point was queried in the first phase
    left
    let m := Nat.find hA
    have hm : m < B.q₁ ∧ qry₁ B v G m = opn B v s G := Nat.find_spec hA
    have hmin : ∀ l < m, qry₁ B v G l ≠ qry₁ B v G m := fun l hl e ↦
      Nat.find_min hA hl ⟨by omega, e.trans hm.2⟩
    have hF : ∃ f, f < B.q₁ ∧ G (qry₁ B v G f) = com B v G :=
      ⟨m, hm.1, by rw [hm.2]; exact hval⟩
    let f := Nat.find hF
    have hf : f < B.q₁ ∧ G (qry₁ B v G f) = com B v G := Nat.find_spec hF
    have hfmin : ∀ l < f, G (qry₁ B v G l) ≠ com B v G := fun l hl e ↦
      Nat.find_min hF hl ⟨by omega, e⟩
    have hfm : f ≤ m := Nat.find_min' hF ⟨hm.1, by rw [hm.2]; exact hval⟩
    have hne : qry₁ B v G f ≠ qry₁ B v G m := by
      intro e
      exact hx ⟨f, hf.1, hf.2, hfmin, by rw [e, hm.2]; exact hacc⟩
    have hlt : f < m := lt_of_le_of_ne hfm fun e ↦ hne (by rw [e])
    refine ⟨(f, m), by simp [hf.1, hm.1], hmin, hne, hlt, ?_⟩
    rw [hf.2, hm.2, hval]
  · simp only [not_exists, not_and] at hA
    right
    by_cases hB : ∃ k, k < B.q₂ ∧ qry₂ B v s G k = opn B v s G
    · left
      let k := Nat.find hB
      have hk : k < B.q₂ ∧ qry₂ B v s G k = opn B v s G := Nat.find_spec hB
      refine ⟨k, Finset.mem_range.2 hk.1, ⟨fun l hl ↦ hk.2 ▸ hA l hl, fun l hl e ↦
        Nat.find_min hB hl ⟨by omega, e.trans hk.2⟩⟩, by rw [hk.2]; exact hval⟩
    · simp only [not_exists, not_and] at hB
      exact Or.inr ⟨⟨hA, hB⟩, hval⟩

open Classical in
/-- **Binding.** Summed over all oracles, an accepted prover without a winning extractor
occurs for at most `(q₁² + q₂ + 1) |D|^{|P|} / |D|` oracles. -/
theorem card_accept_le (acc : P → Prop) :
    (Finset.univ.filter fun G : P → D ↦ Accept B v s acc G ∧ ¬ ExtWins B v acc G).card *
        Fintype.card D ≤
      (B.q₁ * B.q₁ + B.q₂ + 1) * Fintype.card (P → D) := by
  set N := Fintype.card (P → D)
  have hsub : (Finset.univ.filter fun G : P → D ↦ Accept B v s acc G ∧ ¬ ExtWins B v acc G) ⊆
      ((Finset.range B.q₁ ×ˢ Finset.range B.q₁).biUnion fun ij ↦
          Finset.univ.filter fun G : P → D ↦ Coll B v G ij.1 ij.2) ∪
        ((Finset.range B.q₂).biUnion fun k ↦ Finset.univ.filter fun G : P → D ↦ Hit₂ B v s G k) ∪
        Finset.univ.filter fun G : P → D ↦ HitOpen B v s G := by
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
    rcases bad_of_accept B v s acc G hG.1 hG.2 with ⟨ij, hij, h⟩ | ⟨k, hk, h⟩ | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.2 ⟨ij, hij, by simpa using h⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨k, hk, by simpa using h⟩))
    · exact Finset.mem_union_right _ (by simpa using h)
  have h1 : ((Finset.range B.q₁ ×ˢ Finset.range B.q₁).biUnion fun ij ↦
      Finset.univ.filter fun G : P → D ↦ Coll B v G ij.1 ij.2).card * Fintype.card D ≤
        B.q₁ * B.q₁ * N := by
    calc _ ≤ (∑ ij ∈ Finset.range B.q₁ ×ˢ Finset.range B.q₁,
          (Finset.univ.filter fun G : P → D ↦ Coll B v G ij.1 ij.2).card) * Fintype.card D :=
          Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ ij ∈ Finset.range B.q₁ ×ˢ Finset.range B.q₁,
          (Finset.univ.filter fun G : P → D ↦ Coll B v G ij.1 ij.2).card * Fintype.card D :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ _ij ∈ Finset.range B.q₁ ×ˢ Finset.range B.q₁, N :=
          Finset.sum_le_sum fun ij _ ↦ card_coll_le B v ij.1 ij.2
      _ = B.q₁ * B.q₁ * N := by simp
  have h2 : ((Finset.range B.q₂).biUnion fun k ↦
      Finset.univ.filter fun G : P → D ↦ Hit₂ B v s G k).card * Fintype.card D ≤ B.q₂ * N := by
    calc _ ≤ (∑ k ∈ Finset.range B.q₂,
          (Finset.univ.filter fun G : P → D ↦ Hit₂ B v s G k).card) * Fintype.card D :=
          Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ k ∈ Finset.range B.q₂,
          (Finset.univ.filter fun G : P → D ↦ Hit₂ B v s G k).card * Fintype.card D :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ _k ∈ Finset.range B.q₂, N :=
          Finset.sum_le_sum fun k _ ↦ card_hit₂_le B v s k
      _ = B.q₂ * N := by simp
  have h3 := card_hitOpen_le B v s
  calc _ ≤ (((Finset.range B.q₁ ×ˢ Finset.range B.q₁).biUnion fun ij ↦
          Finset.univ.filter fun G : P → D ↦ Coll B v G ij.1 ij.2).card +
        ((Finset.range B.q₂).biUnion fun k ↦
          Finset.univ.filter fun G : P → D ↦ Hit₂ B v s G k).card +
        (Finset.univ.filter fun G : P → D ↦ HitOpen B v s G).card) * Fintype.card D :=
        Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans
          ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)))
    _ ≤ _ := by rw [Nat.add_mul, Nat.add_mul]; nlinarith

open Classical in
/-- **Soundness with a hash commitment.** The probability (over a uniform oracle) that the
verifier accepts is at most the probability that the extractor wins, plus
`(q₁² + q₂ + 1) / |D|`. -/
theorem prob_accept_le [Nonempty D] (acc : P → Prop) :
    ((Finset.univ.filter fun G : P → D ↦ Accept B v s acc G).card : ℝ) /
        Fintype.card (P → D) ≤
      ((Finset.univ.filter fun G : P → D ↦ ExtWins B v acc G).card : ℝ) /
          Fintype.card (P → D) +
        ((B.q₁ * B.q₁ + B.q₂ + 1 : ℕ) : ℝ) / Fintype.card D := by
  have hN : (0 : ℝ) < Fintype.card (P → D) := by exact_mod_cast Fintype.card_pos
  have hD : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hsplit : (Finset.univ.filter fun G : P → D ↦ Accept B v s acc G).card ≤
      (Finset.univ.filter fun G : P → D ↦ ExtWins B v acc G).card +
        (Finset.univ.filter fun G : P → D ↦ Accept B v s acc G ∧ ¬ ExtWins B v acc G).card := by
    refine (Finset.card_le_card fun G hG ↦ ?_).trans (Finset.card_union_le _ _)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hG ⊢
    by_cases h : ExtWins B v acc G
    · exact Or.inl h
    · exact Or.inr ⟨hG, h⟩
  have hb := card_accept_le B v s acc
  have hb' : ((Finset.univ.filter fun G : P → D ↦
      Accept B v s acc G ∧ ¬ ExtWins B v acc G).card : ℝ) ≤
        ((B.q₁ * B.q₁ + B.q₂ + 1 : ℕ) : ℝ) * Fintype.card (P → D) / Fintype.card D := by
    rw [le_div_iff₀ hD]; exact_mod_cast hb
  rw [div_add_div _ _ hN.ne' hD.ne', le_div_iff₀ (mul_pos hN hD), div_mul_eq_mul_div,
    div_le_iff₀ hN]
  have hs : ((Finset.univ.filter fun G : P → D ↦ Accept B v s acc G).card : ℝ) ≤
      (Finset.univ.filter fun G : P → D ↦ ExtWins B v acc G).card +
        (Finset.univ.filter fun G : P → D ↦ Accept B v s acc G ∧ ¬ ExtWins B v acc G).card := by
    exact_mod_cast hsplit
  have := mul_le_mul_of_nonneg_right hs (mul_nonneg hN.le hD.le)
  rw [le_div_iff₀ hD] at hb'
  nlinarith

end Card

end GcZk.Bind
