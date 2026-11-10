/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.AdaptiveFresh

/-!
# Adaptive authenticity: the bound

## Main results

* `GcZk.Adaptive.card_bad_le`: `|V| · Σ_{Δ ≠ 0} #bad ≤ q (|V| + (|V| - 1)) |Rand|`. With `Δ`
  uniform on `V \ {0}` and the rest uniform, a query bad for the final input occurs with
  probability at most `q (1 / (|V| - 1) + 1 / |V|)`.
* `GcZk.Adaptive.card_win_le`: `|V| · Σ_{Δ ≠ 0} #win ≤ (|V| + q (|V| + (|V| - 1))) |Rand|`.
* `GcZk.Adaptive.adaptive_authenticity`: an adversary taking `q` actions wins the adaptive
  authenticity game with probability at most `(q + 1) / (|V| - 1) + q / |V|`.

## Proof

For each `k < q`, the randomness whose first bad step is `k` injects, by the map of the game
truncated to `k` steps, into the simulated randomness where the query at step `k` hits the active
label plus `Δ` (at most one `Δ` per simulated randomness) or a fresh active label (at most a
fraction `1 / |V|`, `GcZk.Adaptive.card_freshHit_le`).
-/

namespace GcZk.Adaptive

open Auth RO Lin

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]
variable (C : Circuit) (m q : ℕ) (A : AAdv V)

/-- Step `k` is the first bad step. -/
def FirstBad (Δ : V) (p : Rand V m C.length) (k : ℕ) : Prop :=
  BadStep C m A Δ p k ∧ ∀ j < k, ¬ BadStep C m A Δ p j

/-- The query at step `k` of the simulated game hits the active label of its selector plus `Δ`. -/
def HitDelta (Δ : V) (σ : Rand V m C.length) (k : ℕ) : Prop :=
  ∃ i y s z o, actK C m A k σ = .query i y ∧ C[i]? = some (.mux s z o) ∧
    y = simX C m A σ k i s + Δ

open Classical in
theorem card_bad_le_first (Δ : V) :
    (Finset.univ.filter fun p : Rand V m C.length ↦ RealBad C m q A Δ p).card ≤
      ∑ k ∈ Finset.range q,
        (Finset.univ.filter fun p : Rand V m C.length ↦ FirstBad C m A Δ p k).card := by
  refine le_trans (Finset.card_le_card fun p hp ↦ ?_) Finset.card_biUnion_le
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨k, hk, hb⟩ := exists_badStep C m A Δ p hp
  have hex : ∃ k, BadStep C m A Δ p k := ⟨k, hb⟩
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨Nat.find hex, lt_of_le_of_lt (Nat.find_min' hex hb) hk, Nat.find_spec hex,
    fun j hj ↦ Nat.find_min hex hj⟩

open Classical in
theorem card_first_le (Δ : V) (hΔ : Δ ≠ 0) (k : ℕ) :
    (Finset.univ.filter fun p : Rand V m C.length ↦ FirstBad C m A Δ p k).card ≤
      (Finset.univ.filter fun σ : Rand V m C.length ↦ HitDelta C m A Δ σ k).card +
        (Finset.univ.filter fun σ : Rand V m C.length ↦ FreshHit C m A k σ).card := by
  refine le_trans ?_ (Finset.card_union_le _ _)
  refine Finset.card_le_card_of_injOn (toAdSim C m k A Δ) (fun p hp ↦ ?_)
    ((toAdSim_injOn C m k A Δ hΔ).mono fun p hp ↦ ?_)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp
    obtain ⟨i, y, s, z, o, ha, hC, hy⟩ := simBadAt_toAdSim C m A Δ hΔ p hp.1 hp.2
    simp only [Finset.coe_union, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_union,
      Set.mem_ofPred_eq]
    rcases hy with hy | ⟨hunk, hy, hf⟩
    · exact Or.inl ⟨i, y, s, z, o, ha, hC, hy⟩
    · exact Or.inr ⟨i, y, s, z, o, ha, hC, hunk, hy, hf⟩
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    exact not_realBad_of_first C m A Δ p hp.2

open Classical in
theorem sum_hitDelta_le (k : ℕ) :
    ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun σ : Rand V m C.length ↦ HitDelta C m A Δ σ k).card ≤
      Fintype.card (Rand V m C.length) := by
  calc _ ≤ ∑ Δ : V,
        (Finset.univ.filter fun σ : Rand V m C.length ↦ HitDelta C m A Δ σ k).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ∑ σ : Rand V m C.length,
        (Finset.univ.filter fun Δ : V ↦ HitDelta C m A Δ σ k).card := by
        simp only [Finset.card_filter]; exact Finset.sum_comm
    _ ≤ ∑ _σ : Rand V m C.length, 1 := by
        refine Finset.sum_le_sum fun σ _ ↦ Finset.card_le_one.2 fun a ha b hb ↦ ?_
        obtain ⟨i, y, s, z, o, h1, h2, h3⟩ := (Finset.mem_filter.1 ha).2
        obtain ⟨i', y', s', z', o', h1', h2', h3'⟩ := (Finset.mem_filter.1 hb).2
        rw [h1] at h1'; cases h1'
        rw [h2] at h2'; cases h2'
        exact add_left_cancel (h3.symm.trans h3')
    _ = Fintype.card (Rand V m C.length) := by simp

open Classical in
/-- **Bad queries.** `|V| · Σ_{Δ ≠ 0} #bad ≤ q (|V| + (|V| - 1)) |Rand|`: with `Δ` uniform on
`V \ {0}` and the rest uniform, a query bad for the final input occurs with probability at most
`q (1 / (|V| - 1) + 1 / |V|)`. -/
theorem card_bad_le :
    Fintype.card V * ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun p : Rand V m C.length ↦ RealBad C m q A Δ p).card ≤
      q * ((Fintype.card V + (Fintype.card V - 1)) * Fintype.card (Rand V m C.length)) := by
  set N := Fintype.card (Rand V m C.length)
  set F := fun k ↦ (Finset.univ.filter fun σ : Rand V m C.length ↦ FreshHit C m A k σ).card
  have hF : ∀ k, F k * Fintype.card V ≤ N := fun k ↦ card_freshHit_le C m A k
  have hcard : (Finset.univ.filter (· ≠ (0 : V))).card = Fintype.card V - 1 := by
    rw [Finset.filter_ne' Finset.univ (0 : V), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
  have step : ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun p : Rand V m C.length ↦ RealBad C m q A Δ p).card ≤
      ∑ k ∈ Finset.range q, (N + (Fintype.card V - 1) * F k) := by
    calc _ ≤ ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), ∑ k ∈ Finset.range q,
          ((Finset.univ.filter fun σ : Rand V m C.length ↦ HitDelta C m A Δ σ k).card + F k) := by
          refine Finset.sum_le_sum fun Δ hΔ ↦ ?_
          have hΔ : Δ ≠ 0 := by simpa using hΔ
          exact (card_bad_le_first C m q A Δ).trans
            (Finset.sum_le_sum fun k _ ↦ card_first_le C m A Δ hΔ k)
      _ = ∑ k ∈ Finset.range q, (∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
          (Finset.univ.filter fun σ : Rand V m C.length ↦ HitDelta C m A Δ σ k).card +
            (Fintype.card V - 1) * F k) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [Finset.sum_add_distrib, Finset.sum_const, hcard, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun k _ ↦ Nat.add_le_add_right (sum_hitDelta_le C m A k) _
  calc Fintype.card V * _ ≤ Fintype.card V * ∑ k ∈ Finset.range q,
        (N + (Fintype.card V - 1) * F k) := Nat.mul_le_mul_left _ step
    _ = ∑ k ∈ Finset.range q, (Fintype.card V * N + (Fintype.card V - 1) * (F k *
        Fintype.card V)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring
    _ ≤ ∑ _k ∈ Finset.range q, (Fintype.card V * N + (Fintype.card V - 1) * N) :=
        Finset.sum_le_sum fun k _ ↦ Nat.add_le_add_left (Nat.mul_le_mul_left _ (hF k)) _
    _ = q * ((Fintype.card V + (Fintype.card V - 1)) * N) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

variable (out : ℕ)

open Classical in
/-- `|V| · Σ_{Δ ≠ 0} #win ≤ (|V| + q (|V| + (|V| - 1))) |Rand|`. -/
theorem card_win_le :
    Fintype.card V * ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun p : Rand V m C.length ↦ RealWin C m out q A Δ p).card ≤
      Fintype.card V * Fintype.card (Rand V m C.length) +
        q * ((Fintype.card V + (Fintype.card V - 1)) * Fintype.card (Rand V m C.length)) := by
  have h1 := Nat.mul_le_mul_left (Fintype.card V) (win_le C m out q A)
  rw [Nat.mul_add] at h1
  exact h1.trans (Nat.add_le_add_left (card_bad_le C m q A) _)

open Classical in
/-- **Adaptive authenticity.** With `Δ` uniform on `V \ {0}` and the zero-labels and the hash
uniform, an adversary taking `q` actions (queries to the hash and label requests) outputs the
inactive output label for the input it requested with probability at most
`(q + 1) / (|V| - 1) + q / |V|`. -/
theorem adaptive_authenticity :
    ((∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun p : Rand V m C.length ↦ RealWin C m out q A Δ p).card : ℕ) : ℝ) /
      ((Fintype.card V - 1) * Fintype.card (Rand V m C.length)) ≤
      (q + 1) / (Fintype.card V - 1) + q / Fintype.card V := by
  have key := card_win_le C m q A out
  have hn1 : 1 ≤ Fintype.card V := Fintype.card_pos
  have hN : 0 < Fintype.card (Rand V m C.length) := Fintype.card_pos
  generalize (∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun p : Rand V m C.length ↦ RealWin C m out q A Δ p).card) = W at key ⊢
  generalize Fintype.card V = n at key hn1 ⊢
  generalize Fintype.card (Rand V m C.length) = N at key hN ⊢
  rcases Nat.eq_or_lt_of_le hn1 with h | h
  · -- `V` is trivial: the left side is `0`
    subst h
    simp only [Nat.cast_one, sub_self, zero_mul, div_zero]
    positivity
  · have hn : (1 : ℝ) < n := by exact_mod_cast h
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hkey : (n : ℝ) * W ≤ n * N + q * ((n + (n - 1)) * N) := by
      have := (Nat.cast_le (α := ℝ)).2 key
      push_cast [Nat.cast_sub hn1] at this
      linarith
    rw [div_le_iff₀ (mul_pos (by linarith) hN')]
    have e : ((q + 1) / (n - 1) + q / n) * ((n - 1) * N) =
        ((n : ℝ) * N + q * ((n + (n - 1)) * N)) / n := by
      field_simp
      ring
    rw [e, le_div_iff₀ (by linarith)]
    linarith

end GcZk.Adaptive
