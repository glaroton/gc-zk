/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.PVWZK

/-!
# The two modes of the PVW common string and DDH

We compare the setups of [PVW08, Sect. 5.3] (2019 revision) with the DDH tuples of
[PVW08, Sect. 5.1], in additive notation, in a group `Gp` of prime order `q > 2`:
* messy mode: `(g₀, x₀ g₀, g₁, x₁ g₁)` with `g₀, g₁ ≠ 0` and `x₀ ≠ x₁` nonzero;
* decryption mode: `(g₀, x g₀, y g₀, x y g₀)` with `g₀ ≠ 0` and `x, y` nonzero;
* DDH tuple: `(g, h, a g, a h)` with `g, h ≠ 0` and `a` uniform;
* random tuple: `(g, h, a g, b h)` with `g, h ≠ 0` and `a ≠ b` uniform.

Writing `g₁ = a g₀`, a messy string is a random tuple with `a, b ≠ 0`, and a decryption-mode
string is a DDH tuple with `a ≠ 0` (`sum_messy`, `sum_dec`); these are bijections of the
parameters. Removing the excluded values costs `2 / q` and `1 / q` (`abs_avg_sub_le`). So for any
function `F` of the common string with values in `[0, 1]`, the difference of its averages over the
two modes is at most its DDH advantage plus `3 / q` (`abs_modes_le`). This is the
indistinguishability of modes in [PVW08, Theorem 5.2], as an explicit reduction: the DDH
distinguisher is `F` itself, applied to the tuple read as a common string.

## Main result

* `GcZk.PVW.zk_pvw_ddh`: zero knowledge with the PVW OT in messy mode. Averaged over the messy
  setup, the real execution and the simulator differ by at most
  `Q / |R| + Adv_DDH(p_w) + Adv_DDH(p_0) + 6 / q`, where `p_x` is the distinguisher of
  `GcZk.PVW.pHyb`.

Lean has no notion of efficient computation; that `p_x` is efficient when the verifier is, is
argued in the blueprint.
-/

namespace GcZk.PVW

open Finset

variable {q : ℕ} {Gp : Type*} [AddCommGroup Gp] [Module (ZMod q) Gp]

/-- The common string with the given four elements. -/
def mk (g₀ h₀ g₁ h₁ : Gp) : Crs Gp := ⟨fun b ↦ cond b g₁ g₀, fun b ↦ cond b h₁ h₀⟩

/-- The average of `f` over a finite set. -/
noncomputable def avg {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ := (∑ p ∈ s, f p) / s.card

/-- **Averages over a subset.** If `0 ≤ f ≤ 1`, the averages of `f` over `T ⊆ T'` differ by at
most the proportion of `T'` outside `T`. -/
theorem abs_avg_sub_le {α : Type*} {T T' : Finset α} (hT : T ⊆ T') (hne : T.Nonempty)
    (f : α → ℝ) (h0 : ∀ p ∈ T', 0 ≤ f p) (h1 : ∀ p ∈ T', f p ≤ 1) :
    |avg T f - avg T' f| ≤ ((T'.card : ℝ) - T.card) / T'.card := by
  classical
  have pt : (0 : ℝ) < T.card := by exact_mod_cast hne.card_pos
  have pt' : (0 : ℝ) < T'.card := by exact_mod_cast (hne.mono hT).card_pos
  have hc : (T.card : ℝ) ≤ T'.card := by exact_mod_cast card_le_card hT
  have hS : ∑ p ∈ T', f p = ∑ p ∈ T, f p + ∑ p ∈ T' \ T, f p := by
    rw [← sum_sdiff hT, add_comm]
  have S0 : 0 ≤ ∑ p ∈ T, f p := sum_nonneg fun p hp ↦ h0 p (hT hp)
  have S1 : ∑ p ∈ T, f p ≤ T.card := by
    calc ∑ p ∈ T, f p ≤ ∑ _p ∈ T, (1 : ℝ) := sum_le_sum fun p hp ↦ h1 p (hT hp)
      _ = T.card := by simp
  have e0 : 0 ≤ ∑ p ∈ T' \ T, f p := sum_nonneg fun p hp ↦ h0 p (mem_sdiff.1 hp).1
  have e1 : ∑ p ∈ T' \ T, f p ≤ T'.card - T.card := by
    calc ∑ p ∈ T' \ T, f p ≤ ∑ _p ∈ T' \ T, (1 : ℝ) :=
          sum_le_sum fun p hp ↦ h1 p (mem_sdiff.1 hp).1
      _ = T'.card - T.card := by
        rw [sum_const, card_sdiff_of_subset hT, nsmul_eq_mul, mul_one,
          Nat.cast_sub (card_le_card hT)]
  simp only [avg, hS]
  generalize ∑ p ∈ T, f p = S at S0 S1 ⊢
  generalize ∑ p ∈ T' \ T, f p = e at e0 e1 ⊢
  generalize (T.card : ℝ) = t at pt hc S1 e1 ⊢
  generalize (T'.card : ℝ) = t' at pt' hc e1 ⊢
  have key : S / t - (S + e) / t' = S * (t' - t) / (t * t') - e / t' := by
    field_simp; ring
  have b1 : 0 ≤ S * (t' - t) / (t * t') :=
    div_nonneg (mul_nonneg S0 (sub_nonneg.2 hc)) (mul_pos pt pt').le
  have b2 : S * (t' - t) / (t * t') ≤ (t' - t) / t' := by
    rw [div_le_div_iff₀ (mul_pos pt pt') pt']
    have := mul_nonneg (mul_nonneg (sub_nonneg.2 hc) pt'.le) (sub_nonneg.2 S1)
    nlinarith
  have b3 : 0 ≤ e / t' := div_nonneg e0 pt'.le
  have b4 : e / t' ≤ (t' - t) / t' := div_le_div_of_nonneg_right e1 pt'.le
  rw [key, abs_le]
  constructor <;> linarith

section Prime

variable [Fact q.Prime] [Fintype Gp] [DecidableEq Gp] (hcard : Fintype.card Gp = q)

/-- The nonzero elements of the group. -/
def nz : Finset Gp := univ.filter (· ≠ 0)

/-- The nonzero exponents. -/
def nzq : Finset (ZMod q) := univ.filter (· ≠ 0)

omit [DecidableEq Gp] in
include hcard in
theorem smul_bijective {g : Gp} (hg : g ≠ 0) : Function.Bijective fun r : ZMod q ↦ r • g := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun r s h ↦ ?_, by simp [hcard]⟩
  have : (r - s) • g = 0 := by simp only at h; rw [sub_smul, h, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hg)

open Classical in
/-- The discrete logarithm in base `g` (`0` if `g = 0`). -/
noncomputable def lg (g x : Gp) : ZMod q :=
  if hg : g ≠ 0 then (Equiv.ofBijective _ (smul_bijective hcard hg)).symm x else 0

theorem lg_smul {g : Gp} (hg : g ≠ 0) (r : ZMod q) : lg hcard g (r • g) = r := by
  simp only [lg, hg, ne_eq, not_false_eq_true, dite_true]
  exact (Equiv.ofBijective _ (smul_bijective hcard hg)).symm_apply_apply r

theorem smul_lg {g : Gp} (hg : g ≠ 0) (x : Gp) : lg hcard g x • g = x := by
  simp only [lg, hg, ne_eq, not_false_eq_true, dite_true]
  exact (Equiv.ofBijective _ (smul_bijective hcard hg)).apply_symm_apply x

theorem lg_ne_zero {g x : Gp} (hg : g ≠ 0) (hx : x ≠ 0) : lg hcard g x ≠ 0 := by
  intro h; apply hx; rw [← smul_lg hcard hg x, h, zero_smul]

omit [Fact q.Prime] [Fintype Gp] [DecidableEq Gp] in
theorem smul_ne_zero' [Fact q.Prime] {r : ZMod q} {g : Gp} (hr : r ≠ 0) (hg : g ≠ 0) :
    r • g ≠ 0 := by
  rw [Ne, smul_eq_zero, not_or]; exact ⟨hr, hg⟩

omit [Module (ZMod q) Gp] [Fact q.Prime] in
include hcard in
theorem card_nz : (nz : Finset Gp).card = q - 1 := by
  rw [nz, filter_ne' univ (0 : Gp), card_erase_of_mem (mem_univ _), card_univ, hcard]

omit [Fintype Gp] [DecidableEq Gp] in
theorem card_nzq : (nzq : Finset (ZMod q)).card = q - 1 := by
  rw [nzq, filter_ne' univ (0 : ZMod q), card_erase_of_mem (mem_univ _), card_univ, ZMod.card]

/-! ### The four distributions -/

/-- Parameters of the messy setup `(g₀, g₁, (x₀, x₁))`, and of the random tuples restricted to
`a, b ≠ 0`. -/
def parM : Finset (Gp × Gp × ZMod q × ZMod q) := nz ×ˢ nz ×ˢ (nzq : Finset (ZMod q)).offDiag

/-- Parameters `(g, h, (a, b))` of the random tuples. -/
def parRa : Finset (Gp × Gp × ZMod q × ZMod q) := nz ×ˢ nz ×ˢ (univ : Finset (ZMod q)).offDiag

/-- Parameters of the decryption setup `(g₀, y, x)`. -/
def parD : Finset (Gp × ZMod q × ZMod q) := nz ×ˢ nzq ×ˢ nzq

/-- Parameters `(g, h, a)` of the DDH tuples restricted to `a ≠ 0`. -/
def parT : Finset (Gp × Gp × ZMod q) := nz ×ˢ nz ×ˢ nzq

/-- Parameters `(g, h, a)` of the DDH tuples. -/
def parRe : Finset (Gp × Gp × ZMod q) := nz ×ˢ nz ×ˢ univ

/-- The messy common string. -/
def crsM (p : Gp × Gp × ZMod q × ZMod q) : Crs Gp :=
  mk p.1 (p.2.2.1 • p.1) p.2.1 (p.2.2.2 • p.2.1)

/-- The random tuple `(g, h, a g, b h)`. -/
def tupRa (p : Gp × Gp × ZMod q × ZMod q) : Crs Gp :=
  mk p.1 p.2.1 (p.2.2.1 • p.1) (p.2.2.2 • p.2.1)

/-- The decryption-mode common string. -/
def crsD (p : Gp × ZMod q × ZMod q) : Crs Gp :=
  mk p.1 (p.2.2 • p.1) (p.2.1 • p.1) (p.2.2 • p.2.1 • p.1)

/-- The DDH tuple `(g, h, a g, a h)`. -/
def tupRe (p : Gp × Gp × ZMod q) : Crs Gp :=
  mk p.1 p.2.1 (p.2.2 • p.1) (p.2.2 • p.2.1)

theorem crsD_dec (p : Gp × ZMod q × ZMod q) (hp : p ∈ (parD : Finset _)) : (crsD p).Dec q := by
  simp only [parD, nzq, mem_product, mem_filter, mem_univ, true_and] at hp
  refine ⟨p.2.2, p.2.1, hp.2.1, rfl, fun b ↦ ?_⟩
  cases b <;> rfl

include hcard in
/-- **Messy strings are random tuples with `a, b ≠ 0`.** -/
theorem sum_messy (F : Crs Gp → ℝ) :
    ∑ p ∈ (parM : Finset (Gp × Gp × ZMod q × ZMod q)), F (crsM p) =
      ∑ p ∈ (parM : Finset (Gp × Gp × ZMod q × ZMod q)), F (tupRa p) := by
  refine sum_nbij'
    (fun p ↦ (p.1, p.2.2.1 • p.1, lg hcard p.1 p.2.1, p.2.2.2 * lg hcard p.1 p.2.1 / p.2.2.1))
    (fun p ↦ (p.1, p.2.2.1 • p.1, lg hcard p.1 p.2.1, p.2.2.2 * lg hcard p.1 p.2.1 / p.2.2.1))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨g, g', x, x'⟩ hp
    simp only [parM, nz, nzq, mem_product, mem_filter, mem_univ, true_and, mem_offDiag] at hp ⊢
    obtain ⟨hg, hg', hx, hx', hxx⟩ := hp
    refine ⟨hg, smul_ne_zero' hx hg, lg_ne_zero hcard hg hg', ?_, ?_⟩
    · exact div_ne_zero (mul_ne_zero hx' (lg_ne_zero hcard hg hg')) hx
    · intro h
      apply hxx
      rw [eq_div_iff hx, mul_comm] at h
      exact (mul_right_cancel₀ (lg_ne_zero hcard hg hg') (by rw [h])).symm
  · rintro ⟨g, h, a, b⟩ hp
    simp only [parM, nz, nzq, mem_product, mem_filter, mem_univ, true_and, mem_offDiag] at hp ⊢
    obtain ⟨hg, hh, ha, hb, hab⟩ := hp
    refine ⟨hg, smul_ne_zero' ha hg, lg_ne_zero hcard hg hh, ?_, ?_⟩
    · exact div_ne_zero (mul_ne_zero hb (lg_ne_zero hcard hg hh)) ha
    · intro e
      apply hab
      rw [eq_div_iff ha, mul_comm] at e
      exact (mul_right_cancel₀ (lg_ne_zero hcard hg hh) (by rw [e])).symm
  · rintro ⟨g, g', x, x'⟩ hp
    simp only [parM, nz, nzq, mem_product, mem_filter, mem_univ, true_and, mem_offDiag] at hp
    obtain ⟨hg, hg', hx, hx', -⟩ := hp
    have hl := lg_ne_zero hcard hg hg'
    simp only [Prod.mk.injEq, lg_smul hcard hg, smul_lg hcard hg, true_and]
    field_simp
  · rintro ⟨g, h, a, b⟩ hp
    simp only [parM, nz, nzq, mem_product, mem_filter, mem_univ, true_and, mem_offDiag] at hp
    obtain ⟨hg, hh, ha, hb, -⟩ := hp
    have hl := lg_ne_zero hcard hg hh
    simp only [Prod.mk.injEq, lg_smul hcard hg, smul_lg hcard hg, true_and]
    field_simp
  · rintro ⟨g, g', x, x'⟩ hp
    simp only [parM, nz, nzq, mem_product, mem_filter, mem_univ, true_and, mem_offDiag] at hp
    obtain ⟨hg, hg', hx, hx', -⟩ := hp
    have e : (x' * lg hcard g g' / x) • (x • g) = x' • g' := by
      rw [smul_smul, div_mul_cancel₀ _ hx, mul_smul, smul_lg hcard hg]
    simp only [crsM, tupRa, mk, smul_lg hcard hg, e]

include hcard in
/-- **Decryption-mode strings are DDH tuples with `a ≠ 0`.** -/
theorem sum_dec (F : Crs Gp → ℝ) :
    ∑ p ∈ (parD : Finset (Gp × ZMod q × ZMod q)), F (crsD p) =
      ∑ p ∈ (parT : Finset (Gp × Gp × ZMod q)), F (tupRe p) := by
  refine sum_nbij' (fun p ↦ (p.1, p.2.2 • p.1, p.2.1)) (fun p ↦ (p.1, p.2.2, lg hcard p.1 p.2.1))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨g, y, x⟩ hp
    simp only [parD, parT, nz, nzq, mem_product, mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, smul_ne_zero' hp.2.2 hp.1, hp.2.1⟩
  · rintro ⟨g, h, a⟩ hp
    simp only [parD, parT, nz, nzq, mem_product, mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, hp.2.2, lg_ne_zero hcard hp.1 hp.2.1⟩
  · rintro ⟨g, y, x⟩ hp
    simp only [parD, nz, mem_product, mem_filter, mem_univ, true_and] at hp
    simp [lg_smul hcard hp.1]
  · rintro ⟨g, h, a⟩ hp
    simp only [parT, nz, mem_product, mem_filter, mem_univ, true_and] at hp
    simp [smul_lg hcard hp.1]
  · rintro ⟨g, y, x⟩ -
    simp only [crsD, tupRe, smul_comm y x]

/-! ### The cost of the excluded values -/

theorem cast_q_sub_one : (((q - 1 : ℕ)) : ℝ) = q - 1 := by
  have : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
  push_cast [Nat.cast_sub this]; ring

include hcard in
omit [Module (ZMod q) Gp] in
theorem ratio_messy (hq : 2 < q) :
    (((parRa : Finset (Gp × Gp × ZMod q × ZMod q)).card : ℝ) -
        (parM : Finset (Gp × Gp × ZMod q × ZMod q)).card) /
      (parRa : Finset (Gp × Gp × ZMod q × ZMod q)).card = 2 / q := by
  have h1 : ((((nzq : Finset (ZMod q)).offDiag).card : ℕ) : ℝ) = (q - 1) * (q - 1) - (q - 1) := by
    rw [offDiag_card, card_nzq, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul, cast_q_sub_one]
  have h2 : ((((univ : Finset (ZMod q)).offDiag).card : ℕ) : ℝ) = q * q - q := by
    rw [offDiag_card, card_univ, ZMod.card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
  simp only [parRa, parM, card_product, Nat.cast_mul, card_nz hcard, cast_q_sub_one, h1, h2]
  have : (2 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℝ) - 1 ≠ 0 := by linarith
  have hq1 : (q : ℝ) ≠ 0 := by linarith
  field_simp
  ring

include hcard in
omit [Module (ZMod q) Gp] in
theorem ratio_dec :
    (((parRe : Finset (Gp × Gp × ZMod q)).card : ℝ) - (parT : Finset (Gp × Gp × ZMod q)).card) /
      (parRe : Finset (Gp × Gp × ZMod q)).card = 1 / q := by
  simp only [parRe, parT, card_product, Nat.cast_mul, card_nz hcard, card_nzq, card_univ,
    ZMod.card, cast_q_sub_one]
  have : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have hq0 : (q : ℝ) - 1 ≠ 0 := by linarith
  have hq1 : (q : ℝ) ≠ 0 := by linarith
  field_simp
  ring

/-- The DDH advantage of a function of the common string: the difference of its averages over
DDH tuples and random tuples, read as common strings. -/
noncomputable def advDDH (F : Crs Gp → ℝ) : ℝ :=
  |avg (parRe : Finset (Gp × Gp × ZMod q)) (fun p ↦ F (tupRe p)) -
    avg (parRa : Finset (Gp × Gp × ZMod q × ZMod q)) (fun p ↦ F (tupRa p))|

include hcard in
/-- **Indistinguishability of the modes from DDH.** For `F` with values in `[0, 1]`, the averages
over the messy and the decryption-mode setups differ by at most the DDH advantage of `F` plus
`3 / q`. -/
theorem abs_modes_le (hq : 2 < q) (F : Crs Gp → ℝ) (h0 : ∀ c, 0 ≤ F c) (h1 : ∀ c, F c ≤ 1) :
    |avg (parM : Finset (Gp × Gp × ZMod q × ZMod q)) (fun p ↦ F (crsM p)) -
        avg (parD : Finset (Gp × ZMod q × ZMod q)) (fun p ↦ F (crsD p))| ≤
      advDDH (q := q) F + 3 / q := by
  have hne1 : (nzq : Finset (ZMod q)).Nonempty := ⟨1, by simp [nzq]⟩
  have hnz : (nz : Finset Gp).Nonempty := by
    rw [← card_pos, card_nz hcard]; omega
  have hoff : (nzq : Finset (ZMod q)).offDiag.Nonempty := by
    rw [← card_pos, offDiag_card, card_nzq]
    have : 2 ≤ q - 1 := by omega
    have : 2 * (q - 1) ≤ (q - 1) * (q - 1) := Nat.mul_le_mul_right _ this
    omega
  have hM : (parM : Finset (Gp × Gp × ZMod q × ZMod q)).Nonempty :=
    hnz.product (hnz.product hoff)
  have hT : (parT : Finset (Gp × Gp × ZMod q)).Nonempty := hnz.product (hnz.product hne1)
  have eM : avg (parM : Finset (Gp × Gp × ZMod q × ZMod q)) (fun p ↦ F (crsM p)) =
      avg (parM : Finset (Gp × Gp × ZMod q × ZMod q)) (fun p ↦ F (tupRa p)) := by
    rw [avg, avg, sum_messy hcard]
  have eD : avg (parD : Finset (Gp × ZMod q × ZMod q)) (fun p ↦ F (crsD p)) =
      avg (parT : Finset (Gp × Gp × ZMod q)) (fun p ↦ F (tupRe p)) := by
    rw [avg, avg, sum_dec hcard]
    congr 2
    simp only [parD, parT, card_product, card_nz hcard, card_nzq]
  have sM : (parM : Finset (Gp × Gp × ZMod q × ZMod q)) ⊆ parRa :=
    product_subset_product_right (product_subset_product_right
      (offDiag_mono (subset_univ _)))
  have sT : (parT : Finset (Gp × Gp × ZMod q)) ⊆ parRe :=
    product_subset_product_right (product_subset_product_right (subset_univ _))
  have d1 := abs_avg_sub_le sM hM (fun p ↦ F (tupRa p)) (fun p _ ↦ h0 _) (fun p _ ↦ h1 _)
  have d2 := abs_avg_sub_le sT hT (fun p ↦ F (tupRe p)) (fun p _ ↦ h0 _) (fun p _ ↦ h1 _)
  rw [ratio_messy hcard hq] at d1
  rw [ratio_dec hcard] at d2
  rw [eM, eD]
  unfold advDDH
  have t := abs_sub_le (avg (parM : Finset (Gp × Gp × ZMod q × ZMod q)) fun p ↦ F (tupRa p))
    (avg (parRa : Finset (Gp × Gp × ZMod q × ZMod q)) fun p ↦ F (tupRa p))
    (avg (parT : Finset (Gp × Gp × ZMod q)) fun p ↦ F (tupRe p))
  have t' := abs_sub_le (avg (parRa : Finset (Gp × Gp × ZMod q × ZMod q)) fun p ↦ F (tupRa p))
    (avg (parRe : Finset (Gp × Gp × ZMod q)) fun p ↦ F (tupRe p))
    (avg (parT : Finset (Gp × Gp × ZMod q)) fun p ↦ F (tupRe p))
  rw [abs_sub_comm] at d2
  have : |(avg (parRa : Finset (Gp × Gp × ZMod q × ZMod q)) fun p ↦ F (tupRa p)) -
      avg (parRe : Finset (Gp × Gp × ZMod q)) fun p ↦ F (tupRe p)| =
      |(avg (parRe : Finset (Gp × Gp × ZMod q)) fun p ↦ F (tupRe p)) -
      avg (parRa : Finset (Gp × Gp × ZMod q × ZMod q)) fun p ↦ F (tupRa p)| := abs_sub_comm _ _
  have hq' : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have : (3 : ℝ) / q = 2 / q + 1 / q := by field_simp; norm_num
  linarith

include hcard in
omit [Module (ZMod q) Gp] in
theorem parM_nonempty (hq : 2 < q) : (parM : Finset (Gp × Gp × ZMod q × ZMod q)).Nonempty := by
  have hnz : (nz : Finset Gp).Nonempty := by
    rw [← card_pos, card_nz hcard]; omega
  have hoff : (nzq : Finset (ZMod q)).offDiag.Nonempty := by
    rw [← card_pos, offDiag_card, card_nzq]
    have : 2 ≤ q - 1 := by omega
    have : 2 * (q - 1) ≤ (q - 1) * (q - 1) := Nat.mul_le_mul_right _ this
    omega
  exact hnz.product (hnz.product hoff)

omit [Fact q.Prime] [Fintype Gp] [DecidableEq Gp] in
theorem abs_avg_sub_avg_le {α : Type*} {s : Finset α} (hs : s.Nonempty) (f g : α → ℝ) (ε : ℝ)
    (h : ∀ p ∈ s, |f p - g p| ≤ ε) : |avg s f - avg s g| ≤ ε := by
  have ps : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  rw [avg, avg, ← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos ps, div_le_iff₀ ps]
  calc |∑ p ∈ s, (f p - g p)| ≤ ∑ p ∈ s, |f p - g p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ s, ε := sum_le_sum h
    _ = ε * s.card := by rw [sum_const, nsmul_eq_mul, mul_comm]

/-! ### Zero knowledge under DDH -/

section ZK

variable {k : ℕ} {V R D : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ι : V → Gp)
  (decode : Gp → V) (H : ℕ → V → V) (C : Circuit) (o : ℕ) (w : ℕ → Bool)
  [DecidableEq V] [DecidableEq R] [Fintype V] [Fintype R] [Fintype D] [NeZero q]

omit [Fact q.Prime] [Fintype Gp] [DecidableEq Gp] [Module (ZMod 2) V] in
theorem pHyb_le_one [Nonempty R] [Nonempty D] (c : Crs Gp) (Ve : PVer k q V R D Gp)
    (x : ℕ → Bool) : pHyb c ι decode Ve H C o x ≤ 1 := by
  classical
  have pN : 0 < Fintype.card (Fin k → ZMod q) := Fintype.card_pos
  have pX : 0 < Fintype.card ((V × R → D) × D) := Fintype.card_pos
  have pR : 0 < Fintype.card R := Fintype.card_pos
  unfold pHyb
  rw [div_le_one (by positivity)]
  have : (∑ r : Fin k → ZMod q, ∑ rr : R, (univ.filter fun y : (V × R → D) × D ↦
      hybP c ι decode Ve H C o x r y.1 y.2 rr).card) ≤
      Fintype.card (Fin k → ZMod q) * Fintype.card ((V × R → D) × D) * Fintype.card R := by
    calc _ ≤ ∑ _r : Fin k → ZMod q, ∑ _rr : R, Fintype.card ((V × R → D) × D) :=
          sum_le_sum fun r _ ↦ sum_le_sum fun rr _ ↦ card_filter_le _ _
      _ = _ := by simp [sum_const, card_univ]; ring
  convert (Nat.cast_le (α := ℝ)).2 this using 1
  push_cast; ring

include hcard in
/-- **Zero knowledge with the PVW OT in messy mode, under DDH.** Let the verifier depend on the
common string and make at most `Q` queries. Averaged over the messy setup, the real execution and
the simulator differ by at most `Q / |R|` plus the DDH advantages of the distinguishers `p_w` and
`p_0` plus `6 / q`. -/
theorem zk_pvw_ddh [Nonempty R] [Nonempty D] (hq : 2 < q) (Ve : Crs Gp → PVer k q V R D Gp)
    (Q : ℕ) (hQ : ∀ c, (Ve c).q₁ + (Ve c).q₂ + (Ve c).q₃ ≤ Q)
    (hι : ∀ v, decode (ι v) = v) (hw : (plain w C).getD o false = true)
    (hC : OT.InputsBelow k C) :
    |avg (parM : Finset (Gp × Gp × ZMod q × ZMod q))
        (fun p ↦ pReal (crsM p) ι decode (Ve (crsM p)) H C o w) -
      avg (parM : Finset (Gp × Gp × ZMod q × ZMod q))
        (fun p ↦ pHyb (crsM p) ι decode (Ve (crsM p)) H C o fun _ ↦ false)| ≤
      (Q : ℝ) / Fintype.card R + advDDH (q := q) (fun c ↦ pHyb c ι decode (Ve c) H C o w) +
        advDDH (q := q) (fun c ↦ pHyb c ι decode (Ve c) H C o fun _ ↦ false) + 6 / q := by
  set Hw : Crs Gp → ℝ := fun c ↦ pHyb c ι decode (Ve c) H C o w
  set H0 : Crs Gp → ℝ := fun c ↦ pHyb c ι decode (Ve c) H C o fun _ ↦ false
  have pR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have a := abs_avg_sub_avg_le (parM_nonempty hcard hq)
    (fun p ↦ pReal (crsM p) ι decode (Ve (crsM p)) H C o w) (fun p ↦ Hw (crsM p))
    ((Q : ℝ) / Fintype.card R) fun p _ ↦
      (real_hyb (crsM p) ι decode (Ve (crsM p)) H C o w hι hw hC).trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hQ _) pR.le)
  have b : avg (parD : Finset (Gp × ZMod q × ZMod q)) (fun p ↦ Hw (crsD p)) =
      avg (parD : Finset (Gp × ZMod q × ZMod q)) (fun p ↦ H0 (crsD p)) := by
    unfold avg
    congr 1
    exact sum_congr rfl fun p hp ↦
      pHyb_dec (crsD p) ι decode (Ve (crsD p)) H C o (crsD_dec p hp) _ _
  have cw := abs_modes_le hcard hq Hw (fun c ↦ pHyb_nonneg c ι decode (Ve c) H C o w)
    (fun c ↦ pHyb_le_one ι decode H C o c (Ve c) w)
  have c0 := abs_modes_le hcard hq H0
    (fun c ↦ pHyb_nonneg c ι decode (Ve c) H C o fun _ ↦ false)
    (fun c ↦ pHyb_le_one ι decode H C o c (Ve c) fun _ ↦ false)
  rw [b] at cw
  have t1 := abs_sub_le (avg (parM : Finset (Gp × Gp × ZMod q × ZMod q))
      (fun p ↦ pReal (crsM p) ι decode (Ve (crsM p)) H C o w))
    (avg (parM : Finset (Gp × Gp × ZMod q × ZMod q)) (fun p ↦ Hw (crsM p)))
    (avg (parM : Finset (Gp × Gp × ZMod q × ZMod q)) (fun p ↦ H0 (crsM p)))
  have t2 := abs_sub_le (avg (parM : Finset (Gp × Gp × ZMod q × ZMod q)) (fun p ↦ Hw (crsM p)))
    (avg (parD : Finset (Gp × ZMod q × ZMod q)) (fun p ↦ H0 (crsD p)))
    (avg (parM : Finset (Gp × Gp × ZMod q × ZMod q)) (fun p ↦ H0 (crsM p)))
  rw [abs_sub_comm (avg (parD : Finset (Gp × ZMod q × ZMod q)) (fun p ↦ H0 (crsD p)))] at t2
  have hq' : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have : (6 : ℝ) / q = 3 / q + 3 / q := by field_simp; norm_num
  linarith

end ZK

end Prime

end GcZk.PVW
