/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import Mathlib

/-!
# Cut-and-choose against a malicious garbler

The garbler sends `N` garbled circuits, of which the set `B` is bad. The evaluator chooses a set
`E` of circuits to evaluate and opens (checks) the others. As in Lindell's protocol [Lin13],
**one good evaluated circuit suffices**. So the garbler cheats
successfully iff no opened circuit is bad (it is not caught) and no evaluated circuit is good.
That happens iff `E = B` (`cheats_iff`).

## Main results

* `GcZk.CC.card_cheats_fixed`: if `E` is uniform among the `t`-subsets, at most one choice lets
  the garbler cheat. The error is at most `1 / binom(N, t)`, with equality when `|B| = t`
  (`card_cheats_fixed_eq`).
* `GcZk.CC.card_cheats_lindell`: if each circuit is evaluated or checked by an independent fair
  coin, i.e. `E` is uniform among all `2^N` subsets, the error is at most `2^{-N}`.
* `GcZk.CC.choose_le_two_pow`: `binom(N, t) ≤ 2^N`, so independent coins are never worse than
  any fixed `t`. For `N = 40` the best fixed `t` gives `2^{-37.0}` against `2^{-40}`.

With independent coins `E = ∅` has probability `2^{-N}` and is the cheating choice for `B = ∅`.
Lindell's protocol handles that case separately. It is inside the `2^{-N}` bound here.

## References

* [Lin13] Y. Lindell, *Fast cut-and-choose based protocols for malicious and covert adversaries*,
  CRYPTO 2013; J. Cryptology 29 (2016).
-/

namespace GcZk.CC

variable {N : ℕ}

/-- The garbler with bad set `B` cheats against the evaluation set `E`: every opened circuit is
good (not caught), and every evaluated circuit is bad (no correct output). -/
def Cheats (B E : Finset (Fin N)) : Prop := (∀ i, i ∉ E → i ∉ B) ∧ ∀ i ∈ E, i ∈ B

instance (B E : Finset (Fin N)) : Decidable (Cheats B E) := by
  unfold Cheats; infer_instance

/-- Cheating means guessing the evaluation set exactly. -/
theorem cheats_iff (B E : Finset (Fin N)) : Cheats B E ↔ E = B := by
  constructor
  · rintro ⟨h1, h2⟩
    ext i
    exact ⟨h2 i, fun hB ↦ by_contra fun hE ↦ h1 i hE hB⟩
  · rintro rfl
    exact ⟨fun _ h ↦ h, fun _ h ↦ h⟩

/-- **Fixed number of evaluated circuits.** Among the `t`-subsets, at most one evaluation set lets
the garbler cheat: the error of a uniform `t`-subset is at most `1 / binom(N, t)`. -/
theorem card_cheats_fixed (B : Finset (Fin N)) (t : ℕ) :
    ((Finset.univ.powersetCard t).filter (Cheats B)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro E hE E' hE'
  simp only [Finset.mem_filter, cheats_iff] at hE hE'
  rw [hE.2, hE'.2]

/-- The bound is attained: a garbler with exactly `t` bad circuits cheats against one
`t`-subset, with probability exactly `1 / binom(N, t)`. -/
theorem card_cheats_fixed_eq (B : Finset (Fin N)) :
    ((Finset.univ.powersetCard B.card).filter (Cheats B)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨B, ?_⟩
  ext E
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
    cheats_iff, Finset.mem_singleton]
  constructor
  · exact fun h ↦ h.2
  · rintro rfl; exact ⟨rfl, rfl⟩

/-- The number of `t`-subsets of the circuits. -/
theorem card_powersetCard (t : ℕ) :
    (Finset.univ.powersetCard t : Finset (Finset (Fin N))).card = N.choose t := by
  simp

/-- **Independent fair coins (Lindell).** Among all `2^N` evaluation sets, at most one lets the
garbler cheat: the error is at most `2^{-N}`. -/
theorem card_cheats_lindell (B : Finset (Fin N)) :
    ((Finset.univ.powerset).filter (Cheats B)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro E hE E' hE'
  simp only [Finset.mem_filter, cheats_iff] at hE hE'
  rw [hE.2, hE'.2]

/-- With independent coins every garbler cheats with probability exactly `2^{-N}`. -/
theorem card_cheats_lindell_eq (B : Finset (Fin N)) :
    ((Finset.univ.powerset).filter (Cheats B)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨B, ?_⟩
  ext E
  simp [cheats_iff]

/-- The number of evaluation sets with independent coins. -/
theorem card_powerset_univ :
    (Finset.univ.powerset : Finset (Finset (Fin N))).card = 2 ^ N := by
  simp

/-- `binom(N, t) ≤ 2^N`: independent coins are never worse than a fixed number of evaluated
circuits. -/
theorem choose_le_two_pow (t : ℕ) : N.choose t ≤ 2 ^ N :=
  Nat.choose_le_two_pow N t

/-- The error of a uniform `t`-subset, as a probability. -/
theorem prob_cheats_fixed_le (B : Finset (Fin N)) (t : ℕ) (ht : t ≤ N) :
    (((Finset.univ.powersetCard t).filter (Cheats B)).card : ℝ) /
        (Finset.univ.powersetCard t : Finset (Finset (Fin N))).card ≤ 1 / N.choose t := by
  rw [card_powersetCard]
  have hpos : (0 : ℝ) < N.choose t := by exact_mod_cast Nat.choose_pos ht
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_cheats_fixed B t) hpos.le

/-- The error with independent fair coins, as a probability. -/
theorem prob_cheats_lindell (B : Finset (Fin N)) :
    (((Finset.univ.powerset).filter (Cheats B)).card : ℝ) /
        (Finset.univ.powerset : Finset (Finset (Fin N))).card = 1 / 2 ^ N := by
  rw [card_cheats_lindell_eq, card_powerset_univ]
  push_cast; ring

end GcZk.CC
