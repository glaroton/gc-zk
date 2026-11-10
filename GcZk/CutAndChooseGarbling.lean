/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.Jko
import GcZk.CutAndChoose

/-!
# Cut-and-choose of garbled circuits

A (possibly malicious) garbler sends `N` copies of a garbling of the same circuit `C`. Each copy
consists of a claimed seed, the material, and the pair of labels offered for each input wire.
The evaluator opens some copies and evaluates the others on its input `x`.

A copy is *good* when its material is the garbling of `C` with its seed and its input pairs are
`(L, L + Δ)` (`GcZk.Jko.Verified`). Opening a copy reveals its seed, so the evaluator can check
goodness by garbling again. This is the hypothesis "opening a bad circuit reveals it" of
`GcZk.CC`, now a definition. "A good evaluated copy gives a correct output" becomes a theorem:
by `GcZk.eval_garble`, a good evaluated copy outputs the correct value `C(x)` with its correct
label. How the evaluator chooses among the outputs of several evaluated copies is not modeled.

## Main results

* `GcZk.CCG.output_of_good`: a good copy evaluates to the plaintext output and its label.
* `GcZk.CCG.caught_or_correct`: for every evaluation set `E`, either an opened copy is caught,
  or some evaluated copy outputs the correct result, or `E` is exactly the set of bad copies.
* `GcZk.CCG.prob_fail_fixed_le`, `GcZk.CCG.prob_fail_lindell`: the third case has probability
  at most `1 / binom(N, t)` for a uniform `t`-subset, and exactly `2^{-N}` with independent fair
  coins.

What is not modeled: the evaluator's input labels for the evaluated copies come through the
offered pairs, as in an OT, so the consistency of the garbler's own inputs across copies is
outside this file.
-/

namespace GcZk.CCG

open Jko

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {N : ℕ}

/-- One copy sent by the garbler: claimed seed, material, and input label pairs. -/
structure Copy (V : Type*) where
  seed : Seed V
  material : List (Material V)
  pairs : ℕ → V × V

/-- The copy is a correct garbling of `C` with its own seed. -/
def Good (H : ℕ → V → V) (C : Circuit) (c : Copy V) : Prop :=
  Verified H C ⟨c.material, c.pairs, c.seed⟩

/-- The output wire the evaluator obtains from a copy on its input `x`. -/
def output (H : ℕ → V → V) (C : Circuit) (out : ℕ) (x : ℕ → Bool) (c : Copy V) : Wire V :=
  (eval H (otReceive c.pairs x) C c.material).getD out (false, 0)

/-- **One good evaluated copy suffices.** A good copy evaluates to the plaintext output `C(x)`
and the label of that value. -/
theorem output_of_good (H : ℕ → V → V) (C : Circuit) (out : ℕ) (x : ℕ → Bool) {c : Copy V}
    (hc : Good H C c) :
    output H C out x c = ((plain x C).getD out false,
      lab c.seed.delta ((garble H c.seed C).1.getD out 0) ((plain x C).getD out false)) := by
  have h1 : c.material = (garble H c.seed C).2 := hc.1
  rw [output, h1, otReceive_eq_activeInputs c.seed c.pairs hc.2, eval_garble]

open Classical in
/-- The bad copies. -/
noncomputable def badSet (H : ℕ → V → V) (C : Circuit) (copies : Fin N → Copy V) :
    Finset (Fin N) :=
  Finset.univ.filter fun i ↦ ¬ Good H C (copies i)

/-- **Caught or correct.** For every evaluation set `E`: an opened copy is bad (the garbler is
caught), or an evaluated copy outputs the correct result, or `E` is exactly the set of bad
copies. -/
theorem caught_or_correct (H : ℕ → V → V) (C : Circuit) (out : ℕ) (x : ℕ → Bool)
    (copies : Fin N → Copy V) (E : Finset (Fin N)) :
    (∃ i ∉ E, ¬ Good H C (copies i)) ∨
      (∃ i ∈ E, output H C out x (copies i) = ((plain x C).getD out false,
        lab (copies i).seed.delta ((garble H (copies i).seed C).1.getD out 0)
          ((plain x C).getD out false))) ∨
      E = badSet H C copies := by
  by_cases hc : CC.Cheats (badSet H C copies) E
  · exact Or.inr (Or.inr ((CC.cheats_iff _ _).1 hc))
  · simp only [CC.Cheats, not_and_or, not_forall, not_not, exists_prop] at hc
    rcases hc with ⟨i, hi, hb⟩ | ⟨i, hi, hb⟩
    · refine Or.inl ⟨i, hi, ?_⟩
      simpa [badSet] using hb
    · refine Or.inr (Or.inl ⟨i, hi, output_of_good H C out x ?_⟩)
      simpa [badSet] using hb

open Classical in
/-- The evaluation sets for which the garbler is neither caught nor corrected by a good copy. -/
def Fails (H : ℕ → V → V) (C : Circuit) (copies : Fin N → Copy V) (E : Finset (Fin N)) : Prop :=
  (∀ i ∉ E, Good H C (copies i)) ∧ ∀ i ∈ E, ¬ Good H C (copies i)

omit [Module (ZMod 2) V] in
theorem fails_iff (H : ℕ → V → V) (C : Circuit) (copies : Fin N → Copy V)
    (E : Finset (Fin N)) : Fails H C copies E ↔ CC.Cheats (badSet H C copies) E := by
  simp only [Fails, CC.Cheats, badSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨fun i hi hb ↦ hb (h1 i hi), h2⟩,
    fun ⟨h1, h2⟩ ↦ ⟨fun i hi ↦ by_contra (h1 i hi), h2⟩⟩

omit [Module (ZMod 2) V] in
open Classical in
/-- **A fixed number of evaluated copies.** The garbler escapes both checks with probability at
most `1 / binom(N, t)`. -/
theorem prob_fail_fixed_le (H : ℕ → V → V) (C : Circuit) (copies : Fin N → Copy V) (t : ℕ)
    (ht : t ≤ N) :
    (((Finset.univ.powersetCard t).filter (Fails H C copies)).card : ℝ) /
        (Finset.univ.powersetCard t : Finset (Finset (Fin N))).card ≤ 1 / N.choose t := by
  have : (Finset.univ.powersetCard t).filter (Fails H C copies) =
      (Finset.univ.powersetCard t).filter (CC.Cheats (badSet H C copies)) :=
    Finset.filter_congr fun E _ ↦ fails_iff H C copies E
  rw [this]
  exact CC.prob_cheats_fixed_le _ t ht

omit [Module (ZMod 2) V] in
open Classical in
/-- **Independent fair coins.** The garbler escapes both checks with probability exactly
`2^{-N}`. -/
theorem prob_fail_lindell (H : ℕ → V → V) (C : Circuit) (copies : Fin N → Copy V) :
    (((Finset.univ.powerset).filter (Fails H C copies)).card : ℝ) /
        (Finset.univ.powerset : Finset (Finset (Fin N))).card = 1 / 2 ^ N := by
  have : (Finset.univ.powerset).filter (Fails H C copies) =
      (Finset.univ.powerset).filter (CC.Cheats (badSet H C copies)) :=
    Finset.filter_congr fun E _ ↦ fails_iff H C copies E
  rw [this]
  exact CC.prob_cheats_lindell _

end GcZk.CCG
