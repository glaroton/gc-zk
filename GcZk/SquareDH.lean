/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.ObliviousTransfer

/-!
# Sender security of the Chou–Orlandi OT: the square Diffie–Hellman reduction

In the Chou–Orlandi OT the sender masks the two labels of an input with the keys
`H_K(a • B)` and `H_K(a • (B - A))`, where `A = a • g` and `B` is the receiver's message. A
receiver that learns both labels must, in the random oracle model, query `H_K` at both key points.
Their difference is `a • A = (a * a) • g`, so such a receiver solves the *square Diffie–Hellman*
problem: given `a • g`, compute `(a * a) • g`.

## Main results

* `GcZk.SqDH.keys_sub`: the two key points differ by `(a * a) • g`.
* `GcZk.SqDH.card_both_le`: a receiver that, for uniform `a`, queries both key points among its
  `n` key queries yields `n²` square-DH solvers, one per pair of query positions, and
  `#{a : both keys queried} ≤ Σ_{i,j < n} #{a : solver (i, j) wins}`. So
  `Pr[both keys queried] ≤ n² · max Adv_sqDH`.

The square Diffie–Hellman problem is equivalent to the computational Diffie–Hellman problem in
groups of odd prime order: a CDH solver applied to `(a • g, a • g)` gives `(a * a) • g`, and
conversely, from a square solver `S`, `(a * b) • g = 2⁻¹ • (S((a + b) • g) - S(a • g) - S(b • g))`
(not formalized). No hardness is assumed in Lean: the theorem is a reduction, and the bound is
in terms of the advantage of explicit solvers built from the receiver.
-/

namespace GcZk.SqDH

variable {q : ℕ} {Gp : Type*} [AddCommGroup Gp] [Module (ZMod q) Gp] (g : Gp)

/-- A square Diffie–Hellman solver wins on `a` if, given `a • g`, it outputs `(a * a) • g`. -/
def Wins (S : Gp → Gp) (a : ZMod q) : Prop := S (a • g) = (a * a) • g

/-- **The two key points differ by `(a * a) • g`.** -/
theorem keys_sub (a : ZMod q) (B : Gp) : a • B - a • (B - a • g) = (a * a) • g := by
  rw [smul_sub, sub_sub_cancel, mul_smul]

/-- A receiver, as seen from the sender's secret: its message `B` and its `n` key queries, as
functions of `A = a • g` (all its other randomness fixed). -/
structure Receiver (Gp : Type*) where
  n : ℕ
  msg : Gp → Gp
  query : Gp → ℕ → Gp

/-- The receiver queries both key points of the sender with secret `a`. -/
def BothKeys (Rc : Receiver Gp) (a : ZMod q) : Prop :=
  ∃ i < Rc.n, ∃ j < Rc.n, Rc.query (a • g) i = a • Rc.msg (a • g) ∧
    Rc.query (a • g) j = a • (Rc.msg (a • g) - a • g)

/-- The square-DH solver that subtracts the `j`-th key query from the `i`-th. -/
def solver (Rc : Receiver Gp) (i j : ℕ) : Gp → Gp := fun A ↦ Rc.query A i - Rc.query A j

theorem solver_wins (Rc : Receiver Gp) (a : ZMod q) {i j : ℕ}
    (hi : Rc.query (a • g) i = a • Rc.msg (a • g))
    (hj : Rc.query (a • g) j = a • (Rc.msg (a • g) - a • g)) :
    Wins g (solver Rc i j) a := by
  rw [Wins, solver, hi, hj, keys_sub]

variable [NeZero q]

open Classical in
/-- **The reduction.** The secrets for which the receiver queries both key points are at most the
wins of the `n²` solvers, summed. With `a` uniform,
`Pr[both keys queried] ≤ Σ_{i,j < n} Pr[solver (i, j) wins] ≤ n² · max Adv_sqDH`. -/
theorem card_both_le (Rc : Receiver Gp) :
    (Finset.univ.filter fun a : ZMod q ↦ BothKeys g Rc a).card ≤
      ∑ ij ∈ Finset.range Rc.n ×ˢ Finset.range Rc.n,
        (Finset.univ.filter fun a : ZMod q ↦ Wins g (solver Rc ij.1 ij.2) a).card := by
  refine (Finset.card_le_card fun a ha ↦ ?_).trans Finset.card_biUnion_le
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨i, hi, j, hj, h1, h2⟩ := ha
  exact Finset.mem_biUnion.2 ⟨(i, j), by simp [hi, hj], by
    simpa using solver_wins g Rc a h1 h2⟩

open Classical in
/-- The same bound with the best solver: `#{a : both keys queried} ≤ n² · max_{i,j} #{wins}`. -/
theorem card_both_le_max (Rc : Receiver Gp) (ε : ℕ)
    (hε : ∀ i j, (Finset.univ.filter fun a : ZMod q ↦ Wins g (solver Rc i j) a).card ≤ ε) :
    (Finset.univ.filter fun a : ZMod q ↦ BothKeys g Rc a).card ≤ Rc.n * Rc.n * ε := by
  refine (card_both_le g Rc).trans ?_
  calc _ ≤ ∑ _ij ∈ Finset.range Rc.n ×ˢ Finset.range Rc.n, ε :=
        Finset.sum_le_sum fun ij _ ↦ hε ij.1 ij.2
    _ = Rc.n * Rc.n * ε := by simp

end GcZk.SqDH
