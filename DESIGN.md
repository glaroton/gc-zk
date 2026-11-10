# gc-zk: design

No originality is claimed for any definition, statement or proof idea: they come from the cited
literature or are standard in it. What is ours is only the formalization in Lean.

Goal: a Lean 4 / Mathlib formalization of zero knowledge from privacy-free garbled circuits:
the protocol of Jawurek–Kerschbaum–Orlandi (CCS 2013, "JKO13"), instantiated with a privacy-free
garbling in the sense of Frederiksen–Nielsen–Orlandi (Eurocrypt 2015, "FNO15").
We are not aware (2026-11-09) of a previous formalization of zero knowledge from garbled circuits
or of privacy-free garbling; the related work is discussed in the introduction of the blueprint.

This file is the original plan, kept for the record. All four phases are done; the current state
is in the README, and what is not formalized is listed in the last chapter of the blueprint.

The garbling scheme is the privacy-free scheme of Zahur–Rosulek–Evans (EUROCRYPT 2015, Sect. 6):
Free XOR and their one-ciphertext evaluator half-gate, written as a multiplexer. The theorems are
about this abstract scheme; no implementation is verified.

## Phase 1: privacy-free Free-XOR garbling, correctness (no probability)

* Labels: any `ZMod 2`-module `V` (for instance `Fin 128 → ZMod 2`, 128-bit strings with XOR).
* Circuits: a list of nodes `input j | const b | xor a b | mux s z o`. Operands are indices of
  earlier nodes. Any index is accepted; out-of-range reads give the default wire.
* Garbling seed: global offset `Δ`, zero-labels of the inputs and constants, and a hash
  `H : ℕ → V → V` (gate index, label). Free XOR: `L_c = L_a + L_b`. The mux gate (a multiplexer
  form of the ZRE15 evaluator half-gate, which ZRE15 Sect. 6 use for privacy-free garbling) has zero-label `H(i, S) + Z` and one ciphertext
  `T = H(i, S) + H(i, S + Δ) + Z + O`.
* **Theorem (correctness).** For every input `x`, evaluating on the active input labels
  `L_j + x_j Δ` gives, at every node, the plaintext value `v` and the label `L + v Δ`.
  There are no hypotheses on `H` or `Δ`: correctness is pure algebra in characteristic 2.

## Phase 2: the JKO13 protocol in the (F_OT, F_COM)-hybrid model

The verifier V garbles `C = R(x, ·)` and sends the material. The prover P gets the labels of its
witness `w` through ideal oblivious transfer, evaluates, and commits to the output label `Z`
(ideal commitment). V opens the seed. P re-garbles, checks the material and the OT labels,
and opens. V accepts iff `Z = L_out + Δ`.

* **Completeness:** from Phase 1.
* **Zero knowledge against a malicious V, perfect, in the hybrid model.** The simulator reads V's
  OT inputs from F_OT and commits to nothing (F_COM is ideal). If V's opening verifies, Phase 1
  shows that the honest P's `Z` is the 1-label computed from the seed, so the simulator opens
  to it. Otherwise both abort. The views are equal as functions of V's coins.
* **Soundness:** if `R(x, ·)` is unsatisfiable, a cheating P is accepted only if it wins the
  authenticity game of the garbling. This is a reduction; the bound comes in Phase 3.
* Optional: the cut-and-choose bound `1 / binom(N, t)`
  (combinatorics on finite sets).

## Phase 3: authenticity of the concrete scheme (hardest)

The evaluator gets the material and the active input labels, and must output the inactive
output label. With `Δ` uniform and `H` a random oracle (or correlation-robust), the bound is
roughly `(q + #gates) / |V|` for `q` oracle queries. Here we decide between Mathlib's `PMF`
with a hand-made lazy oracle and VCV-io's `OracleComp` with query bounds.

Status (2026-11-08): Phase 3a is done (`GcZk/Authenticity.lean`): the real material comes from
an ideal garbler that does not use `Δ`, and in that ideal model the bound is `1 / (|V| - 1)`.
Phase 3b is done (`GcZk/RandomOracle.lean`, `GcZk.RO.rom_bound`): for a `q`-query adversary in
the random oracle model, the bound is `(q + 1) / (|V| - 1)`. The active labels are fixed
parameters; drawing them at random is a remark, not a theorem.

## Phase 4: the view with real OT and commitments

Status (2026-11-09): done without a general framework, by counting. The commitment is a hash
commitment in the random oracle model (`GcZk/Commitment.lean`, `GcZk/Binding.lean`,
`GcZk/EndToEnd.lean`). The OT is the Chou–Orlandi OT (zero knowledge in
`GcZk/ObliviousTransfer.lean`; soundness in `GcZk/COFinal.lean`, through adaptive authenticity
and a reduction to explicit square Diffie–Hellman solvers) or the dual-mode OT of Peikert,
Vaikuntanathan and Waters (`GcZk/PVW*.lean`, zero knowledge reduced to explicit DDH
distinguishers). The plan as written then was:

Phase 2 proves zero knowledge and soundness in the (F_OT, F_COM)-hybrid model. To drop the ideal
functionalities, instantiate OT and commitment with concrete protocols and prove the
composition. The verifier's view then contains the transcripts of those protocols, and zero
knowledge becomes computational indistinguishability, with a simulator that extracts the
verifier's OT inputs. This needs an adversary and simulator framework with negligible
advantages, which is where VCV-io would help.

## Conventions

As in lc-analysis and lc-manifolds: no `sorry`, the main theorems depend only on
`propext`, `Classical.choice` and `Quot.sound` (`scripts/Axioms.lean`), and the README states
how the library was written.
