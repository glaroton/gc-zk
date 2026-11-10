/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk

/-!
# The public interface of gc-zk

`import GcZk.API` (or `import GcZk`) gives the whole library. The declarations listed here are
the ones meant to be used by other projects. Their names and statements are kept stable across
versions: a renamed declaration keeps its old name as a `@[deprecated]` alias for at least one
release, and a changed statement is recorded in the changelog. Every other declaration is an
implementation detail and may change. The blueprint documents each statement in the usual
mathematical language; its labels (`thm:zk`, `thm:co-sound`, ...) are stable as well.

## Circuits and the garbling (`GcZk`)

* `GcZk.Node`, `GcZk.Circuit`, `GcZk.plain`: circuits and their plaintext evaluation.
* `GcZk.Seed`, `GcZk.Material`, `GcZk.lab`, `GcZk.garble`, `GcZk.eval`, `GcZk.activeInputs`: the
  privacy-free Free-XOR garbling and its evaluation.
* `GcZk.eval_garble`: correctness.

## The protocol with ideal OT and commitment (`GcZk.Jko`)

* `GcZk.Jko.VerifierMsg`, `GcZk.Jko.proverLabel`, `GcZk.Jko.Verified`, `GcZk.Jko.view`,
  `GcZk.Jko.sim`, `GcZk.Jko.honestMsg`, `GcZk.Jko.Accepts`, `GcZk.Jko.Prover`, `GcZk.Jko.AuthWin`:
  the protocol, the verifier's view, the simulator, cheating provers and the authenticity game.
* `GcZk.Jko.complete`, `GcZk.Jko.zk`, `GcZk.Jko.view_witness_indep`, `GcZk.Jko.sound`,
  `GcZk.Jko.authWin_iff`: completeness, zero knowledge against a malicious verifier, soundness by
  reduction to authenticity.
* `GcZk.Jko.hvSim`, `GcZk.Jko.hvzk`, `GcZk.Jko.no_check_leaks`: the variant without opening.

## Authenticity

* `GcZk.Auth.garble_eq_idealMaterial`, `GcZk.Auth.exists_pads`, `GcZk.Auth.ideal_bound`: reduction
  to an ideal garbler with pads.
* `GcZk.RO.rom_bound`, `GcZk.Sec.garble_rom_bound`: authenticity in the random oracle model.
* `GcZk.Adaptive.adaptive_authenticity`: adaptive authenticity.

## Commitment and end-to-end soundness

* `GcZk.Com.zk_rom`, `GcZk.Com.zk_count`: zero knowledge with the hash commitment.
* `GcZk.Bind.prob_accept_le`, `GcZk.E2E.prob_accept_le`: soundness with the hash commitment.

## Oblivious transfer

* `GcZk.OT.zk_ot`: zero knowledge with the Chou–Orlandi OT.
* `GcZk.CO.prob_accept_le`: soundness with the Chou–Orlandi OT, by reduction to square
  Diffie–Hellman.
* `GcZk.SqDH.card_both_le`, `GcZk.SqDH.card_both_le_max`: learning both labels of an input solves
  square Diffie–Hellman.
* `GcZk.PVW.enc_bijective`, `GcZk.PVW.messy_of_ext`, `GcZk.PVW.enc_zero_key`,
  `GcZk.PVW.prob_accept_le`: the PVW OT in messy mode and soundness with it.
* `GcZk.PVW.zk_pvw`, `GcZk.PVW.zk_pvw_modes`, `GcZk.PVW.zk_pvw_ddh`: zero knowledge with the PVW OT,
  reduced to DDH.

## Cut-and-choose

* `GcZk.CC.prob_cheats_fixed_le`, `GcZk.CC.prob_cheats_lindell`, `GcZk.CCG.caught_or_correct`,
  `GcZk.CCG.prob_fail_fixed_le`, `GcZk.CCG.prob_fail_lindell`.
-/
