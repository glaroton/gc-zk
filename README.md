# gc-zk

**Zero knowledge from privacy-free garbled circuits, formalized in Lean 4 and Mathlib.**

The library formalizes the zero-knowledge protocol of Jawurek, Kerschbaum and Orlandi (CCS 2013,
"JKO13") over the privacy-free Free-XOR garbling of Zahur, Rosulek and Evans (EUROCRYPT 2015,
Sect. 6): correctness, authenticity in the random oracle model, the protocol with ideal and with
real commitments and oblivious transfers, adaptive authenticity, and cut-and-choose.

The blueprint (the mathematics in the usual language, each result naming its Lean counterpart; the
web version adds a dependency graph) has its source in [`blueprint/src`](blueprint/src); build it
with `leanblueprint pdf` or `leanblueprint web`. The original plan is in [DESIGN.md](DESIGN.md).

## What the protocol is for

JKO13 is an interactive zero-knowledge argument of knowledge for statements "I know `w` with
`C(w) = 1`", for any Boolean circuit `C`. Its cost is proportional to the size of `C`, and besides
one oblivious transfer per witness bit it uses only a hash, so it suits statements without
algebraic structure.

* **Typical uses** (JKO13, Sect. 1 and 1.1): knowledge of a hash preimage (`y = SHA-256(x)`), of a
  block-cipher key (`y₁ = AES_k(y₂)`), statements about data encrypted under a secret key, and
  knowledge of a signature or a Fiat–Shamir proof without revealing it. With the half-gates
  garbling, the garbled circuit for an AES key is about 108 KB with 128-bit labels (ZRE15, Sect. 6).
* **What it does not give:** it is interactive and convinces only the verifier who garbled the
  circuit. It is not public-coin, so Fiat–Shamir does not apply (JKO13, Sect. 3, footnote 6): there
  is no non-interactive, publicly verifiable proof. Each proof needs a fresh garbling, since the
  opening reveals `Δ`.
* **Ways to make it insecure:** a prover that reveals its output label before checking the opened
  garbling (a malicious verifier can garble another circuit or mount a selective-failure attack);
  sending the garbled circuit before the OTs, or an OT that lets the prover choose its input late
  (the garbling must then be adaptively secure; this is the Chou–Orlandi case); accepting the PVW
  key `(0, 0)`, which sends the messages in the clear (the sender here rejects every key with first
  component `0`); a hash that is only correlation robust
  (Choi–Katz–Kumaresan–Zhou, TCC 2012); short labels.

The introduction of the blueprint discusses each point and the theorem it relates to.

## Message order and the security it gives

What can be proved depends mostly on the order of the messages: when the prover's witness bits are
fixed relative to the moment it sees the garbled circuit, and when the verifier opens its garbling
relative to the prover's answer. Chapter 2 of the blueprint explains each case with its sources;
this is its summary, with the Lean theorems.

| Choice | Security that can be expected | Lean |
|---|---|---|
| Witness fixed, then garbled circuit | Soundness from static authenticity | `GcZk.Jko.sound`, `GcZk.Sec.garble_rom_bound`, `GcZk.E2E.prob_accept_le`, `GcZk.PVW.prob_accept_le` |
| Garbled circuit first, or an OT with late choice | Soundness needs adaptive authenticity | `GcZk.Adaptive.adaptive_authenticity`, `GcZk.CO.prob_accept_le` |
| No opening | Honest-verifier zero knowledge only | `GcZk.Jko.hvzk`, `GcZk.Jko.no_check_leaks` |
| Commit, open, check, reveal | Zero knowledge against a malicious verifier, one circuit | `GcZk.Jko.zk`, `GcZk.Com.zk_rom`, `GcZk.OT.zk_ot`, `GcZk.PVW.zk_pvw_ddh` |
| Garbling cannot be opened | Cut-and-choose, error `2^{-N}` | `GcZk.CC.prob_cheats_lindell`, `GcZk.CCG.caught_or_correct` |
| Ideal OT and commitment | Perfect zero knowledge | `GcZk.Jko.zk` |
| Hash commitment (random oracle) | Statistical zero knowledge, programmable oracle | `GcZk.Com.zk_rom` |
| PVW OT, messy mode | Computational zero knowledge (DDH) | `GcZk.PVW.zk_pvw_ddh` |
| Chou–Orlandi OT | Soundness by reduction to square Diffie–Hellman | `GcZk.CO.prob_accept_le` |
| Adaptive corruptions | A receiver-equivocal OT with an ideal commitment suffices (Ganesh–Kondi–Patra–Sarkar) | the ingredients: `GcZk.AC.pvw_dec_equivocal`, `GcZk.AC.explain_prover`, `GcZk.AC.equivocate_rom`, `GcZk.AC.prob_accept_dec_le`; adaptive security itself is not formalized |

The security statements above assume *static* corruptions: the adversary chooses at the start which
party it controls. Against *adaptive* corruptions, a simulator must also explain its transcript when
the prover is corrupted late. For two parties this matters mainly when the proof is a component of
a larger, composed protocol. What has to be explained depends on when the prover is corrupted
(Chapter 2, Sect. 2.5; the table is our reading, after Ganesh–Kondi–Patra–Sarkar, PKC 2018,
Sect. 3, who prove the case of an ideal commitment):

| Prover corrupted | To be explained | Property used |
|---|---|---|
| before the oblivious transfers | nothing | none |
| after the oblivious transfers, before the commitment | its OT messages, for the actual witness | receiver-equivocal OT (`GcZk.AC.pvw_dec_equivocal`, `GcZk.AC.explain_prover`) |
| after the commitment, before the opening | its OT messages and its commitment | also an equivocal commitment (`GcZk.AC.equivocate_rom`) |
| after the label is revealed | its OT messages; the commitment is already opened | receiver-equivocal OT; the label does not depend on the witness (`GcZk.Jko.zk`, `GcZk.AC.explain_prover`) |

Universal composability (UC) and adaptive security itself, which needs a model of execution with
corruptions, are discussed in the blueprint but not formalized here. What is formalized are the
protocol-specific ingredients of the table (`GcZk/Corruption.lean`, see the contents below).

**No claim of originality.** No originality is claimed for any definition, statement or proof
idea: the protocols, the security notions and the arguments come from the cited literature or are
standard in it. What is ours is only their formalization in Lean. Where a statement could not yet be
matched with a published one, the blueprint says so; should any of them turn out to be new, this will
be stated separately.

## Checking the proofs

There is no `sorry`. The main theorems depend only on `propext`, `Classical.choice` and
`Quot.sound`:

```bash
lake exe cache get
lake build
lake env lean scripts/Axioms.lean
```

The check that every declaration cited in the blueprint exists uses `checkdecls`, a development
dependency that Lake loads only on request:

```bash
lake -R -Kenv=dev exe checkdecls blueprint/lean_decls
```

## Using gc-zk from another project

Add gc-zk as a Lake dependency, pinned to a release tag, and `import GcZk`. It requires only Mathlib.
A project that depends on it must use the same Lean and Mathlib versions, given in
`lean-toolchain` and `lakefile.lean` (currently Lean `v4.36.0-rc2` and the Mathlib tag of the same
name).

The declarations meant for other projects are listed in `GcZk/API.lean`: the protocol, the
simulators, and the zero-knowledge, soundness and authenticity theorems. Their names and statements
are kept stable; a renamed declaration keeps its old name as a deprecated alias for at least one
release, and changes are recorded at each release. Everything else is an implementation detail.
The module root `GcZk` and the namespaces `GcZk.*` do not clash with those of other libraries.

## Contents

### The garbling

* `GcZk/Garbling.lean`: the garbling, with the non-linear gate written as a multiplexer (the
  evaluator half-gate of ZRE15 followed by a free XOR), and its correctness
  (`GcZk.eval_garble`): evaluating on the active input labels gives every node's plaintext value
  `v` and the label `L + v • Δ`, with no hypothesis on the hash or on `Δ`.

### The protocol with ideal OT and commitment

* `GcZk/Jko.lean`: the JKO13 protocol in the hybrid model with ideal OT and commitment.
  * `GcZk.Jko.complete`: completeness.
  * `GcZk.Jko.zk`: perfect zero knowledge against a malicious verifier. For every message the
    verifier sends, its view equals the output of a simulator that does not use the witness.
  * `GcZk.Jko.sound`: if `C` is unsatisfiable, the verifier accepts a cheating prover exactly
    when the prover wins the authenticity game of the garbling, bounded below.
  * Without the opening (the warm-up of JKO13, Sect. 3): `GcZk.Jko.hvzk`, zero knowledge against
    an honest verifier; `GcZk.Jko.no_check_leaks`, a malicious verifier that offers inconsistent
    OT pairs for the circuit `x₀ ⊕ x₁` learns the first witness bit from a prover that does not
    check, while the full protocol aborts on the same messages.

### Authenticity

* `GcZk/Authenticity.lean`: authenticity, reduced to an ideal model.
  * `GcZk.Auth.garble_eq_idealMaterial`, `GcZk.Auth.exists_pads`: the real material is produced
    by an ideal garbler that never uses `Δ`, from pads `H(i, S + Δ) + c Δ`. So `Δ` reaches the
    evaluator's view only through the hashes of inactive selector labels.
  * `GcZk.Auth.ideal_bound`: with uniform pads independent of `Δ`, any adversary outputs the
    inactive output label with probability at most `1 / (|V| - 1)`.
  * `GcZk.Jko.authWin_iff`: the authenticity game of the protocol is the game of finding
    `active output label + Δ`.
* `GcZk/RandomOracle.lean`: `GcZk.RO.rom_bound`. With `H` a uniformly random function and `Δ`
  uniform on `V \ {0}`, an adversary making `q` adaptive queries outputs the inactive output label
  with probability at most `(q + 1) / (|V| - 1)`. The proof is identical-until-bad by counting: an
  injection moves the hash values at the inactive points `(i, S_i + Δ)` into independent pads.
  This bound needs no characteristic 2.
* `GcZk/Security.lean`: `GcZk.Sec.garble_rom_bound`, the same bound for the real garbling
  (`GcZk.garble`) with `Δ`, the hash and all the zero-labels uniform. The adversary also receives
  the active labels of its input.

### Real commitment, end-to-end soundness

* `GcZk/Commitment.lean`, `GcZk/Binding.lean`: the ideal commitment replaced by the hash
  commitment `G(Z, r)` in the random oracle model (OT still ideal).
  * `GcZk.Com.zk_rom`: statistical zero knowledge against a malicious verifier with `q₁ + q₂ + q₃`
    queries, error at most `(q₁ + q₂ + q₃) / |R|`. The simulator programs the oracle.
  * `GcZk.Bind.prob_accept_le`: a cheating prover is accepted with probability at most that of an
    extractor (an authenticity adversary) plus `(q₁² + q₂ + 1) / |D|`.
* `GcZk/EndToEnd.lean`: `GcZk.E2E.prob_accept_le`, end-to-end soundness. With the seed, the
  garbling hash and the commitment oracle uniform, a cheating prover for an unsatisfiable circuit,
  with `n₁` query steps before committing and `n₂` after, is accepted with probability at most
  `(n₁ + 1) / (|V| - 1) + (n₁² + n₂ + 1) / |D|`.

### Real oblivious transfer

In these files `q` is the order of the group, and numbers of queries carry subscripts.

* `GcZk/ObliviousTransfer.lean`: the ideal OT replaced by the Chou–Orlandi OT. `GcZk.OT.zk_ot`:
  zero knowledge with the real OT and the hash commitment, error at most
  `(q₀ + q₁ + q₂ + q₃) / |R|`, for circuits that read only the inputs `j < k`. Receiver privacy is
  perfect, and the verifier opens its OT secrets so the prover checks both masked labels.
* `GcZk/PVW.lean`, `GcZk/PVWSound.lean`: the DDH instance of the dual-mode OT of Peikert,
  Vaikuntanathan and Waters (CRYPTO 2008, Sect. 5.3) in messy mode, as Jawurek, Kerschbaum and
  Orlandi suggest for `F_COT` (their Appendix A). On a messy branch encryption is a bijection of the
  coins (`GcZk.PVW.enc_bijective`), and the trapdoor extracts the receiver's choice from its key
  provided its first component is nonzero (`GcZk.PVW.messy_of_ext`); the verifier checks this,
  since the key `(0, 0)` leaks both messages (`GcZk.PVW.enc_zero_key`). `GcZk.PVW.prob_accept_le`:
  end-to-end soundness with this OT, with the same bound as `GcZk.E2E.prob_accept_le`, by an exact
  reduction.
* `GcZk/PVWZK.lean`: zero knowledge with the PVW OT. `GcZk.PVW.zk_pvw`: for a fixed common string,
  the real execution and the simulator (keys of the choice `0`, then the simulator of `GcZk.Com`)
  differ by at most `(q₁ + q₂ + q₃) / |R|` plus `|p_w - p_0|`, where `p_x` is the probability of
  output `1` with the keys of `x` and the simulator. In decryption mode `p_x` does not depend on `x`
  (`GcZk.PVW.pHyb_dec`), so averaged over messy strings the error is `Q / |R|` plus the advantages
  of two explicit distinguishers between the modes (`GcZk.PVW.zk_pvw_modes`), negligible under DDH
  by PVW, Theorem 5.2.
* `GcZk/PVWDDH.lean`: the messy and decryption setups are random and DDH tuples with the zero
  exponents removed (`GcZk.PVW.sum_messy`, `GcZk.PVW.sum_dec`), which costs `3 / q`
  (`GcZk.PVW.abs_modes_le`). `GcZk.PVW.zk_pvw_ddh`: averaged over the messy setup, the ZK error is
  at most `Q / |R| + Adv_DDH(p_w) + Adv_DDH(p_0) + 6 / q`.

### Adaptive authenticity and soundness with the Chou–Orlandi OT

With the Chou–Orlandi OT the prover can choose its input after seeing the garbled circuit, so
soundness needs adaptive authenticity.

* `GcZk/Adaptive.lean`, `GcZk/LinearPart.lean`, `GcZk/AdaptiveBad.lean`,
  `GcZk/AdaptiveShift.lean`, `GcZk/AdaptiveFresh.lean`, `GcZk/AdaptiveBound.lean`: authenticity when
  the evaluator requests its input labels one at a time, after seeing the material and interleaved
  with hash queries. `GcZk.Adaptive.adaptive_authenticity`: an adversary taking `q` actions (queries
  and requests together) wins with probability at most `(q + 1) / (|V| - 1) + q / |V|`.
* `GcZk/COSound.lean`, `GcZk/COSqDH.lean`, `GcZk/COFinal.lean`: soundness with the Chou–Orlandi OT.
  `GcZk.CO.prob_accept_le`: the verifier accepts with probability at most
  `(n₁² + n₂ + 1) / |D| + (Q + 1) / (|V| - 1) + Q / |V| + k / q + Adv`, with `Q = 2(k + n₁)` and
  `Adv` the sum of the advantages of `k (n₀ + n₁)(n₀ + n₁ - 1)` explicit square Diffie–Hellman
  solvers, in a group of prime order `q`.

### Ingredients for adaptive corruptions

* `GcZk/Corruption.lean`. `GcZk.AC.ReceiverEquivocal`: the receiver's OT message can be produced
  without the choice bit and explained for either bit by a bijection of its randomness (Ganesh,
  Kondi, Patra and Sarkar, PKC 2018, Definition 3.1). `GcZk.AC.pvw_dec_equivocal`: the PVW
  receiver in decryption mode is receiver equivocal (ibid., Theorem 3.2). `GcZk.AC.co_equivocal`:
  so is the Chou–Orlandi receiver, for a party that knows the sender's secret.
  `GcZk.AC.explain_prover`: with a receiver-equivocal OT, the prover's OT messages and the
  verifier's view, for any witness and the explained randomness, are the simulated ones.
  `GcZk.AC.equivocate_rom`: a prover corrupted after committing reveals `(Z_w, r)`; a simulator
  that committed to a uniform value and programs `G(Z_w, r)` at the corruption is off by at most
  `(q₁ + q₂ + q₃) / |R|`. `GcZk.AC.prob_accept_dec_le`: soundness with the PVW OT in decryption
  mode, at most the messy-mode bound plus the DDH advantage of the acceptance probability plus
  `3 / q`.

### Cut-and-choose

* `GcZk/CutAndChoose.lean`: cut-and-choose against a malicious garbler, when one good evaluated
  circuit suffices. Cheating means guessing the evaluation set exactly (`GcZk.CC.cheats_iff`).
  The error is at most `1 / binom(N, t)` for a uniform `t`-subset, with equality when `t` circuits
  are bad. It is exactly `2^{-N}` with independent fair coins (Lindell, CRYPTO 2013).
  `binom(N, t) ≤ 2^N`.
* `GcZk/CutAndChooseGarbling.lean`: the same bounds for copies of the garbling. A copy is good when
  it is the garbling of its own seed (checked by opening). `GcZk.CCG.caught_or_correct`: an opened
  copy is caught, or an evaluated good copy outputs `C(x)` with its label, or the evaluation set is
  exactly the set of bad copies.

## What is not formalized

The efficiency of the DDH distinguishers and of the square Diffie–Hellman solvers (Lean has no
notion of efficient computation), the hash outside the random oracle model, the reduction of
adversaries with fewer or differently interleaved queries to the fixed form, adaptive security
itself and universal composition (only their protocol-specific ingredients are formalized), the consistency of the garbler's inputs across cut-and-choose copies, and
any implementation. Details are in the last chapter of the blueprint.

## Related work

The introduction of the blueprint discusses these works, with precise references.

* **Frameworks for game-based proofs:** EasyCrypt, CryptHOL (Isabelle/HOL), SSProve (Coq), and, in
  Lean 4, VCVio and CatCrypt. gc-zk does not use a framework: probabilities are counts over finite
  types, and games are functions of the randomness.
* **Garbled circuits and secure computation, formalized:** the EasyCrypt verification of Yao's
  secure function evaluation (Almeida et al., CCS 2017); simulation-based security of multi-party
  computation in Isabelle/HOL (Butler–Aspinall–Gascón, ITP 2017); in Lean 4, the simulation-based
  privacy of a garbling scheme, proved symbolically (Dziembowski–Fabiański–Micciancio–Stefański,
  CSF 2026). CatCrypt (Spitters, ePrint 2026/604) lists Yao's garbled circuits with half-gates and a
  "Simplest OT" among its protocols, whose sources are private; as of November 2026 the README of
  its public core lists machinery for universal composability, and says that the UC theory itself is
  in separate distributions. A somewhat restricted variant of the UC framework has been mechanized
  in EasyCrypt (EasyUC, Canetti–Stoughton–Varia, CSF 2019).
* We are not aware of a previous formalization of zero knowledge from garbled circuits or of
  privacy-free garbling.
* **Adaptive garbling:** Bellare–Hoang–Rogaway (ASIACRYPT 2012) introduced adaptive privacy,
  obliviousness and authenticity; Hemenway et al. (CRYPTO 2016) and Jafargholi–Wichs (TCC 2016-B)
  prove adaptive privacy for a modification of Yao's scheme and for Yao's scheme itself. We have not
  found a published statement of adaptive authenticity for unmodified privacy-free garbling, which
  the Chou–Orlandi case needs.
* **The Chou–Orlandi OT:** a receiver can delay its decryption, as pointed out by Byali–Patra–Ravi–
  Sarkar (ePrint 2017/1165) and discussed by Doerner–Kondi–Lee–shelat (S&P 2018); Chou and Orlandi
  withdraw the claim of UC security of their protocol.
* **Adaptive corruptions:** Ganesh–Kondi–Patra–Sarkar (PKC 2018) show that JKO13 is secure against
  adaptive corruptions with a receiver-equivocal OT and an ideal commitment.

## How this library was written

glaroton chose the protocol and the model and reviews the results. The Lean proofs
were written by the AI assistant Claude (Anthropic) working under his direction. Correctness
does not depend on trusting either of them: Lean checks every proof.
