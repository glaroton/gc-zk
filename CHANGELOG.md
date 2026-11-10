# Changelog

Changes to the public interface listed in `GcZk/API.lean` are recorded here, release by release.
A renamed declaration keeps its old name as a deprecated alias for at least one release.

## v0.1.0 (2026-11-10)

First public release. Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`.

* The privacy-free Free-XOR garbling, its correctness, and authenticity: in an ideal model, in the
  random oracle model, and adaptive authenticity.
* The protocol of Jawurek, Kerschbaum and Orlandi with ideal oblivious transfer and commitment:
  completeness, zero knowledge against a malicious verifier, soundness by reduction to
  authenticity, and the variant without opening (honest-verifier zero knowledge only).
* The hash commitment in the random oracle model: zero knowledge, binding and end-to-end soundness.
* The Chou–Orlandi OT: zero knowledge, and soundness by reduction to square Diffie–Hellman.
* The PVW dual-mode OT: soundness in messy mode, and zero knowledge reduced to DDH.
* Some ingredients for adaptive corruptions: the equivocation condition for the receiver of the OT
  (PVW in decryption mode, not in messy mode; Chou–Orlandi given the sender's secret), the
  explanation of the prover, the equivocation of the hash commitment, and soundness in decryption
  mode.
* Cut-and-choose bounds against a malicious garbler.
