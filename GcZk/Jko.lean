/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.Garbling

/-!
# Zero knowledge from privacy-free garbling (JKO13)

The protocol of Jawurek–Kerschbaum–Orlandi [JKO13] for proving knowledge of a witness `w` with
`C(w) = 1`, where `C` is a circuit with output node `out`. It runs in the hybrid model with
ideal oblivious transfer and ideal commitment:

1. The verifier garbles `C` with a seed `σ` and sends the material. Through the OT functionality
   the prover receives, for each input `j`, the label of `w j`.
2. The prover evaluates and commits to the output label `Z`.
3. The verifier opens `σ`. The prover re-garbles, and opens `Z` only if the material and the
   OT labels are the ones `σ` determines (`Verified`).
4. The verifier accepts iff `Z` is the 1-label `L_out + Δ` of the output node.

## Main results

* `GcZk.Jko.complete`: an honest prover with a witness convinces an honest verifier.
* `GcZk.Jko.zk`: perfect zero knowledge against a malicious verifier. Whatever the verifier
  sends, its view (the opened label, or an abort) is computed by `sim` from its own messages,
  without the witness.
* `GcZk.Jko.sound`: if no input satisfies `C`, a cheating prover is accepted exactly when it
  outputs the inactive output label, i.e. when it wins the authenticity game of the garbling.
* `GcZk.Jko.hvzk`: without the opening, zero knowledge against an honest verifier.
* `GcZk.Jko.no_check_leaks`: without the prover's check, a malicious verifier learns a witness
  bit from the OT pairs alone.

In the hybrid model the OT functionality gives the verifier nothing, and the commitment
functionality gives it only the information that the prover committed. Its view is therefore
the opened label or an abort, a function of its own messages. A verifier that randomizes is a
family of deterministic ones indexed by its coins, so equality of views for every message
gives equality of view distributions.

## References

* [JKO13] M. Jawurek, F. Kerschbaum, C. Orlandi, *Zero-knowledge using garbled circuits: how to
  prove non-algebraic statements efficiently*, ACM CCS 2013.
-/

namespace GcZk.Jko

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Everything a (possibly malicious) verifier sends: the garbled material, its inputs to the
OT functionality (the pair of labels offered for each input wire), and the opened seed. -/
structure VerifierMsg (V : Type*) where
  material : List (Material V)
  pairs : ℕ → V × V
  opening : Seed V

/-- What the OT functionality returns to a receiver with choice bits `x`. -/
def otReceive (pairs : ℕ → V × V) (x : ℕ → Bool) : ℕ → Wire V :=
  fun j ↦ (x j, if x j then (pairs j).2 else (pairs j).1)

/-- The output label computed by the honest prover with witness `w`. -/
def proverLabel (H : ℕ → V → V) (C : Circuit) (out : ℕ) (w : ℕ → Bool)
    (msg : VerifierMsg V) : V :=
  ((eval H (otReceive msg.pairs w) C msg.material).getD out (false, 0)).2

/-- The prover's check after the opening: the material and the OT pairs are the ones the
opened seed determines. -/
def Verified (H : ℕ → V → V) (C : Circuit) (msg : VerifierMsg V) : Prop :=
  msg.material = (garble H msg.opening C).2 ∧
    ∀ j, msg.pairs j = (msg.opening.input j, msg.opening.input j + msg.opening.delta)

open Classical in
/-- The verifier's view of the honest prover with witness `w`: the opened label, or an abort. -/
noncomputable def view (H : ℕ → V → V) (C : Circuit) (out : ℕ) (w : ℕ → Bool)
    (msg : VerifierMsg V) : Option V :=
  if Verified H C msg then some (proverLabel H C out w msg) else none

open Classical in
/-- The simulator: it uses only the verifier's messages, not the witness. -/
noncomputable def sim (H : ℕ → V → V) (C : Circuit) (out : ℕ) (msg : VerifierMsg V) :
    Option V :=
  if Verified H C msg then
    some ((garble H msg.opening C).1.getD out 0 + msg.opening.delta)
  else none

/-- The messages of the honest verifier with seed `σ`. -/
def honestMsg (H : ℕ → V → V) (C : Circuit) (σ : Seed V) : VerifierMsg V :=
  ⟨(garble H σ C).2, fun j ↦ (σ.input j, σ.input j + σ.delta), σ⟩

/-- The verifier with seed `σ` accepts the opened label `Z`. -/
def Accepts (H : ℕ → V → V) (C : Circuit) (out : ℕ) (σ : Seed V) (Z : V) : Prop :=
  Z = (garble H σ C).1.getD out 0 + σ.delta

omit [Module (ZMod 2) V] in
/-- OT pairs of the form `(L, L + Δ)` hand out the active labels. -/
theorem otReceive_eq_activeInputs (σ : Seed V) (pairs : ℕ → V × V)
    (h : ∀ j, pairs j = (σ.input j, σ.input j + σ.delta)) (x : ℕ → Bool) :
    otReceive pairs x = activeInputs σ x := by
  funext j
  simp only [otReceive, activeInputs, h j]
  cases x j <;> simp

/-- After a successful check, the honest prover's label is the label of the plaintext output
value, computed from the opened seed. -/
theorem proverLabel_of_verified (H : ℕ → V → V) (C : Circuit) (out : ℕ) (w : ℕ → Bool)
    {msg : VerifierMsg V} (hv : Verified H C msg) :
    proverLabel H C out w msg =
      lab msg.opening.delta ((garble H msg.opening C).1.getD out 0)
        ((plain w C).getD out false) := by
  rw [proverLabel, hv.1, otReceive_eq_activeInputs msg.opening msg.pairs hv.2,
    eval_garble]

omit [Module (ZMod 2) V] in
theorem verified_honestMsg (H : ℕ → V → V) (C : Circuit) (σ : Seed V) :
    Verified H C (honestMsg H C σ) :=
  ⟨rfl, fun _ ↦ rfl⟩

/-- **Completeness.** With a witness, the honest prover passes its own check and convinces the
honest verifier, for every seed. -/
theorem complete (H : ℕ → V → V) (C : Circuit) (out : ℕ) (σ : Seed V) {w : ℕ → Bool}
    (hw : (plain w C).getD out false = true) :
    view H C out w (honestMsg H C σ) = some (proverLabel H C out w (honestMsg H C σ)) ∧
      Accepts H C out σ (proverLabel H C out w (honestMsg H C σ)) := by
  refine ⟨by simp [view, verified_honestMsg], ?_⟩
  rw [Accepts, proverLabel_of_verified H C out w (verified_honestMsg H C σ), hw, lab_true]
  rfl

/-- **Perfect zero knowledge against a malicious verifier.** For every message the verifier
sends, its view of the honest prover with any witness is the simulator's output, which does not
use the witness. -/
theorem zk (H : ℕ → V → V) (C : Circuit) (out : ℕ) {w : ℕ → Bool}
    (hw : (plain w C).getD out false = true) (msg : VerifierMsg V) :
    view H C out w msg = sim H C out msg := by
  unfold view sim
  split_ifs with hv
  · rw [proverLabel_of_verified H C out w hv, hw, lab_true]
  · rfl

/-- In particular, the verifier's view is the same for any two witnesses. -/
theorem view_witness_indep (H : ℕ → V → V) (C : Circuit) (out : ℕ) {w w' : ℕ → Bool}
    (hw : (plain w C).getD out false = true) (hw' : (plain w' C).getD out false = true)
    (msg : VerifierMsg V) :
    view H C out w msg = view H C out w' msg := by
  rw [zk H C out hw, zk H C out hw']

/-! ### Soundness -/

/-- A cheating prover: its OT choice bits, and the label it commits to as a function of the
material and of the labels it received. Ideal commitment makes the label independent of the
later opening. -/
structure Prover (V : Type*) where
  choice : ℕ → Bool
  respond : List (Material V) → (ℕ → V) → V

/-- The label the cheating prover commits to against the honest verifier with seed `σ`. -/
def Prover.label (H : ℕ → V → V) (C : Circuit) (σ : Seed V) (P : Prover V) : V :=
  P.respond (honestMsg H C σ).material
    (fun j ↦ (otReceive (honestMsg H C σ).pairs P.choice j).2)

/-- The authenticity game of the garbling: given the material and the active labels of an input
`x` of its choice, the adversary must output the *inactive* label of the output node, the label
of the value that `C` does not compute on `x`. -/
def AuthWin (H : ℕ → V → V) (C : Circuit) (out : ℕ) (σ : Seed V) (A : Prover V) : Prop :=
  A.respond (garble H σ C).2 (fun j ↦ (activeInputs σ A.choice j).2) =
    lab σ.delta ((garble H σ C).1.getD out 0) (!(plain A.choice C).getD out false)

omit [Module (ZMod 2) V] in
/-- **Soundness, by reduction to authenticity.** If no input satisfies `C`, then for every seed
the honest verifier accepts a cheating prover exactly when the prover wins the authenticity
game. A bound on the authenticity advantage over random seeds is therefore a bound on the
soundness error. -/
theorem sound (H : ℕ → V → V) (C : Circuit) (out : ℕ)
    (hC : ∀ x, (plain x C).getD out false = false) (σ : Seed V) (P : Prover V) :
    Accepts H C out σ (P.label H C σ) ↔ AuthWin H C out σ P := by
  rw [Accepts, AuthWin, Prover.label, hC, Bool.not_false, lab_true,
    otReceive_eq_activeInputs σ (honestMsg H C σ).pairs (fun _ ↦ rfl)]
  rfl

/-! ### Without the opening

In the warm-up of [JKO13, Sect. 3] the verifier never opens its garbling: the prover sends the
output label it computed, and the verifier compares it with the 1-label. Against an honest
verifier the prover's message is determined by the verifier's seed (`hvzk`). Against a malicious
verifier it is not: without the prover's check, the labels offered in the oblivious transfers
alone can reveal a witness bit (`no_check_leaks`), while the full protocol aborts on the same
message. -/

/-- The honest-verifier simulator of the variant without opening: the 1-label of the output
node, computed from the verifier's seed. -/
def hvSim (H : ℕ → V → V) (C : Circuit) (out : ℕ) (σ : Seed V) : V :=
  (garble H σ C).1.getD out 0 + σ.delta

/-- **Honest-verifier zero knowledge without opening.** Against the honest verifier with seed
`σ`, the label the prover sends is the simulator's output, which uses the seed and not the
witness. -/
theorem hvzk (H : ℕ → V → V) (C : Circuit) (out : ℕ) (σ : Seed V) {w : ℕ → Bool}
    (hw : (plain w C).getD out false = true) :
    proverLabel H C out w (honestMsg H C σ) = hvSim H C out σ := by
  rw [proverLabel_of_verified H C out w (verified_honestMsg H C σ), hw, lab_true]
  rfl

/-- The circuit `x₀ ⊕ x₁`, with output node `2`. -/
def xorCircuit : Circuit := [.input 0, .input 1, .xor 0 1]

/-- A malicious verifier message: honest material for `xorCircuit`, but the OT pairs `(0, a)` for
input `0` and `(0, 0)` for input `1`, which are not of the form `(L, L + Δ)` for a single `Δ`. -/
def leakMsg (a : V) : VerifierMsg V :=
  ⟨[.free, .free, .free], fun j ↦ if j = 0 then (0, a) else (0, 0), ⟨0, fun _ ↦ 0, fun _ ↦ 0⟩⟩

omit [Module (ZMod 2) V] in
/-- **Without the prover's check, zero knowledge fails.** The two witnesses `(1, 0)` and `(0, 1)`
of `x₀ ⊕ x₁` lead the prover, on `leakMsg a` with `a ≠ 0`, to the labels `a` and `0`, so a prover
that sends its label without checking reveals its first witness bit. The prover's check rejects
this message, so in the full protocol the view is an abort for both witnesses. -/
theorem no_check_leaks (H : ℕ → V → V) {a : V} (ha : a ≠ 0) :
    (plain (fun j ↦ decide (j = 0)) xorCircuit).getD 2 false = true ∧
      (plain (fun j ↦ decide (j = 1)) xorCircuit).getD 2 false = true ∧
      proverLabel H xorCircuit 2 (fun j ↦ decide (j = 0)) (leakMsg a) = a ∧
      proverLabel H xorCircuit 2 (fun j ↦ decide (j = 1)) (leakMsg a) = 0 ∧
      ¬ Verified H xorCircuit (leakMsg a) := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · simp [proverLabel, eval, evalAux, evalNode, otReceive, leakMsg, xorCircuit]
  · simp [proverLabel, eval, evalAux, evalNode, otReceive, leakMsg, xorCircuit]
  · rintro ⟨-, h⟩
    have h0 := h 0
    simp only [leakMsg, ↓reduceIte, Prod.mk.injEq, add_zero, true_and] at h0
    exact ha h0

end GcZk.Jko
