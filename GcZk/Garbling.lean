/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import Mathlib

/-!
# Privacy-free Free-XOR garbling

The privacy-free garbling scheme of [ZRE15, Sect. 6] (privacy-free in the sense of [FNO15]):
Free XOR [KS08] and, for the non-linear gate, the one-ciphertext evaluator half-gate of
[ZRE15, Sect. 3.1] written as a multiplexer, `mux(s, z, o) = z ⊕ (s ∧ (z ⊕ o))`.

Labels live in a `ZMod 2`-module `V` (for instance 128-bit strings with XOR). A wire with
zero-label `L` carries the label `L + b • Δ` for the bit `b` (`lab`). The evaluator knows every
wire value (privacy-free garbling).

## Main result

* `GcZk.eval_garble`: evaluating the garbled circuit on the active input labels gives, at every
  node, the plaintext value `v` and the label `L + v • Δ`. There is no hypothesis on the hash
  `H` or on `Δ`: correctness is pure algebra in characteristic 2.

## References

* [KS08] V. Kolesnikov, T. Schneider, *Improved garbled circuit: free XOR gates and
  applications*, ICALP 2008.
* [FNO15] T. K. Frederiksen, J. B. Nielsen, C. Orlandi, *Privacy-free garbled circuits with
  applications to efficient zero-knowledge*, Eurocrypt 2015.
* [ZRE15] S. Zahur, M. Rosulek, D. Evans, *Two halves make a whole*, Eurocrypt 2015.
-/

namespace GcZk

/-- A node of a Boolean circuit. Operands are indices of earlier nodes; an index that is not
smaller than the node's own position reads the default wire. -/
inductive Node
  | input (j : ℕ)
  | const (b : Bool)
  | xor (a b : ℕ)
  /-- `mux s z o` is `o` if the value of `s` is `true`, and `z` otherwise. -/
  | mux (s z o : ℕ)
  deriving DecidableEq, Repr

/-- A circuit is the list of its nodes, in evaluation order. -/
abbrev Circuit := List Node

/-! ### Plaintext evaluation -/

/-- The value of one node, given the values `vs` of the earlier nodes. -/
def plainNode (x : ℕ → Bool) (vs : List Bool) : Node → Bool
  | .input j => x j
  | .const b => b
  | .xor a b => vs.getD a false ^^ vs.getD b false
  | .mux s z o => if vs.getD s false then vs.getD o false else vs.getD z false

/-- Plaintext evaluation of the nodes `C` after the already computed values `vs`. -/
def plainAux (x : ℕ → Bool) : Circuit → List Bool → List Bool
  | [], vs => vs
  | n :: ns, vs => plainAux x ns (vs ++ [plainNode x vs n])

/-- The values of all the nodes of `C` on the input `x`. -/
def plain (x : ℕ → Bool) (C : Circuit) : List Bool := plainAux x C []

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_eq_zero' (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem two_nsmul_eq_zero' (v : V) : 2 • v = 0 := by
  rw [two_nsmul, add_self_eq_zero']

theorem two_zsmul_eq_zero' (v : V) : (2 : ℤ) • v = 0 := by
  rw [two_zsmul, add_self_eq_zero']

/-- The label of the bit `b` on a wire with zero-label `L`. -/
def lab (Δ L : V) (b : Bool) : V := L + if b then Δ else 0

omit [Module (ZMod 2) V] in
@[simp] theorem lab_false (Δ L : V) : lab Δ L false = L := by simp [lab]

omit [Module (ZMod 2) V] in
@[simp] theorem lab_true (Δ L : V) : lab Δ L true = L + Δ := by simp [lab]

/-! ### Garbling -/

/-- The garbler's randomness: the global offset and the zero-labels of the inputs and of the
constants (the latter indexed by node position). -/
structure Seed (V : Type*) where
  delta : V
  input : ℕ → V
  const : ℕ → V

/-- The garbled material of one node. -/
inductive Material (V : Type*)
  | free
  /-- A constant node publishes its active label. -/
  | const (L : V)
  /-- A multiplexer publishes one ciphertext. -/
  | mux (T : V)

/-- Garbling of one node at position `bs.length`, given the zero-labels `bs` of the earlier
nodes: its zero-label and its material. `H i L` is the hash of the label `L` at gate `i`. -/
def garbleNode (H : ℕ → V → V) (σ : Seed V) (bs : List V) : Node → V × Material V
  | .input j => (σ.input j, .free)
  | .const b => (σ.const bs.length, .const (lab σ.delta (σ.const bs.length) b))
  | .xor a b => (bs.getD a 0 + bs.getD b 0, .free)
  | .mux s z o =>
    (H bs.length (bs.getD s 0) + bs.getD z 0,
      .mux (H bs.length (bs.getD s 0) + H bs.length (bs.getD s 0 + σ.delta) +
        bs.getD z 0 + bs.getD o 0))

/-- Garbling of the nodes `C` after the zero-labels `bs`: all the zero-labels, and the material
of the nodes of `C`. -/
def garbleAux (H : ℕ → V → V) (σ : Seed V) : Circuit → List V → List V × List (Material V)
  | [], bs => (bs, [])
  | n :: ns, bs =>
    ((garbleAux H σ ns (bs ++ [(garbleNode H σ bs n).1])).1,
      (garbleNode H σ bs n).2 :: (garbleAux H σ ns (bs ++ [(garbleNode H σ bs n).1])).2)

/-- The garbling of `C`: the zero-labels of all the nodes, and the material. -/
def garble (H : ℕ → V → V) (σ : Seed V) (C : Circuit) : List V × List (Material V) :=
  garbleAux H σ C []

/-! ### Evaluation -/

/-- An evaluated wire: its value and its active label. -/
abbrev Wire (V : Type*) := Bool × V

/-- Evaluation of one node at position `ws.length`, given the evaluated earlier nodes `ws` and
the input wires `inp`. -/
def evalNode (H : ℕ → V → V) (inp : ℕ → Wire V) (ws : List (Wire V)) :
    Node → Material V → Wire V
  | .input j, _ => inp j
  | .const b, .const L => (b, L)
  | .xor a b, _ => ((ws.getD a (false, 0)).1 ^^ (ws.getD b (false, 0)).1,
      (ws.getD a (false, 0)).2 + (ws.getD b (false, 0)).2)
  | .mux s z o, .mux T =>
    if (ws.getD s (false, 0)).1 then
      ((ws.getD o (false, 0)).1,
        H ws.length (ws.getD s (false, 0)).2 + (ws.getD o (false, 0)).2 + T)
    else
      ((ws.getD z (false, 0)).1, H ws.length (ws.getD s (false, 0)).2 + (ws.getD z (false, 0)).2)
  | _, _ => (false, 0)

/-- Evaluation of the nodes `C`, with material `ms`, after the evaluated wires `ws`. -/
def evalAux (H : ℕ → V → V) (inp : ℕ → Wire V) :
    Circuit → List (Material V) → List (Wire V) → List (Wire V)
  | n :: ns, m :: ms, ws => evalAux H inp ns ms (ws ++ [evalNode H inp ws n m])
  | _, _, ws => ws

/-- Evaluation of the circuit `C` with material `ms` on the input wires `inp`. -/
def eval (H : ℕ → V → V) (inp : ℕ → Wire V) (C : Circuit) (ms : List (Material V)) :
    List (Wire V) :=
  evalAux H inp C ms []

/-- The active input wires for the input `x`. -/
def activeInputs (σ : Seed V) (x : ℕ → Bool) : ℕ → Wire V :=
  fun j ↦ (x j, lab σ.delta (σ.input j) (x j))

/-! ### Correctness -/

theorem getD_snoc {α : Type*} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  rcases lt_trichotomy i l.length with h | rfl | h
  · simp [h, List.getElem?_append_left h]
  · simp
  · simp [h.ne', h.not_gt, List.getElem?_eq_none (by simp; omega : (l ++ [a]).length ≤ i)]

/-- The invariant of evaluation: each evaluated wire carries the plaintext value and the
label of that value. -/
def Good (Δ : V) (bs : List V) (vs : List Bool) (ws : List (Wire V)) : Prop :=
  vs.length = bs.length ∧ ws.length = bs.length ∧
    ∀ i, ws.getD i (false, 0) = (vs.getD i false, lab Δ (bs.getD i 0) (vs.getD i false))

omit [Module (ZMod 2) V] in
theorem good_nil (Δ : V) : Good Δ [] [] [] := by
  simp [Good, lab]

theorem good_snoc (H : ℕ → V → V) (σ : Seed V) (x : ℕ → Bool) (n : Node) {bs : List V}
    {vs : List Bool} {ws : List (Wire V)} (h : Good σ.delta bs vs ws) :
    Good σ.delta (bs ++ [(garbleNode H σ bs n).1]) (vs ++ [plainNode x vs n])
      (ws ++ [evalNode H (activeInputs σ x) ws n (garbleNode H σ bs n).2]) := by
  obtain ⟨hv, hw, hg⟩ := h
  refine ⟨by simp [hv], by simp [hw], fun i ↦ ?_⟩
  simp only [getD_snoc, hv, hw]
  split_ifs with h1 h2
  · exact hg i
  · -- the new node
    cases n with
    | input j => simp [garbleNode, evalNode, plainNode, activeInputs]
    | const b => simp [garbleNode, evalNode, plainNode]
    | xor a b =>
      simp only [garbleNode, evalNode, plainNode, hg a, hg b]
      cases vs.getD a false <;> cases vs.getD b false <;>
        simp only [lab_false, lab_true, Bool.xor_false, Bool.xor_true, Bool.not_false,
          Bool.not_true, Prod.mk.injEq, true_and] <;>
        first
        | (abel; done)
        | (abel_nf; simp only [two_zsmul_eq_zero', zero_add])
    | mux s z o =>
      simp only [garbleNode, evalNode, plainNode, hg s, hw]
      cases hs : vs.getD s false
      · simp only [lab_false, Bool.false_eq_true, ↓reduceIte, hg z, Prod.mk.injEq, true_and]
        unfold lab; abel
      · simp only [lab_true, ↓reduceIte, hg o, Prod.mk.injEq, true_and]
        unfold lab
        rw [show H bs.length (bs.getD s 0 + σ.delta) + (bs.getD o 0 + if vs.getD o false then
              σ.delta else 0) + (H bs.length (bs.getD s 0) + H bs.length (bs.getD s 0 + σ.delta) +
              bs.getD z 0 + bs.getD o 0) =
            (H bs.length (bs.getD s 0 + σ.delta) + H bs.length (bs.getD s 0 + σ.delta)) +
              (bs.getD o 0 + bs.getD o 0) +
              (H bs.length (bs.getD s 0) + bs.getD z 0 + if vs.getD o false then σ.delta else 0)
            by abel]
        simp only [add_self_eq_zero', zero_add]
  · simp [lab]

theorem good_aux (H : ℕ → V → V) (σ : Seed V) (x : ℕ → Bool) (C : Circuit) :
    ∀ {bs : List V} {vs : List Bool} {ws : List (Wire V)}, Good σ.delta bs vs ws →
      Good σ.delta (garbleAux H σ C bs).1 (plainAux x C vs)
        (evalAux H (activeInputs σ x) C (garbleAux H σ C bs).2 ws) := by
  induction C with
  | nil => intro bs vs ws h; simpa [garbleAux, plainAux, evalAux] using h
  | cons n ns ih =>
    intro bs vs ws h
    simpa only [garbleAux, plainAux, evalAux] using ih (good_snoc H σ x n h)

/-- **Correctness of privacy-free Free-XOR garbling.** Evaluating the garbled circuit on the
active input labels gives, at every node `i`, the plaintext value `v` of the node and the label
`L + v • Δ`, where `L` is the node's zero-label. No hypothesis on `H` or `Δ` is needed. -/
theorem eval_garble (H : ℕ → V → V) (σ : Seed V) (x : ℕ → Bool) (C : Circuit) (i : ℕ) :
    (eval H (activeInputs σ x) C (garble H σ C).2).getD i (false, 0) =
      ((plain x C).getD i false,
        lab σ.delta ((garble H σ C).1.getD i 0) ((plain x C).getD i false)) :=
  (good_aux H σ x C (good_nil σ.delta)).2.2 i

end GcZk
