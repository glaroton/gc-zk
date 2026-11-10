/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.RandomOracle

/-!
# Authenticity of the real garbling in the random oracle model

`GcZk.RO.rom_bound` takes the active labels of the inputs and of the constants as fixed
parameters. Here the garbler samples everything as in the real scheme: the offset `Δ ≠ 0`, the
hash `H`, and the zero-labels of the `k` inputs and of the constants. The adversary receives the
material of `GcZk.garble` and the active labels of its input `x`, makes `q` adaptive queries to
`H`, and wins if it outputs the inactive output label.

## Main result

* `GcZk.Sec.garble_rom_bound`: the winning tuples `(Δ, H, L_in, L_const)` number at most
  `(q + 1)` times the tuples `(H, L_in, L_const)`, summed over `Δ ≠ 0`. So the success
  probability is at most `(q + 1) / (|V| - 1)`.

The proof reparametrizes by the active labels: for fixed `Δ`, the maps `L ↦ L + x Δ` (inputs)
and `L ↦ L + b Δ` (constants) are bijections, and they turn the real game into the game of
`GcZk.RO.rom_bound` with fixed active labels.
-/

namespace GcZk

open RO Auth

variable {V : Type*} [AddCommGroup V]

namespace Auth

/-- The ideal garbler reads the constant labels only at `(i, b)` where node `i` is `const b`. -/
theorem idealAux_congr_const (H : ℕ → V → V) (inp : ℕ → Wire V) (pad : ℕ → V → Bool → V) :
    ∀ (D : Circuit) {Ac Ac' : ℕ → Bool → V} {ws : List (Wire V)},
      (∀ k b, D.getD k (.input 0) = .const b → Ac' (ws.length + k) b = Ac (ws.length + k) b) →
        idealAux H inp Ac' pad D ws = idealAux H inp Ac pad D ws := by
  intro D
  induction D with
  | nil => intro _ _ _ _; rfl
  | cons n ns ih =>
    intro Ac Ac' ws h
    have hn : idealNode H Ac' pad ws n = idealNode H Ac pad ws n := by
      cases n with
      | const b =>
        have := h 0 b (by simp)
        simp only [Nat.add_zero] at this
        simp [idealNode, this]
      | _ => rfl
    simp only [idealAux, hn]
    refine congrArg _ (ih fun k b hk ↦ ?_)
    rw [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_comm 1 k]
    exact h (k + 1) b (by simpa using hk)

end Auth

namespace Sec

variable [Module (ZMod 2) V]

/-- A finite family of labels, extended by `0`. -/
def extF {m : ℕ} (L : Fin m → V) : ℕ → V := fun i ↦ if h : i < m then L ⟨i, h⟩ else 0

/-- The real seed: offset `Δ`, zero-labels of the `k` inputs and of the constants. -/
def seedOf (C : Circuit) (k : ℕ) (Δ : V) (Lin : Fin k → V) (Lc : Fin C.length → V) : Seed V :=
  ⟨Δ, extF Lin, extF Lc⟩

/-- The active labels of the inputs for `x`. -/
def activeIn (k : ℕ) (x : ℕ → Bool) (Δ : V) (Lin : Fin k → V) : Fin k → V :=
  fun j ↦ Lin j + if x j then Δ else 0

/-- The shift of the constant labels: `Δ` at the constants `1`. -/
def shiftC (C : Circuit) (Δ : V) : Fin C.length → V :=
  fun i ↦ if C.getD i (.input 0) = .const true then Δ else 0

/-- The active labels of the constants. -/
def constLab (C : Circuit) (Δ : V) (Lc : Fin C.length → V) : Fin C.length → V :=
  fun i ↦ Lc i + shiftC C Δ i

/-- The input wires seen by the evaluator, from the active labels. -/
def inpOf (k : ℕ) (x : ℕ → Bool) (A : Fin k → V) : ℕ → Wire V := fun j ↦ (x j, extF A j)

/-- Constant labels that do not depend on the bit. -/
def acOf {m : ℕ} (B : Fin m → V) : ℕ → Bool → V := fun i _ ↦ extF B i

variable (C : Circuit) (out q k : ℕ) (x : ℕ → Bool) (AA : (Fin k → V) → QAdv V)

/-- The material of the real garbling. -/
def gMat (Δ : V) (H : Fin C.length → V → V) (Lin : Fin k → V) (Lc : Fin C.length → V) :
    List (Material V) :=
  (garble (extH H) (seedOf C k Δ Lin Lc) C).2

/-- The adversary, which sees the material and the active labels of its input, wins the real
game: it outputs the inactive output label. -/
def GarbleWin (Δ : V) (H : Fin C.length → V → V) (Lin : Fin k → V) (Lc : Fin C.length → V) :
    Prop :=
  (AA (activeIn k x Δ Lin)).guess (gMat C k Δ H Lin Lc)
      (answers (extH H) (AA (activeIn k x Δ Lin)) (gMat C k Δ H Lin Lc) q) =
    activeOut (extH H) (activeInputs (seedOf C k Δ Lin Lc) x) C out (gMat C k Δ H Lin Lc) + Δ

omit [Module (ZMod 2) V] in
theorem activeInputs_seedOf (hx : ∀ j, k ≤ j → x j = false) (Δ : V) (Lin : Fin k → V)
    (Lc : Fin C.length → V) :
    activeInputs (seedOf C k Δ Lin Lc) x = inpOf k x (activeIn k x Δ Lin) := by
  funext j
  simp only [activeInputs, inpOf, seedOf, extF, activeIn, lab]
  by_cases hj : j < k
  · simp [hj]
  · simp [hj, hx j (by omega)]

theorem gMat_eq (Δ : V) (H : Fin C.length → V → V) (Lin : Fin k → V) (Lc : Fin C.length → V)
    (hx : ∀ j, k ≤ j → x j = false) :
    gMat C k Δ H Lin Lc =
      realMat (inpOf k x (activeIn k x Δ Lin)) (acOf (constLab C Δ Lc)) C Δ (extH H) := by
  rw [gMat, garble_eq_idealMaterial (extH H) (seedOf C k Δ Lin Lc) x C,
    activeInputs_seedOf C k x hx, realMat, idealMaterial, idealMaterial]
  refine (idealAux_congr_const _ _ _ C fun i b hi ↦ ?_).symm
  have hlt : i < C.length := by
    by_contra h
    rw [List.getD_eq_default _ _ (by omega)] at hi
    cases hi
  simp only [List.length_nil, Nat.zero_add, acOf, extF, dite_eq_left hlt, constLab, shiftC,
    hi, realAc, seedOf, lab]
  cases b <;> simp

theorem garbleWin_iff (hx : ∀ j, k ≤ j → x j = false) (Δ : V) (H : Fin C.length → V → V)
    (Lin : Fin k → V) (Lc : Fin C.length → V) :
    GarbleWin C out q k x AA Δ H Lin Lc ↔
      RealWin (inpOf k x (activeIn k x Δ Lin)) (acOf (constLab C Δ Lc)) C out q
        (AA (activeIn k x Δ Lin)) Δ H := by
  rw [GarbleWin, RealWin, gMat_eq C k x Δ H Lin Lc hx, activeInputs_seedOf C k x hx]

variable [Fintype V]

open Classical in
/-- **Authenticity of the real garbling in the random oracle model.** The garbler samples
`Δ ≠ 0`, the hash and the zero-labels of the inputs and of the constants. An adversary that sees
the material and the active labels of its input `x`, and makes `q` adaptive hash queries, outputs
the inactive output label for at most `(q + 1)` times all `(H, L_in, L_const)`, summed over `Δ`.
With uniform choices its success probability is at most `(q + 1) / (|V| - 1)`. The inputs used
are `j < k`; `x` is `0` on the others. -/
theorem garble_rom_bound (hx : ∀ j, k ≤ j → x j = false) :
    ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V,
      (Finset.univ.filter fun H : Fin C.length → V → V ↦
        GarbleWin C out q k x AA Δ H Lin Lc).card ≤
    (q + 1) * Fintype.card (Fin C.length → V → V) * Fintype.card (Fin k → V) *
      Fintype.card (Fin C.length → V) := by
  set g : V → (Fin k → V) → (Fin C.length → V) → ℕ := fun Δ A B ↦
    (Finset.univ.filter fun H : Fin C.length → V → V ↦
      RealWin (inpOf k x A) (acOf B) C out q (AA A) Δ H).card
  -- Reparametrize by the active labels, for each offset.
  have reparam : ∀ Δ : V, ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V,
      (Finset.univ.filter fun H : Fin C.length → V → V ↦
        GarbleWin C out q k x AA Δ H Lin Lc).card = ∑ A, ∑ B, g Δ A B := by
    intro Δ
    refine Fintype.sum_equiv (Equiv.addRight fun j : Fin k ↦ if x j then Δ else 0) _ _
      fun Lin ↦ ?_
    refine Fintype.sum_equiv (Equiv.addRight (shiftC C Δ)) _ _ fun Lc ↦ ?_
    simp only [g]
    congr 1
    ext H
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, garbleWin_iff C out q k x AA hx]
    rfl
  rw [Finset.sum_congr rfl fun Δ _ ↦ reparam Δ, Finset.sum_comm]
  calc ∑ A : Fin k → V, ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), ∑ B, g Δ A B
      = ∑ A : Fin k → V, ∑ B : Fin C.length → V,
          ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), g Δ A B :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ ≤ ∑ _A : Fin k → V, ∑ _B : Fin C.length → V,
          (q + 1) * Fintype.card (Fin C.length → V → V) :=
        Finset.sum_le_sum fun A _ ↦ Finset.sum_le_sum fun B _ ↦
          rom_bound (inpOf k x A) (acOf B) C out q (AA A)
    _ = _ := by simp [Finset.card_univ]; ring

end Sec

end GcZk
