/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.PVW

/-!
# End-to-end soundness with the PVW oblivious transfer in messy mode

The ideal OT of `GcZk.E2E` is replaced by the dual-mode OT of [PVW08] in messy mode
(`GcZk.PVW`). The common string is fixed and messy. A cheating prover sends a key `pk_j` for every
input `j`; the verifier rejects if some `pk_j` has first component `0`, and otherwise sends, for
each input and each branch `b`, the encryption of the label `L_j + b Δ` with uniform coins. As in
the open-all phase of `F_COT` [JKO13, Fig. 3], at the opening the prover sees the seed and also all
the coins of the OT. The rest is as in `GcZk.E2E`.

## Main result

* `GcZk.PVW.prob_accept_le`: the verifier accepts with probability at most
  `(n₁ + 1) / (|V| - 1) + (n₁² + n₂ + 1) / |D|`, the bound of `GcZk.E2E.prob_accept_le`.

## Proof

The trapdoor extracts from `pk_j` a choice bit `ext pk_j`, and the other branch is messy
(`GcZk.PVW.messy_of_ext`). On the messy branch, encryption is a bijection of the coins, so we can
sample the ciphertext uniformly and recover the coins from it once the label is known, that is,
after the opening (`coinsEquiv`). For each value of the messy ciphertexts and of the coins of the
other branch, the prover is then a prover of `GcZk.E2E` with OT input `ext pk` (`toE2E`): it can
compute everything it sees from the active labels before the opening and from the seed after it.
Averaging the bound of `GcZk.E2E.prob_accept_le` over these values gives the result.

The reduction is exact, with no computational step: in messy mode the sender's security is
statistical (perfect here), and soundness rests on authenticity and binding only. Zero knowledge
with this OT is in `GcZk.PVWZK` and `GcZk.PVWDDH`, not in this file: in messy mode the receiver's
security is computational, under DDH [PVW08, Theorem 4.1].

## References

* [PVW08] C. Peikert, V. Vaikuntanathan, B. Waters, *A framework for efficient and composable
  oblivious transfer*, CRYPTO 2008.
* [JKO13] M. Jawurek, F. Kerschbaum, C. Orlandi, *Zero-knowledge using garbled circuits: how to
  prove non-algebraic statements efficiently*, CCS 2013.
-/

namespace GcZk.PVW

open RO Sec GcZk.E2E

variable {q : ℕ} {Gp : Type*} [AddCommGroup Gp] [Module (ZMod q) Gp]
variable {V R D : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The ciphertexts of both branches of every input. -/
abbrev Cts (k : ℕ) (Gp : Type*) := Fin k → Bool → Gp × Gp

/-- The coins of both branches of every input. -/
abbrev Coins (k q : ℕ) := Fin k → Bool → ZMod q × ZMod q

/-- A cheating prover with `k` OT inputs against the PVW OT: its keys, then the steps of
`GcZk.E2E.PProver`, seeing the ciphertexts instead of the active labels and, after the opening,
the coins of the OT. -/
structure Prover (k q : ℕ) (V R D Gp : Type*) where
  pk : Fin k → Gp × Gp
  n₁ : ℕ
  n₂ : ℕ
  step₁ : List (Material V) → Cts k Gp → List (V × D) → (ℕ × V) × (V × R)
  commit : List (Material V) → Cts k Gp → List (V × D) → D
  step₂ : List (Material V) → Cts k Gp → List (V × D) → Seed V → Coins k q → List (V × D) →
    (ℕ × V) × (V × R)
  opened : List (Material V) → Cts k Gp → List (V × D) → Seed V → Coins k q → List (V × D) →
    V × R

variable (C : Circuit) (out k : ℕ) (c : Crs Gp) (ι : V → Gp) (P : Prover k q V R D Gp)

/-- The verifier's ciphertexts: the label `L_j + b Δ`, encoded in `Gp` by `ι`, on branch `b`. -/
def cts (Δ : V) (Lin : Fin k → V) (rnd : Coins k q) : Cts k Gp :=
  fun j b ↦ enc c (P.pk j) b (ι (Lin j + if b then Δ else 0)) (rnd j b)

/-- The verifier accepts the cheating prover: every key passes the check `pk₁ ≠ 0`, and the
prover opens its commitment to the target label. -/
def RealAccept (Δ : V) (H : Fin C.length → V → V) (Lin : Fin k → V) (Lc : Fin C.length → V)
    (G : V × R → D) (rnd : Coins k q) : Prop :=
  (∀ j, (P.pk j).1 ≠ 0) ∧
    let M := gMat C k Δ H Lin Lc
    let T := cts k c ι P Δ Lin rnd
    let σ := seedOf C k Δ Lin Lc
    let c₁ := cans (oH C H) G (P.step₁ M T) P.n₁
    let c₂ := cans (oH C H) G (P.step₂ M T c₁ σ rnd) P.n₂
    (P.opened M T c₁ σ rnd c₂).1 = target C out H σ ∧
      G (P.opened M T c₁ σ rnd c₂) = P.commit M T c₁

/-! ### The reduction -/

section Reduction

variable [Fact q.Prime] [Fintype Gp] [DecidableEq Gp] (hcard : Fintype.card Gp = q)
  (t : Bool → ZMod q) (hc : c.Messy t) (hpk : ∀ j, (P.pk j).1 ≠ 0)

/-- The extracted OT input. -/
def xOf : ℕ → Bool := fun j ↦ if h : j < k then ext t (P.pk ⟨j, h⟩) else false

include hcard hc hpk in
/-- Encryption on the messy branch of `pk_j`, as an equivalence between coins and ciphertexts. -/
noncomputable def E (j : Fin k) (m : Gp) : ZMod q × ZMod q ≃ Gp × Gp :=
  Equiv.ofBijective _
    (enc_bijective hcard c (b := !ext t (P.pk j)) (hc.g_ne _) (hc.h_eq _)
      (messy_of_ext c hc (hpk j)) m)

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem E_apply (j : Fin k) (m : Gp) (st : ZMod q × ZMod q) :
    E k c P hcard t hc hpk j m st = enc c (P.pk j) (!ext t (P.pk j)) m st := rfl

/-- The coins, from the ciphertexts of the messy branches and the coins of the other branches:
on the messy branch the coins are those that encrypt the label to the given ciphertext. -/
noncomputable def coinsOf (Δ : V) (Lin : Fin k → V)
    (cr : (Fin k → Gp × Gp) × (Fin k → ZMod q × ZMod q)) : Coins k q :=
  fun j b ↦ if b = ext t (P.pk j) then cr.2 j
    else (E k c P hcard t hc hpk j (ι (Lin j + if b then Δ else 0))).symm (cr.1 j)

theorem eq_not_of_ne {a b : Bool} (h : ¬b = a) : b = !a := by
  cases a <;> cases b <;> simp_all

/-- **Sampling the messy ciphertext instead of the coins.** -/
noncomputable def coinsEquiv (Δ : V) (Lin : Fin k → V) :
    (Fin k → Gp × Gp) × (Fin k → ZMod q × ZMod q) ≃ Coins k q where
  toFun := coinsOf k c ι P hcard t hc hpk Δ Lin
  invFun rnd := (fun j ↦ E k c P hcard t hc hpk j
      (ι (Lin j + if !ext t (P.pk j) then Δ else 0)) (rnd j (!ext t (P.pk j))),
    fun j ↦ rnd j (ext t (P.pk j)))
  left_inv cr := by
    ext j <;> simp [coinsOf]
  right_inv rnd := by
    funext j b
    by_cases hb : b = ext t (P.pk j)
    · subst hb; simp [coinsOf]
    · obtain rfl := eq_not_of_ne hb
      simp [coinsOf]

/-- The ciphertexts that the reduction shows: on the extracted branch, the encryption of the active
label; on the other, the sampled ciphertext. -/
def ctsOf (A : Fin k → V) (cr : (Fin k → Gp × Gp) × (Fin k → ZMod q × ZMod q)) : Cts k Gp :=
  fun j b ↦ if b = ext t (P.pk j) then enc c (P.pk j) b (ι (A j)) (cr.2 j) else cr.1 j

/-- **The reduction.** For fixed sampled ciphertexts and coins, the prover as a prover of
`GcZk.E2E` with OT input `ext pk`. -/
noncomputable def toE2E (cr : (Fin k → Gp × Gp) × (Fin k → ZMod q × ZMod q)) :
    PProver k V R D where
  x := xOf k P t
  n₁ := P.n₁
  n₂ := P.n₂
  step₁ M A := P.step₁ M (ctsOf k c ι P t A cr)
  commit M A := P.commit M (ctsOf k c ι P t A cr)
  step₂ M A a σ := P.step₂ M (ctsOf k c ι P t A cr) a σ
    (coinsOf k c ι P hcard t hc hpk σ.delta (fun j ↦ σ.input j) cr)
  opened M A a σ := P.opened M (ctsOf k c ι P t A cr) a σ
    (coinsOf k c ι P hcard t hc hpk σ.delta (fun j ↦ σ.input j) cr)

omit [Module (ZMod 2) V] in
theorem cts_coinsOf (Δ : V) (Lin : Fin k → V) (cr) :
    cts k c ι P Δ Lin (coinsOf k c ι P hcard t hc hpk Δ Lin cr) =
      ctsOf k c ι P t (activeIn k (xOf k P t) Δ Lin) cr := by
  funext j b
  have hx : xOf k P t j = ext t (P.pk j) := by simp [xOf]
  by_cases hb : b = ext t (P.pk j)
  · subst hb; simp [cts, ctsOf, coinsOf, activeIn, hx]
  · obtain rfl := eq_not_of_ne hb
    simp only [cts, ctsOf, coinsOf, hb, ↓reduceIte]
    rw [← E_apply k c P hcard t hc hpk, Equiv.apply_symm_apply]

omit [Module (ZMod 2) V] in
theorem realAccept_iff (Δ : V) (H : Fin C.length → V → V) (Lin : Fin k → V)
    (Lc : Fin C.length → V) (G : V × R → D) (cr) :
    RealAccept C out k c ι P Δ H Lin Lc G (coinsOf k c ι P hcard t hc hpk Δ Lin cr) ↔
      E2E.RealAccept C out k (toE2E k c ι P hcard t hc hpk cr) Δ H Lin Lc G := by
  have hσ : coinsOf k c ι P hcard t hc hpk (seedOf C k Δ Lin Lc).delta
      (fun j ↦ (seedOf C k Δ Lin Lc).input j) cr = coinsOf k c ι P hcard t hc hpk Δ Lin cr := by
    simp [seedOf, extF]
  simp only [RealAccept, E2E.RealAccept, toE2E, cts_coinsOf, hσ]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hpk, h⟩⟩

variable [Fintype V] [Fintype R] [Fintype D]

omit [Module (ZMod 2) V] in
open Classical in
theorem sum_coins (Δ : V) (H : Fin C.length → V → V) (Lin : Fin k → V)
    (Lc : Fin C.length → V) :
    ∑ rnd : Coins k q,
        (Finset.univ.filter fun G : V × R → D ↦ RealAccept C out k c ι P Δ H Lin Lc G rnd).card =
      ∑ cr : (Fin k → Gp × Gp) × (Fin k → ZMod q × ZMod q),
        (Finset.univ.filter fun G : V × R → D ↦
          E2E.RealAccept C out k (toE2E k c ι P hcard t hc hpk cr) Δ H Lin Lc G).card := by
  rw [← (coinsEquiv k c ι P hcard t hc hpk Δ Lin).sum_comp]
  refine Finset.sum_congr rfl fun cr _ ↦ ?_
  congr 1
  ext G
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact realAccept_iff C out k c ι P hcard t hc hpk Δ H Lin Lc G cr

omit [DecidableEq Gp] in
include hcard hc in
open Classical in
/-- **End-to-end soundness with the PVW OT in messy mode.** For a messy common string, with the
seed, the hash, the commitment oracle and the coins of the OT uniform, the verifier accepts a
cheating prover for an unsatisfiable circuit with probability at most
`(n₁ + 1) / (|V| - 1) + (n₁² + n₂ + 1) / |D|`. -/
theorem prob_accept_le [Nontrivial V] [Nonempty D]
    (hC : ∀ x : ℕ → Bool, (plain x C).getD out false = false) :
    ((∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V,
      ∑ H : Fin C.length → V → V, ∑ rnd : Coins k q,
        (Finset.univ.filter fun G : V × R → D ↦
          RealAccept C out k c ι P Δ H Lin Lc G rnd).card : ℕ) : ℝ) /
      (Fintype.card (Coins k q) * ((Finset.univ.filter (· ≠ (0 : V))).card *
        Fintype.card (Fin k → V) * Fintype.card (Fin C.length → V) *
        Fintype.card (Fin C.length → V → V) * Fintype.card (V × R → D))) ≤
      ((P.n₁ + 1 : ℕ) : ℝ) / (Fintype.card V - 1) +
        ((P.n₁ * P.n₁ + P.n₂ + 1 : ℕ) : ℝ) / Fintype.card D := by
  set B : ℝ := ((P.n₁ + 1 : ℕ) : ℝ) / (Fintype.card V - 1) +
    ((P.n₁ * P.n₁ + P.n₂ + 1 : ℕ) : ℝ) / Fintype.card D
  have hV : (1 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.one_lt_card
  have hB : 0 ≤ B := by
    have : (0 : ℝ) < Fintype.card V - 1 := by linarith
    positivity
  by_cases hpk : ∀ j, (P.pk j).1 ≠ 0
  swap
  · have h0 : ∀ Δ H Lin Lc G rnd, ¬RealAccept C out k c ι P Δ H Lin Lc G rnd :=
      fun _ _ _ _ _ _ h ↦ hpk h.1
    have hz : ∀ Δ H Lin Lc rnd, (Finset.univ.filter fun G : V × R → D ↦
        RealAccept C out k c ι P Δ H Lin Lc G rnd).card = 0 := fun _ _ _ _ _ ↦ by simp [h0]
    simp only [hz, Finset.sum_const_zero, Nat.cast_zero, zero_div]
    exact hB
  have hS : ((Finset.univ.filter (· ≠ (0 : V))).card : ℝ) = Fintype.card V - 1 := by
    rw [Finset.filter_ne' Finset.univ (0 : V), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Nat.cast_sub Fintype.card_pos]
    simp
  set S := Finset.univ.filter (· ≠ (0 : V))
  set N := (S.card : ℝ) * Fintype.card (Fin k → V) * Fintype.card (Fin C.length → V) *
    Fintype.card (Fin C.length → V → V) * Fintype.card (V × R → D)
  have hN : 0 < N := by
    have : (0 : ℝ) < S.card := by rw [hS]; linarith
    have := Fintype.card_pos (α := Fin k → V)
    have := Fintype.card_pos (α := Fin C.length → V)
    have := Fintype.card_pos (α := Fin C.length → V → V)
    have := Fintype.card_pos (α := V × R → D)
    positivity
  set T : (Fin k → Gp × Gp) × (Fin k → ZMod q × ZMod q) → ℕ := fun cr ↦
    ∑ Δ ∈ S, ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V, ∑ H : Fin C.length → V → V,
      (Finset.univ.filter fun G : V × R → D ↦
        E2E.RealAccept C out k (toE2E k c ι P hcard t hc hpk cr) Δ H Lin Lc G).card
  have hsum : (∑ Δ ∈ S, ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V,
      ∑ H : Fin C.length → V → V, ∑ rnd : Coins k q,
        (Finset.univ.filter fun G : V × R → D ↦
          RealAccept C out k c ι P Δ H Lin Lc G rnd).card) = ∑ cr, T cr := by
    simp only [T, sum_coins C out k c ι P hcard t hc hpk]
    symm
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ ↦ ?_)
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ ↦ ?_)
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ ↦ ?_)
    exact Finset.sum_comm
  have hT : ∀ cr, (T cr : ℝ) ≤ B * N := fun cr ↦ by
    have h := E2E.prob_accept_le C out k (toE2E k c ι P hcard t hc hpk cr) (hC _)
      (fun j hj ↦ by simp [toE2E, xOf, Nat.not_lt.2 hj])
    exact (div_le_iff₀ hN).1 h
  have hcr : Fintype.card ((Fin k → Gp × Gp) × (Fin k → ZMod q × ZMod q)) =
      Fintype.card (Coins k q) :=
    Fintype.card_congr (coinsEquiv k c ι P hcard t hc hpk 0 0)
  have hpos : (0 : ℝ) < Fintype.card (Coins k q) := by exact_mod_cast Fintype.card_pos
  rw [hsum, div_le_iff₀ (mul_pos hpos hN)]
  push_cast
  calc ∑ cr, (T cr : ℝ) ≤ ∑ _cr : (Fin k → Gp × Gp) × (Fin k → ZMod q × ZMod q), B * N :=
        Finset.sum_le_sum fun cr _ ↦ hT cr
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, hcr, nsmul_eq_mul]; ring

end Reduction

end GcZk.PVW
