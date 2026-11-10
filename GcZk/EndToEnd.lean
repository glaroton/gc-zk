/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.Security
import GcZk.Binding

/-!
# End-to-end soundness with a hash commitment

The honest verifier garbles an unsatisfiable circuit with a uniform seed (`Δ ≠ 0`, the zero-labels
of the inputs and of the constants) and a uniform hash `H`. The commitment oracle `G` is uniform
and independent. A cheating prover receives the material and the active labels of its OT input
`x`. At each step it makes one query to `H` and one to `G`; a prover that interleaves them
arbitrarily is of this form after padding. It makes `n₁` steps, commits, sees the opened seed,
makes `n₂` more steps, and opens a point.

## Main result

* `GcZk.E2E.prob_accept_le`: the verifier accepts with probability at most
  `(n₁ + 1) / (|V| - 1) + (n₁² + n₂ + 1) / |D|`.

## Proof

For fixed `H` and seed, the prover is a prover of `GcZk.Bind` for the oracle `G` (it answers its
`H` queries itself), so acceptance costs at most the extractor's success plus the binding error.
For fixed `G`, the extractor is an authenticity adversary of `GcZk.Sec` for the oracle `H` (it
answers its `G` queries itself), and the target point of the verifier is the inactive output
label. Summing over all the randomness gives the bound.
-/

namespace GcZk.E2E

open RO Sec GcZk.Bind

variable {V R D : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-! ### Paired runs and their replays -/

/-- The answers to the first `k` steps of a strategy that queries `OH` and `OG` once per step. -/
def cans (OH : ℕ × V → V) (OG : V × R → D) (st : List (V × D) → (ℕ × V) × (V × R)) :
    ℕ → List (V × D)
  | 0 => []
  | k + 1 => cans OH OG st k ++ [(OH (st (cans OH OG st k)).1, OG (st (cans OH OG st k)).2)]

/-- Rebuild the paired answers from the `G` answers, answering `H` with `OH`. -/
def replayG (OH : ℕ × V → V) (st : List (V × D) → (ℕ × V) × (V × R)) (a : List D) :
    List (V × D) :=
  a.foldl (fun acc d ↦ acc ++ [(OH (st acc).1, d)]) []

/-- Rebuild the paired answers from the `H` answers, answering `G` with `OG`. -/
def replayH (OG : V × R → D) (st : List (V × D) → (ℕ × V) × (V × R)) (a : List V) :
    List (V × D) :=
  a.foldl (fun acc h ↦ acc ++ [(h, OG (st acc).2)]) []

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem replayG_snoc (OH : ℕ × V → V) (st : List (V × D) → (ℕ × V) × (V × R)) (a : List D)
    (d : D) : replayG OH st (a ++ [d]) = replayG OH st a ++ [(OH (st (replayG OH st a)).1, d)] := by
  simp [replayG, List.foldl_append]

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem replayH_snoc (OG : V × R → D) (st : List (V × D) → (ℕ × V) × (V × R)) (a : List V)
    (h : V) : replayH OG st (a ++ [h]) = replayH OG st a ++ [(h, OG (st (replayH OG st a)).2)] := by
  simp [replayH, List.foldl_append]

omit [AddCommGroup V] [Module (ZMod 2) V] in
/-- The `G`-only run, replayed, is the paired run. -/
theorem replayG_ans (OH : ℕ × V → V) (G : V × R → D) (st : List (V × D) → (ℕ × V) × (V × R))
    (k : ℕ) :
    replayG OH st (Com.ans G (fun a ↦ (st (replayG OH st a)).2) k) = cans OH G st k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Com.ans, replayG_snoc, ih, cans]

omit [AddCommGroup V] [Module (ZMod 2) V] in
/-- The `H`-only run of an authenticity adversary, replayed, is the paired run. -/
theorem replayH_answers (H : ℕ → V → V) (G : V × R → D) (st : List (V × D) → (ℕ × V) × (V × R))
    (M : List (Material V)) (Aq : QAdv V) (hq : ∀ a, Aq.query M a = (st (replayH G st a)).1)
    (k : ℕ) : replayH G st (answers H Aq M k) = cans (fun p ↦ H p.1 p.2) G st k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [answers, replayH_snoc, ih, hq, ih, cans]

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem cans_take (OH : ℕ × V → V) (OG : V × R → D) (st : List (V × D) → (ℕ × V) × (V × R))
    {k n : ℕ} (h : k ≤ n) : (cans OH OG st n).take k = cans OH OG st k := by
  induction n with
  | zero => rw [Nat.le_zero.1 h]; rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · rw [cans, List.take_append_of_le_length (by
        have : (cans OH OG st n).length = n := by
          clear ih h hk; induction n with
          | zero => rfl
          | succ n ih => simp [cans, ih]
        omega), ih (by omega)]
    · rw [show k = n + 1 by omega]
      have : (cans OH OG st (n + 1)).length = n + 1 := by
        clear ih h hk; induction n with
        | zero => rfl
        | succ n ih => simp [cans] at ih ⊢; omega
      exact List.take_of_length_le (by omega)

/-! ### The cheating prover -/

/-- A cheating prover with `k` OT inputs, making one `H` query and one `G` query per step. -/
structure PProver (k : ℕ) (V R D : Type*) where
  x : ℕ → Bool
  n₁ : ℕ
  n₂ : ℕ
  step₁ : List (Material V) → (Fin k → V) → List (V × D) → (ℕ × V) × (V × R)
  commit : List (Material V) → (Fin k → V) → List (V × D) → D
  step₂ : List (Material V) → (Fin k → V) → List (V × D) → Seed V → List (V × D) →
    (ℕ × V) × (V × R)
  opened : List (Material V) → (Fin k → V) → List (V × D) → Seed V → List (V × D) → V × R

variable (C : Circuit) (out k : ℕ) (P : PProver k V R D)

/-- The hash as an oracle on pairs. -/
def oH (H : Fin C.length → V → V) : ℕ × V → V := fun p ↦ extH H p.1 p.2

/-- The target label of the verifier with seed `σ`: the `1`-label of the output. -/
def target (H : Fin C.length → V → V) (σ : Seed V) : V :=
  (garble (extH H) σ C).1.getD out 0 + σ.delta

/-- The verifier accepts the cheating prover. -/
def RealAccept (Δ : V) (H : Fin C.length → V → V) (Lin : Fin k → V) (Lc : Fin C.length → V)
    (G : V × R → D) : Prop :=
  let M := gMat C k Δ H Lin Lc
  let A := activeIn k P.x Δ Lin
  let σ := seedOf C k Δ Lin Lc
  let c₁ := cans (oH C H) G (P.step₁ M A) P.n₁
  let c₂ := cans (oH C H) G (P.step₂ M A c₁ σ) P.n₂
  (P.opened M A c₁ σ c₂).1 = target C out H σ ∧
    G (P.opened M A c₁ σ c₂) = P.commit M A c₁

/-- For fixed hash and seed: the prover as a `GcZk.Bind` prover for the oracle `G`. -/
def toBind (M : List (Material V)) (A : Fin k → V) (H : Fin C.length → V → V) :
    Bind.Prover Unit (Seed V) (V × R) D where
  q₁ := P.n₁
  q₂ := P.n₂
  Q₁ _ a := (P.step₁ M A (replayG (oH C H) (P.step₁ M A) a)).2
  commit _ a := P.commit M A (replayG (oH C H) (P.step₁ M A) a)
  Q₂ _ a₁ σ a := (P.step₂ M A (replayG (oH C H) (P.step₁ M A) a₁) σ
      (replayG (oH C H) (P.step₂ M A (replayG (oH C H) (P.step₁ M A) a₁) σ) a)).2
  opened _ a₁ σ a := P.opened M A (replayG (oH C H) (P.step₁ M A) a₁) σ
      (replayG (oH C H) (P.step₂ M A (replayG (oH C H) (P.step₁ M A) a₁) σ) a)

omit [Module (ZMod 2) V] in
theorem realAccept_iff (Δ : V) (H : Fin C.length → V → V)
    (Lin : Fin k → V) (Lc : Fin C.length → V) (G : V × R → D) :
    RealAccept C out k P Δ H Lin Lc G ↔
      Bind.Accept (toBind C k P (gMat C k Δ H Lin Lc) (activeIn k P.x Δ Lin) H) ()
        (seedOf C k Δ Lin Lc) (fun p ↦ p.1 = target C out H (seedOf C k Δ Lin Lc)) G := by
  simp only [RealAccept, Bind.Accept, Bind.opn, Bind.com, Bind.a₁, toBind, replayG_ans]

/-! ### The extractor as an authenticity adversary -/

open Classical in
/-- The label of the first `G` query of a replayed first phase answered with the commitment. -/
noncomputable def firstLabel (G : V × R → D) (M : List (Material V)) (A : Fin k → V)
    (c : List (V × D)) : V :=
  if h : ∃ j < P.n₁, G (P.step₁ M A (c.take j)).2 = P.commit M A c then
    (P.step₁ M A (c.take (Nat.find h))).2.1
  else 0

/-- For a fixed commitment oracle `G`: the extractor as an adversary of `GcZk.Sec`. It replays the
first phase, answering `G` itself, and outputs the label of the first `G` query answered with the
commitment. -/
noncomputable def extAdv (G : V × R → D) (A : Fin k → V) : QAdv V where
  query M a := (P.step₁ M A (replayH G (P.step₁ M A) a)).1
  guess M a := firstLabel k P G M A (replayH G (P.step₁ M A) a)

theorem extWins_garbleWin
    (hC : (plain P.x C).getD out false = false) (Δ : V) (H : Fin C.length → V → V)
    (Lin : Fin k → V) (Lc : Fin C.length → V) (G : V × R → D)
    (hw : Bind.ExtWins (toBind C k P (gMat C k Δ H Lin Lc) (activeIn k P.x Δ Lin) H) ()
      (fun p ↦ p.1 = target C out H (seedOf C k Δ Lin Lc)) G) :
    GarbleWin C out P.n₁ k P.x (extAdv k P G) Δ H Lin Lc := by
  classical
  set M := gMat C k Δ H Lin Lc
  set A := activeIn k P.x Δ Lin
  have hrun : replayH G (P.step₁ M A) (answers (extH H) (extAdv k P G A) M P.n₁) =
      cans (oH C H) G (P.step₁ M A) P.n₁ :=
    replayH_answers (extH H) G (P.step₁ M A) M _ (fun _ ↦ rfl) P.n₁
  obtain ⟨j, hj, hval, hmin, hacc⟩ := hw
  have hj' : j < P.n₁ := hj
  simp only [toBind, Bind.qry₁, Bind.com, Bind.a₁, replayG_ans] at hval hmin hacc
  have hex : ∃ i < P.n₁, G (P.step₁ M A ((cans (oH C H) G (P.step₁ M A) P.n₁).take i)).2 =
      P.commit M A (cans (oH C H) G (P.step₁ M A) P.n₁) :=
    ⟨j, hj', by rw [cans_take _ _ _ hj'.le]; exact hval⟩
  have hfind : Nat.find hex = j := by
    refine le_antisymm (Nat.find_min' hex ⟨hj', by rw [cans_take _ _ _ hj'.le]; exact hval⟩) ?_
    by_contra hlt
    rw [not_le] at hlt
    have hs := Nat.find_spec hex
    rw [cans_take _ _ _ (by omega : Nat.find hex ≤ P.n₁)] at hs
    exact hmin _ hlt hs.2
  have hguess : (extAdv k P G A).guess M (answers (extH H) (extAdv k P G A) M P.n₁) =
      target C out H (seedOf C k Δ Lin Lc) := by
    have hg : ∀ a, (extAdv k P G A).guess M a = firstLabel k P G M A (replayH G (P.step₁ M A) a) :=
      fun _ ↦ rfl
    rw [hg, hrun, firstLabel, dite_eq_left_of_eq_true (eq_true hex)]
    simp only [hfind, cans_take _ _ _ hj'.le]
    exact hacc
  unfold GarbleWin
  rw [hguess, target, Auth.activeOut, gMat, eval_garble, hC, lab_false]
  rfl

/-! ### The end-to-end bound -/

variable [Fintype V] [Fintype R] [Fintype D]

open Classical in
/-- **End-to-end soundness, counting form.** Summed over the seed, the hash and the commitment
oracle, the accepting runs of a cheating prover, times `|D|`, are at most
`(n₁ + 1) |G| |H| |L_in| |L_c| |D| + |Δ ≠ 0| |L_in| |L_c| |H| (n₁² + n₂ + 1) |G|`. -/
theorem card_accept_le (hC : (plain P.x C).getD out false = false)
    (hx : ∀ j, k ≤ j → P.x j = false) :
    (∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V,
      ∑ H : Fin C.length → V → V,
        (Finset.univ.filter fun G : V × R → D ↦ RealAccept C out k P Δ H Lin Lc G).card) *
        Fintype.card D ≤
      (P.n₁ + 1) * Fintype.card (V × R → D) * Fintype.card (Fin C.length → V → V) *
          Fintype.card (Fin k → V) * Fintype.card (Fin C.length → V) * Fintype.card D +
        (Finset.univ.filter (· ≠ (0 : V))).card * Fintype.card (Fin k → V) *
          Fintype.card (Fin C.length → V) * Fintype.card (Fin C.length → V → V) *
          ((P.n₁ * P.n₁ + P.n₂ + 1) * Fintype.card (V × R → D)) := by
  set S := Finset.univ.filter (· ≠ (0 : V))
  set NG := Fintype.card (V × R → D)
  set E : ℕ := (P.n₁ * P.n₁ + P.n₂ + 1) * NG
  -- Binding, for each seed and hash.
  have hbind : ∀ Δ (Lin : Fin k → V) (Lc : Fin C.length → V) (H : Fin C.length → V → V),
      (Finset.univ.filter fun G : V × R → D ↦ RealAccept C out k P Δ H Lin Lc G).card *
          Fintype.card D ≤
        (Finset.univ.filter fun G : V × R → D ↦ GarbleWin C out P.n₁ k P.x
          (extAdv k P G) Δ H Lin Lc).card * Fintype.card D + E := by
    intro Δ Lin Lc H
    set B := toBind C k P (gMat C k Δ H Lin Lc) (activeIn k P.x Δ Lin) H
    set acc := fun p : V × R ↦ p.1 = target C out H (seedOf C k Δ Lin Lc)
    have h1 := Bind.card_accept_le B () (seedOf C k Δ Lin Lc) acc
    have h2 : (Finset.univ.filter fun G : V × R → D ↦ RealAccept C out k P Δ H Lin Lc G).card ≤
        (Finset.univ.filter fun G : V × R → D ↦ GarbleWin C out P.n₁ k P.x
          (extAdv k P G) Δ H Lin Lc).card +
        (Finset.univ.filter fun G : V × R → D ↦ Bind.Accept B () (seedOf C k Δ Lin Lc) acc G ∧
          ¬ Bind.ExtWins B () acc G).card := by
      refine (Finset.card_le_card fun G hG ↦ ?_).trans (Finset.card_union_le _ _)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hG ⊢
      by_cases he : Bind.ExtWins B () acc G
      · exact Or.inl (extWins_garbleWin C out k P hC Δ H Lin Lc G he)
      · exact Or.inr ⟨(realAccept_iff C out k P Δ H Lin Lc G).1 hG, he⟩
    have := Nat.mul_le_mul_right (Fintype.card D) h2
    rw [Nat.add_mul] at this
    exact this.trans (Nat.add_le_add_left h1 _)
  -- Authenticity, for each commitment oracle.
  have hauth : ∑ Δ ∈ S, ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V, ∑ H : Fin C.length → V → V,
      (Finset.univ.filter fun G : V × R → D ↦ GarbleWin C out P.n₁ k P.x
        (extAdv k P G) Δ H Lin Lc).card ≤
      (P.n₁ + 1) * Fintype.card (Fin C.length → V → V) * Fintype.card (Fin k → V) *
        Fintype.card (Fin C.length → V) * NG := by
    have swap : ∀ Δ (Lin : Fin k → V) (Lc : Fin C.length → V),
        ∑ H : Fin C.length → V → V, (Finset.univ.filter fun G : V × R → D ↦
          GarbleWin C out P.n₁ k P.x (extAdv k P G) Δ H Lin Lc).card =
        ∑ G : V × R → D, (Finset.univ.filter fun H : Fin C.length → V → V ↦
          GarbleWin C out P.n₁ k P.x (extAdv k P G) Δ H Lin Lc).card := by
      intro Δ Lin Lc
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    simp_rw [swap]
    let f : (V × R → D) → V → (Fin k → V) → (Fin C.length → V) → ℕ := fun G Δ Lin Lc ↦
      (Finset.univ.filter fun H : Fin C.length → V → V ↦
        GarbleWin C out P.n₁ k P.x (extAdv k P G) Δ H Lin Lc).card
    have reorder : ∑ Δ ∈ S, ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V, ∑ G : V × R → D,
        f G Δ Lin Lc = ∑ G : V × R → D, ∑ Δ ∈ S, ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V,
        f G Δ Lin Lc := by
      calc _ = ∑ Δ ∈ S, ∑ Lin : Fin k → V, ∑ G : V × R → D, ∑ Lc : Fin C.length → V,
            f G Δ Lin Lc :=
            Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
        _ = ∑ Δ ∈ S, ∑ G : V × R → D, ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V,
            f G Δ Lin Lc := Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
        _ = _ := Finset.sum_comm
    refine (le_of_eq reorder).trans ?_
    calc _ ≤ ∑ _G : V × R → D, (P.n₁ + 1) * Fintype.card (Fin C.length → V → V) *
          Fintype.card (Fin k → V) * Fintype.card (Fin C.length → V) :=
          Finset.sum_le_sum fun G _ ↦ garble_rom_bound C out P.n₁ k P.x (extAdv k P G) hx
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, NG]; ring
  calc (∑ Δ ∈ S, ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V, ∑ H : Fin C.length → V → V,
        (Finset.univ.filter fun G : V × R → D ↦ RealAccept C out k P Δ H Lin Lc G).card) *
        Fintype.card D
      = ∑ Δ ∈ S, ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V, ∑ H : Fin C.length → V → V,
        (Finset.univ.filter fun G : V × R → D ↦ RealAccept C out k P Δ H Lin Lc G).card *
        Fintype.card D := by simp only [Finset.sum_mul]
    _ ≤ ∑ Δ ∈ S, ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V, ∑ H : Fin C.length → V → V,
        ((Finset.univ.filter fun G : V × R → D ↦ GarbleWin C out P.n₁ k P.x
          (extAdv k P G) Δ H Lin Lc).card * Fintype.card D + E) :=
        Finset.sum_le_sum fun Δ _ ↦ Finset.sum_le_sum fun Lin _ ↦ Finset.sum_le_sum fun Lc _ ↦
          Finset.sum_le_sum fun H _ ↦ hbind Δ Lin Lc H
    _ = (∑ Δ ∈ S, ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V, ∑ H : Fin C.length → V → V,
          (Finset.univ.filter fun G : V × R → D ↦ GarbleWin C out P.n₁ k P.x
            (extAdv k P G) Δ H Lin Lc).card) * Fintype.card D +
        S.card * Fintype.card (Fin k → V) * Fintype.card (Fin C.length → V) *
          Fintype.card (Fin C.length → V → V) * E := by
        simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, Finset.card_univ,
          smul_eq_mul]
        ring
    _ ≤ _ := by
        have := Nat.mul_le_mul_right (Fintype.card D) hauth
        nlinarith

open Classical in
/-- **End-to-end soundness.** With the seed, the hash and the commitment oracle uniform, the
verifier accepts a cheating prover for an unsatisfiable circuit with probability at most
`(n₁ + 1) / (|V| - 1) + (n₁² + n₂ + 1) / |D|`. -/
theorem prob_accept_le [Nontrivial V] [Nonempty D] (hC : (plain P.x C).getD out false = false)
    (hx : ∀ j, k ≤ j → P.x j = false) :
    ((∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V,
      ∑ H : Fin C.length → V → V,
        (Finset.univ.filter fun G : V × R → D ↦ RealAccept C out k P Δ H Lin Lc G).card : ℕ) :
        ℝ) /
      ((Finset.univ.filter (· ≠ (0 : V))).card * Fintype.card (Fin k → V) *
        Fintype.card (Fin C.length → V) * Fintype.card (Fin C.length → V → V) *
        Fintype.card (V × R → D)) ≤
      ((P.n₁ + 1 : ℕ) : ℝ) / (Fintype.card V - 1) +
        ((P.n₁ * P.n₁ + P.n₂ + 1 : ℕ) : ℝ) / Fintype.card D := by
  set T := ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), ∑ Lin : Fin k → V, ∑ Lc : Fin C.length → V,
      ∑ H : Fin C.length → V → V,
        (Finset.univ.filter fun G : V × R → D ↦ RealAccept C out k P Δ H Lin Lc G).card
  have hS : (Finset.univ.filter (· ≠ (0 : V))).card = Fintype.card V - 1 := by
    rw [Finset.filter_ne' Finset.univ (0 : V), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
  have hV : 1 < Fintype.card V := Fintype.one_lt_card
  have hSr : ((Finset.univ.filter (· ≠ (0 : V))).card : ℝ) = Fintype.card V - 1 := by
    rw [hS, Nat.cast_sub hV.le]; simp
  have h := card_accept_le C out k P hC hx
  have pS : (0 : ℝ) < (Finset.univ.filter (· ≠ (0 : V))).card := by
    rw [hSr]; have : (1 : ℝ) < Fintype.card V := by exact_mod_cast hV
    linarith
  have pL : (0 : ℝ) < Fintype.card (Fin k → V) := by exact_mod_cast Fintype.card_pos
  have pC : (0 : ℝ) < Fintype.card (Fin C.length → V) := by exact_mod_cast Fintype.card_pos
  have pH : (0 : ℝ) < Fintype.card (Fin C.length → V → V) := by exact_mod_cast Fintype.card_pos
  have pG : (0 : ℝ) < Fintype.card (V × R → D) := by exact_mod_cast Fintype.card_pos
  have pD : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hR : (T : ℝ) * Fintype.card D ≤
      ((P.n₁ + 1 : ℕ) : ℝ) * Fintype.card (V × R → D) * Fintype.card (Fin C.length → V → V) *
          Fintype.card (Fin k → V) * Fintype.card (Fin C.length → V) * Fintype.card D +
        (Finset.univ.filter (· ≠ (0 : V))).card * Fintype.card (Fin k → V) *
          Fintype.card (Fin C.length → V) * Fintype.card (Fin C.length → V → V) *
          (((P.n₁ * P.n₁ + P.n₂ + 1 : ℕ) : ℝ) * Fintype.card (V × R → D)) := by
    exact_mod_cast h
  rw [← hSr, div_add_div _ _ pS.ne' pD.ne', div_le_div_iff₀ (by positivity) (mul_pos pS pD)]
  nlinarith [mul_pos (mul_pos (mul_pos (mul_pos pS pL) pC) pH) pG]

end GcZk.E2E
