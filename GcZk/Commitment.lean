/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.Jko

/-!
# JKO with a hash commitment: statistical zero knowledge

The ideal commitment of `GcZk.Jko` is replaced by the hash commitment `c = G(Z, r)`, where
`G : V × R → D` is a random oracle and `r` is uniform in `R`. The OT stays ideal. A malicious
verifier runs in three phases, each with adaptive queries to `G`:

1. `q₁` queries, then the material and the OT pairs;
2. after the commitment `c`, `q₂` queries, then the opened seed;
3. after the prover's last message (`(Z, r)` or an abort), `q₃` queries, then its output bit.

The simulator does not know the witness. It commits to a uniform `c`, and if the opening passes
the check it computes `Z = L_out + Δ` from the seed and **programs** `G(Z, r) := c`.

## Main result

* `GcZk.Com.zk_rom`: for every malicious verifier and every witness, the probabilities that the
  verifier outputs `1` in the real execution and with the simulator differ by at most
  `(q₁ + q₂ + q₃) / |R|`.

## Proof

A hybrid game uses the real commitment point `p = (Z_w, r)` but a uniform commitment `c`, and the
programmed oracle `G[p := c]` after the commitment. Real and hybrid agree on the set where the
first phase does not query `p`: there, swapping `G(p)` and `c` is an involution that maps one game
to the other. Hybrid and simulator agree unless the second phase, or the third phase after an
abort, queries `p`. None of these queries depends on `r`, so each one hits `p` for at most one `r`.
-/

namespace GcZk.Com

open Jko

/-! ### Oracle runs -/

section Runs

variable {P A : Type*}

/-- The answers to the first `k` queries of the query strategy `Q`, with oracle `O`. -/
def ans (O : P → A) (Q : List A → P) : ℕ → List A
  | 0 => []
  | k + 1 => ans O Q k ++ [O (Q (ans O Q k))]

/-- The run queries the point `p` among its first `n` queries. -/
def Hits (O : P → A) (Q : List A → P) (n : ℕ) (p : P) : Prop :=
  ∃ k < n, Q (ans O Q k) = p

theorem ans_congr (O O' : P → A) (Q : List A → P) (n : ℕ)
    (h : ∀ k < n, O (Q (ans O' Q k)) = O' (Q (ans O' Q k))) : ans O Q n = ans O' Q n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have e := ih fun j hj ↦ h j (by omega)
    simp only [ans, e, h k (by omega)]

/-- Reprogramming a point that the run does not query does not change the answers. -/
theorem ans_update [DecidableEq P] (O : P → A) (Q : List A → P) (n : ℕ) (p : P) (v : A)
    (h : ¬ Hits O Q n p) : ans (Function.update O p v) Q n = ans O Q n := by
  refine ans_congr _ _ _ _ fun k hk ↦ ?_
  have hne : Q (ans O Q k) ≠ p := fun e ↦ h ⟨k, hk, e⟩
  exact Function.update_of_ne hne _ _

end Runs

/-! ### Verifiers and games -/

/-- A deterministic malicious verifier with three phases of queries to the commitment oracle.
A randomized verifier is a family of these indexed by its coins. -/
structure MalV (V R D : Type*) where
  q₁ : ℕ
  q₂ : ℕ
  q₃ : ℕ
  Q₁ : List D → V × R
  first : List D → List (Material V) × (ℕ → V × V)
  Q₂ : List D → D → List D → V × R
  opening : List D → D → List D → Seed V
  Q₃ : List D → D → List D → Option (V × R) → List D → V × R
  out : List D → D → List D → Option (V × R) → List D → Bool

variable {V R D : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (H : ℕ → V → V) (C : Circuit) (o : ℕ) (w : ℕ → Bool) (A : MalV V R D)
  (chk : List D → D → List D → Prop)

/-- The verifier's messages, from its answers and the commitment. -/
def msg (a₁ : List D) (c : D) (a₂ : List D) : VerifierMsg V :=
  ⟨(A.first a₁).1, (A.first a₁).2, A.opening a₁ c a₂⟩

/-- The output label the honest prover computes from the first message. -/
def zw (a₁ : List D) : V :=
  ((eval H (otReceive (A.first a₁).2 w) C (A.first a₁).1).getD o (false, 0)).2

open Classical in
/-- The prover's last message in the real execution. -/
noncomputable def realFin (r : R) (a₁ : List D) (c : D) (a₂ : List D) : Option (V × R) :=
  if chk a₁ c a₂ then some (zw H C o w A a₁, r) else none

open Classical in
/-- The simulator's last message: it does not use the witness. -/
noncomputable def simFin (r : R) (a₁ : List D) (c : D) (a₂ : List D) : Option (V × R) :=
  if chk a₁ c a₂ then
    some ((garble H (msg A a₁ c a₂).opening C).1.getD o 0 + (msg A a₁ c a₂).opening.delta, r)
  else none

/-- The check of `GcZk.Jko`: the material and the OT pairs come from the opened seed. -/
def verChk (a₁ : List D) (c : D) (a₂ : List D) : Prop := Verified H C (msg A a₁ c a₂)

/-- The prover's check is sound: when it passes, the honest prover's label is the label the
simulator computes from the opened seed. -/
def CheckSound : Prop :=
  ∀ a₁ c a₂, chk a₁ c a₂ → zw H C o w A a₁ =
    (garble H (msg A a₁ c a₂).opening C).1.getD o 0 + (msg A a₁ c a₂).opening.delta

/-- One execution, with oracles for each phase, the commitment and the last message. -/
def play (O₁ O₂ : V × R → D) (O₃ : Option (V × R) → V × R → D) (c : D)
    (fin : List D → D → List D → Option (V × R)) : Bool :=
  A.out (ans O₁ A.Q₁ A.q₁) c (ans O₂ (A.Q₂ (ans O₁ A.Q₁ A.q₁) c) A.q₂)
    (fin (ans O₁ A.Q₁ A.q₁) c (ans O₂ (A.Q₂ (ans O₁ A.Q₁ A.q₁) c) A.q₂))
    (ans (O₃ (fin (ans O₁ A.Q₁ A.q₁) c (ans O₂ (A.Q₂ (ans O₁ A.Q₁ A.q₁) c) A.q₂)))
      (A.Q₃ (ans O₁ A.Q₁ A.q₁) c (ans O₂ (A.Q₂ (ans O₁ A.Q₁ A.q₁) c) A.q₂)
        (fin (ans O₁ A.Q₁ A.q₁) c (ans O₂ (A.Q₂ (ans O₁ A.Q₁ A.q₁) c) A.q₂)))
      A.q₃)

variable [DecidableEq V] [DecidableEq R]

/-- The commitment point of the honest prover. -/
def point (G : V × R → D) (r : R) : V × R := (zw H C o w A (ans G A.Q₁ A.q₁), r)

/-- The real execution: the prover commits with `G(Z_w, r)`. -/
noncomputable def real (G : V × R → D) (r : R) : Bool :=
  play A G G (fun _ ↦ G) (G (point H C o w A G r)) (realFin H C o w A chk r)

/-- The hybrid: commitment `c`, oracle programmed at the real point after the commitment. -/
noncomputable def hyb (G : V × R → D) (c : D) (r : R) : Bool :=
  play A G (Function.update G (point H C o w A G r) c)
    (fun _ ↦ Function.update G (point H C o w A G r) c) c (realFin H C o w A chk r)

/-- The simulator: commitment `c`, and the oracle is programmed only after a successful
opening, at the point it computes from the seed. -/
noncomputable def sim (G : V × R → D) (c : D) (r : R) : Bool :=
  play A G G (fun f ↦ f.elim G fun p ↦ Function.update G p c) c (simFin H C o A chk r)

/-- The first phase queries the real commitment point. -/
def Bad₁ (G : V × R → D) (r : R) : Prop := Hits G A.Q₁ A.q₁ (point H C o w A G r)

/-- The second phase, or the third after an abort, queries the real commitment point. -/
noncomputable def Bad₂₃ (G : V × R → D) (c : D) (r : R) : Prop :=
  Hits G (A.Q₂ (ans G A.Q₁ A.q₁) c) A.q₂ (point H C o w A G r) ∨
    (realFin H C o w A chk r (ans G A.Q₁ A.q₁) c (ans G (A.Q₂ (ans G A.Q₁ A.q₁) c) A.q₂) = none ∧
      Hits G (A.Q₃ (ans G A.Q₁ A.q₁) c (ans G (A.Q₂ (ans G A.Q₁ A.q₁) c) A.q₂) none) A.q₃
        (point H C o w A G r))

/-! ### The simulator computes the prover's message -/

omit [DecidableEq V] [DecidableEq R] in
omit [Module (ZMod 2) V] in
theorem simFin_eq (hchk : CheckSound H C o w A chk) (r : R) :
    simFin H C o A chk r = realFin H C o w A chk r := by
  funext a₁ c a₂
  unfold simFin realFin
  split_ifs with hv
  · rw [hchk a₁ c a₂ hv]
  · rfl

omit [DecidableEq V] [DecidableEq R] in
/-- With a witness, the check of `GcZk.Jko` (the material and the OT pairs come from the opened
seed) is sound. -/
theorem checkSound_verified (hw : (plain w C).getD o false = true) :
    CheckSound H C o w A (verChk H C A) := by
  intro a₁ c a₂ hv
  have := proverLabel_of_verified H C o w hv
  rw [hw, lab_true] at this
  simp only [proverLabel, msg] at this
  simp only [zw, msg, this]

/-! ### Real and hybrid -/

/-- The swap of `G(p)` and `c`. -/
def swap (G : V × R → D) (c : D) (r : R) : (V × R → D) × D :=
  (Function.update G (point H C o w A G r) c, G (point H C o w A G r))

omit [Module (ZMod 2) V] in
theorem ans₁_swap (G : V × R → D) (c : D) (r : R) (h : ¬ Bad₁ H C o w A G r) :
    ans (swap H C o w A G c r).1 A.Q₁ A.q₁ = ans G A.Q₁ A.q₁ :=
  ans_update _ _ _ _ _ h

omit [Module (ZMod 2) V] in
theorem point_swap (G : V × R → D) (c : D) (r : R) (h : ¬ Bad₁ H C o w A G r) :
    point H C o w A (swap H C o w A G c r).1 r = point H C o w A G r := by
  simp only [point, ans₁_swap H C o w A G c r h]

omit [Module (ZMod 2) V] in
theorem bad₁_swap (G : V × R → D) (c : D) (r : R) (h : ¬ Bad₁ H C o w A G r) :
    ¬ Bad₁ H C o w A (swap H C o w A G c r).1 r := by
  unfold Bad₁
  rw [point_swap H C o w A G c r h]
  rintro ⟨k, hk, e⟩
  apply h
  refine ⟨k, hk, ?_⟩
  rwa [swap, ans_update _ _ k _ _ fun ⟨j, hj, ej⟩ ↦ h ⟨j, by omega, ej⟩] at e

omit [Module (ZMod 2) V] in
theorem swap_swap (G : V × R → D) (c : D) (r : R) (h : ¬ Bad₁ H C o w A G r) :
    swap H C o w A (swap H C o w A G c r).1 (swap H C o w A G c r).2 r = (G, c) := by
  rw [swap, point_swap H C o w A G c r h]
  simp [swap]

omit [Module (ZMod 2) V] in
/-- Off the first bad event, the hybrid is the real execution on the swapped oracle. -/
theorem hyb_eq_real (G : V × R → D) (c : D) (r : R) (h : ¬ Bad₁ H C o w A G r) :
    hyb H C o w A chk G c r = real H C o w A chk (swap H C o w A G c r).1 r := by
  have e := point_swap H C o w A G c r h
  unfold hyb real play
  rw [e, ans₁_swap H C o w A G c r h]
  simp [swap]

/-! ### Hybrid and simulator -/

omit [Module (ZMod 2) V] in
/-- Off the bad events, the hybrid and the simulator agree. -/
theorem hyb_eq_sim (hchk : CheckSound H C o w A chk) (G : V × R → D) (c : D) (r : R)
    (h : ¬ Bad₂₃ H C o w A chk G c r) : hyb H C o w A chk G c r = sim H C o A chk G c r := by
  simp only [Bad₂₃, not_or, not_and] at h
  obtain ⟨h2, h3⟩ := h
  have e2 := ans_update G (A.Q₂ (ans G A.Q₁ A.q₁) c) A.q₂ (point H C o w A G r) c h2
  unfold hyb sim play
  rw [simFin_eq H C o w A chk hchk, e2]
  cases hf : realFin H C o w A chk r (ans G A.Q₁ A.q₁) c
      (ans G (A.Q₂ (ans G A.Q₁ A.q₁) c) A.q₂) with
  | none =>
    simp only [Option.elim_none]
    rw [ans_update _ _ _ _ _ (h3 hf)]
  | some p =>
    have hp : p = point H C o w A G r := by
      unfold realFin at hf
      split_ifs at hf
      cases hf
      rfl
    subst hp
    rfl

/-! ### Counting -/

section Counting

variable [Fintype V] [Fintype R] [Fintype D]


omit [Module (ZMod 2) V] in
open Classical in
/-- On the complement of the first bad event, the swap matches hybrid and real executions. -/
theorem card_hyb_eq_card_real (r : R) :
    (Finset.univ.filter fun x : (V × R → D) × D ↦
        ¬ Bad₁ H C o w A x.1 r ∧ hyb H C o w A chk x.1 x.2 r).card =
      (Finset.univ.filter fun x : (V × R → D) × D ↦
        ¬ Bad₁ H C o w A x.1 r ∧ real H C o w A chk x.1 r).card := by
  refine Finset.card_bij' (fun x _ ↦ swap H C o w A x.1 x.2 r)
    (fun x _ ↦ swap H C o w A x.1 x.2 r) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨bad₁_swap H C o w A x.1 x.2 r hx.1, (hyb_eq_real H C o w A chk x.1 x.2 r hx.1) ▸ hx.2⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨bad₁_swap H C o w A x.1 x.2 r hx.1, ?_⟩
    rw [hyb_eq_real H C o w A chk _ _ r (bad₁_swap H C o w A x.1 x.2 r hx.1),
      swap_swap H C o w A x.1 x.2 r hx.1]
    exact hx.2
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact swap_swap H C o w A x.1 x.2 r hx.1
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact swap_swap H C o w A x.1 x.2 r hx.1

omit [Module (ZMod 2) V] in
open Classical in
/-- For one value of `r`: real wins are simulated wins or bad events. -/
theorem card_real_le (hchk : CheckSound H C o w A chk) (r : R) :
    (Finset.univ.filter fun x : (V × R → D) × D ↦ real H C o w A chk x.1 r).card ≤
      (Finset.univ.filter fun x : (V × R → D) × D ↦ sim H C o A chk x.1 x.2 r).card +
        (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
        (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A chk x.1 x.2 r).card := by
  have h1 : (Finset.univ.filter fun x : (V × R → D) × D ↦ real H C o w A chk x.1 r).card ≤
      (Finset.univ.filter fun x : (V × R → D) × D ↦
        ¬ Bad₁ H C o w A x.1 r ∧ real H C o w A chk x.1 r).card +
      (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card := by
    refine (Finset.card_le_card fun x hx ↦ ?_).trans (Finset.card_union_le _ _)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    by_cases hb : Bad₁ H C o w A x.1 r
    · exact Or.inr hb
    · exact Or.inl ⟨hb, hx⟩
  have h2 : (Finset.univ.filter fun x : (V × R → D) × D ↦
        ¬ Bad₁ H C o w A x.1 r ∧ hyb H C o w A chk x.1 x.2 r).card ≤
      (Finset.univ.filter fun x : (V × R → D) × D ↦ sim H C o A chk x.1 x.2 r).card +
      (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A chk x.1 x.2 r).card := by
    refine (Finset.card_le_card fun x hx ↦ ?_).trans (Finset.card_union_le _ _)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    by_cases hb : Bad₂₃ H C o w A chk x.1 x.2 r
    · exact Or.inr hb
    · exact Or.inl ((hyb_eq_sim H C o w A chk hchk x.1 x.2 r hb) ▸ hx.2)
  rw [← card_hyb_eq_card_real] at h1
  omega

omit [Module (ZMod 2) V] in
open Classical in
/-- For one value of `r`: simulated wins are real wins or bad events. -/
theorem card_sim_le (hchk : CheckSound H C o w A chk) (r : R) :
    (Finset.univ.filter fun x : (V × R → D) × D ↦ sim H C o A chk x.1 x.2 r).card ≤
      (Finset.univ.filter fun x : (V × R → D) × D ↦ real H C o w A chk x.1 r).card +
        (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
        (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A chk x.1 x.2 r).card := by
  have h1 : (Finset.univ.filter fun x : (V × R → D) × D ↦ sim H C o A chk x.1 x.2 r).card ≤
      (Finset.univ.filter fun x : (V × R → D) × D ↦
        ¬ Bad₁ H C o w A x.1 r ∧ hyb H C o w A chk x.1 x.2 r).card +
      ((Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
      (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A chk x.1 x.2 r).card) := by
    refine (Finset.card_le_card fun x hx ↦ ?_).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    by_cases hb : Bad₁ H C o w A x.1 r
    · exact Or.inr (Or.inl hb)
    by_cases hb' : Bad₂₃ H C o w A chk x.1 x.2 r
    · exact Or.inr (Or.inr hb')
    exact Or.inl ⟨hb, (hyb_eq_sim H C o w A chk hchk x.1 x.2 r hb').symm ▸ hx⟩
  have h2 : (Finset.univ.filter fun x : (V × R → D) × D ↦
        ¬ Bad₁ H C o w A x.1 r ∧ real H C o w A chk x.1 r).card ≤
      (Finset.univ.filter fun x : (V × R → D) × D ↦ real H C o w A chk x.1 r).card :=
    Finset.card_le_card fun x hx ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (Finset.mem_filter.1 hx).2.2⟩
  rw [card_hyb_eq_card_real] at h1
  omega

omit [Module (ZMod 2) V] [DecidableEq V] [DecidableEq R] [Fintype V] [Fintype D] in
open Classical in
/-- The first bad event happens for at most `q₁` values of `r`. -/
theorem card_bad₁ (x : (V × R → D) × D) :
    (Finset.univ.filter fun r : R ↦ Bad₁ H C o w A x.1 r).card ≤ A.q₁ := by
  calc _ ≤ ((Finset.range A.q₁).image fun k ↦ (A.Q₁ (ans x.1 A.Q₁ k)).2).card := by
        refine Finset.card_le_card fun r hr ↦ ?_
        obtain ⟨k, hk, e⟩ : Bad₁ H C o w A x.1 r := (Finset.mem_filter.1 hr).2
        exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, by rw [e]; rfl⟩
    _ ≤ (Finset.range A.q₁).card := Finset.card_image_le
    _ = A.q₁ := Finset.card_range _

omit [Module (ZMod 2) V] [DecidableEq V] [DecidableEq R] [Fintype V] [Fintype D] in
open Classical in
/-- The second bad event happens for at most `q₂ + q₃` values of `r`. -/
theorem card_bad₂₃ (x : (V × R → D) × D) :
    (Finset.univ.filter fun r : R ↦ Bad₂₃ H C o w A chk x.1 x.2 r).card ≤ A.q₂ + A.q₃ := by
  set a₁ := ans x.1 A.Q₁ A.q₁
  set a₂ := ans x.1 (A.Q₂ a₁ x.2) A.q₂
  calc _ ≤ ((Finset.range A.q₂).image (fun k ↦ (A.Q₂ a₁ x.2 (ans x.1 (A.Q₂ a₁ x.2) k)).2) ∪
          (Finset.range A.q₃).image
            (fun k ↦ (A.Q₃ a₁ x.2 a₂ none (ans x.1 (A.Q₃ a₁ x.2 a₂ none) k)).2)).card := by
        refine Finset.card_le_card fun r hr ↦ ?_
        have hr' : Bad₂₃ H C o w A chk x.1 x.2 r := (Finset.mem_filter.1 hr).2
        rcases hr' with ⟨k, hk, e⟩ | ⟨-, k, hk, e⟩
        · exact Finset.mem_union_left _
            (Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, by rw [e]; rfl⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, by rw [e]; rfl⟩)
    _ ≤ _ := (Finset.card_union_le _ _).trans
          (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    _ = A.q₂ + A.q₃ := by simp

omit [DecidableEq R] in
open Classical in
theorem sum_card_swap {X : Type*} [Fintype X] (P : X → R → Prop) :
    ∑ r : R, (Finset.univ.filter fun x : X ↦ P x r).card =
      ∑ x : X, (Finset.univ.filter fun r : R ↦ P x r).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

omit [Module (ZMod 2) V] in
open Classical in
/-- The bad events, summed over `r`, number at most `(q₁ + q₂ + q₃)` per `(G, c)`. -/
theorem sum_bad_le :
    ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
      ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A chk x.1 x.2 r).card ≤
      (A.q₁ + A.q₂ + A.q₃) * Fintype.card ((V × R → D) × D) := by
  have e1 : ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card =
      ∑ x : (V × R → D) × D, (Finset.univ.filter fun r : R ↦ Bad₁ H C o w A x.1 r).card :=
    sum_card_swap _
  have e2 : ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
        Bad₂₃ H C o w A chk x.1 x.2 r).card =
      ∑ x : (V × R → D) × D, (Finset.univ.filter fun r : R ↦ Bad₂₃ H C o w A chk x.1 x.2 r).card :=
    sum_card_swap _
  rw [e1, e2, ← Finset.sum_add_distrib]
  calc _ ≤ ∑ _x : (V × R → D) × D, (A.q₁ + A.q₂ + A.q₃) :=
        Finset.sum_le_sum fun x _ ↦ by
          have := card_bad₁ H C o w A x; have := card_bad₂₃ H C o w A chk x; omega
    _ = _ := by simp [mul_comm]

omit [Module (ZMod 2) V] in
open Classical in
/-- Counting form of zero knowledge: summed over `r`, the real and the simulated wins differ by at
most `(q₁ + q₂ + q₃) |(V × R → D) × D|`. -/
theorem zk_count (hchk : CheckSound H C o w A chk) :
    (∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦ real H C o w A chk x.1 r).card) ≤
        (∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
          sim H C o A chk x.1 x.2 r).card) +
          (A.q₁ + A.q₂ + A.q₃) * Fintype.card ((V × R → D) × D) ∧
      (∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦ sim H C o A chk x.1 x.2 r).card) ≤
        (∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦ real H C o w A chk x.1 r).card) +
          (A.q₁ + A.q₂ + A.q₃) * Fintype.card ((V × R → D) × D) := by
  have hB := sum_bad_le H C o w A chk
  constructor
  · calc _ ≤ ∑ r : R, ((Finset.univ.filter fun x : (V × R → D) × D ↦
            sim H C o A chk x.1 x.2 r).card +
          (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
          (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A chk x.1 x.2 r).card) :=
          Finset.sum_le_sum fun r _ ↦ card_real_le H C o w A chk hchk r
      _ ≤ _ := by simp only [Finset.sum_add_distrib]; omega
  · calc _ ≤ ∑ r : R, ((Finset.univ.filter fun x : (V × R → D) × D ↦
            real H C o w A chk x.1 r).card +
          (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
          (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A chk x.1 x.2 r).card) :=
          Finset.sum_le_sum fun r _ ↦ card_sim_le H C o w A chk hchk r
      _ ≤ _ := by simp only [Finset.sum_add_distrib]; omega

omit [Module (ZMod 2) V] in
open Classical in
/-- **Statistical zero knowledge with a hash commitment.** For every malicious verifier and
every witness, the probabilities that the verifier outputs `1` in the real execution and with the
simulator (over `G`, `c` and `r` uniform) differ by at most `(q₁ + q₂ + q₃) / |R|`. -/
theorem zk_rom_of_check [Nonempty R] [Nonempty D] (hchk : CheckSound H C o w A chk) :
    |((∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦ real H C o w A chk x.1 r).card : ℕ) :
        ℝ) / (Fintype.card ((V × R → D) × D) * Fintype.card R) -
      ((∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
          sim H C o A chk x.1 x.2 r).card : ℕ) : ℝ) /
        (Fintype.card ((V × R → D) × D) * Fintype.card R)| ≤
      ((A.q₁ + A.q₂ + A.q₃ : ℕ) : ℝ) / Fintype.card R := by
  set Sr := ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦ real H C o w A chk x.1 r).card
  set Ss := ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦ sim H C o A chk x.1 x.2 r).card
  set B₁ := ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card
  set B₂ := ∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
    Bad₂₃ H C o w A chk x.1 x.2 r).card
  set X := Fintype.card ((V × R → D) × D)
  set q := A.q₁ + A.q₂ + A.q₃
  have hB : B₁ + B₂ ≤ q * X := sum_bad_le H C o w A chk
  have hr : Sr ≤ Ss + B₁ + B₂ := by
    calc Sr ≤ ∑ r : R, ((Finset.univ.filter fun x : (V × R → D) × D ↦
            sim H C o A chk x.1 x.2 r).card +
          (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
          (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A chk x.1 x.2 r).card) :=
          Finset.sum_le_sum fun r _ ↦ card_real_le H C o w A chk hchk r
      _ = Ss + B₁ + B₂ := by simp only [Finset.sum_add_distrib, Ss, B₁, B₂]
  have hs : Ss ≤ Sr + B₁ + B₂ := by
    calc Ss ≤ ∑ r : R, ((Finset.univ.filter fun x : (V × R → D) × D ↦
            real H C o w A chk x.1 r).card +
          (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₁ H C o w A x.1 r).card +
          (Finset.univ.filter fun x : (V × R → D) × D ↦ Bad₂₃ H C o w A chk x.1 x.2 r).card) :=
          Finset.sum_le_sum fun r _ ↦ card_sim_le H C o w A chk hchk r
      _ = Sr + B₁ + B₂ := by simp only [Finset.sum_add_distrib, Sr, B₁, B₂]
  have hX : (0 : ℝ) < X := by exact_mod_cast Fintype.card_pos
  have hS : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have key : |(Sr : ℝ) - Ss| ≤ (q : ℝ) * X := by
    have h1 : (Sr : ℝ) ≤ Ss + q * X := by exact_mod_cast (hr.trans (by omega))
    have h2 : (Ss : ℝ) ≤ Sr + q * X := by exact_mod_cast (hs.trans (by omega))
    rw [abs_sub_le_iff]
    constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos (mul_pos hX hS)]
  calc |(Sr : ℝ) - Ss| / (X * Fintype.card R) ≤ (q * X) / (X * Fintype.card R) :=
        div_le_div_of_nonneg_right key (mul_pos hX hS).le
    _ = q / Fintype.card R := by field_simp

open Classical in
/-- **Statistical zero knowledge with a hash commitment**, for the check of `GcZk.Jko`. -/
theorem zk_rom [Nonempty R] [Nonempty D] (hw : (plain w C).getD o false = true) :
    |((∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
        real H C o w A (verChk H C A) x.1 r).card : ℕ) :
        ℝ) / (Fintype.card ((V × R → D) × D) * Fintype.card R) -
      ((∑ r : R, (Finset.univ.filter fun x : (V × R → D) × D ↦
          sim H C o A (verChk H C A) x.1 x.2 r).card : ℕ) : ℝ) /
        (Fintype.card ((V × R → D) × D) * Fintype.card R)| ≤
      ((A.q₁ + A.q₂ + A.q₃ : ℕ) : ℝ) / Fintype.card R :=
  zk_rom_of_check H C o w A _ (checkSound_verified H C o w A hw)

end Counting

end GcZk.Com
