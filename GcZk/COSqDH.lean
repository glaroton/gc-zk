/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.COSound

/-!
# Soundness with the Chou–Orlandi OT: both key points

If the prover queries both key points `(j, a_j • B_j)` and `(j, a_j • (B_j - A_j))` of an input,
their difference is `(a_j * a_j) • g`, a square Diffie–Hellman solution. The solver `solver j i i'`
does not know `a_j`: given `A = a_j • g`, it runs the verifier and the prover, guesses that the key
queries number `i` and `i'` are the first ones at the two key points, answers them with the values
that unmask the masked pair of `j` (a coin) to `L_j` and `L_j + Δ`, and outputs the difference of
the two queried points (blueprint, Definition `def:co-solver` and Lemma `lem:co-sqdh`).

## Main results

* `GcZk.CO.sim₀_eq`, `GcZk.CO.sim₁_eq`: when the guess is right, the simulated run is the real
  run.
* `GcZk.CO.wins_Ψ`: the solver then outputs `(a_j * a_j) • g`.
* `GcZk.CO.Ψ_injOn`: the map to the solver's input and coins is injective on the randomness where
  the guess is right and the two key points differ.
* `GcZk.CO.card_both_le`: the real randomness with both key points queried, and no secret `0`,
  is at most the sum over `j` and `i ≠ i'` of the winning pairs of the solvers.
-/

namespace GcZk.CO

open Adaptive Auth RO

variable {V R D Gp : Type*} {q : ℕ} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup Gp]
  [Module (ZMod q) Gp] (g : Gp) (C : Circuit) (k : ℕ) (G : V × R → D) (P : Prover k V R D Gp)

/-! ### The key queries of the real run -/

/-- The key query number `t` of the real run: the queries before `B`, then one per step. -/
def realKP (Δ : V) (ω : Ω q k C.length V Gp) (t : ℕ) : Fin k × Gp :=
  if t < P.n₀ then P.Q₀ (msgA g k ω.1) (Com.ans (oK k ω.2.1) (P.Q₀ (msgA g k ω.1)) t)
  else kq₁ g C k G P Δ ω (t - P.n₀)

/-- The prover's first key queries at the two key points of `j` are the numbers `i` and `i'`. -/
def BothAt (Δ : V) (ω : Ω q k C.length V Gp) (j : Fin k) (i i' : ℕ) : Prop :=
  i < P.n₀ + P.n₁ ∧ i' < P.n₀ + P.n₁ ∧
    realKP g C k G P Δ ω i = (j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j false) ∧
    (∀ t < i, realKP g C k G P Δ ω t ≠ (j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j false)) ∧
    realKP g C k G P Δ ω i' = (j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j true) ∧
    (∀ t < i', realKP g C k G P Δ ω t ≠ (j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j true))

/-! ### The solver -/

section Solver

variable (j : Fin k) (i i' : ℕ) (Δ : V) (σ : Ω q k C.length V Gp)

/-- The sender messages of the solver: `A` for `j`, `a_{j'} • g` for the others. -/
def amsgS (A : Gp) : Fin k → Gp := fun j' ↦ if j' = j then A else σ.1 j' • g

open Classical in
/-- The solver's answer to the key query number `t` at `x`, after the key queries at `ps`. -/
noncomputable def kOr (t : ℕ) (ps : List (Fin k × Gp)) (x : Fin k × Gp) : V :=
  if t = i then (σ.2.2.1 j).1 + σ.2.2.2.1.1 j
  else if t = i' then (σ.2.2.1 j).2 + (σ.2.2.2.1.1 j + Δ)
  else if i < t ∧ x = ps.getD i (j, 0) then (σ.2.2.1 j).1 + σ.2.2.2.1.1 j
  else if i' < t ∧ x = ps.getD i' (j, 0) then (σ.2.2.1 j).2 + (σ.2.2.2.1.1 j + Δ)
  else σ.2.1 x.1 x.2

/-- The solver's run before `B`: answers and points of the key queries. -/
noncomputable def sim₀ (A : Gp) : ℕ → List V × List (Fin k × Gp)
  | 0 => ([], [])
  | t + 1 => ((sim₀ A t).1 ++
      [kOr C k j i i' Δ σ t (sim₀ A t).2 (P.Q₀ (amsgS g C k j σ A) (sim₀ A t).1)],
    (sim₀ A t).2 ++ [P.Q₀ (amsgS g C k j σ A) (sim₀ A t).1])

/-- The receiver messages in the solver's run. -/
noncomputable def msgBS (A : Gp) : Fin k → Gp :=
  P.msgB (amsgS g C k j σ A) (sim₀ g C k P j i i' Δ σ A P.n₀).1

open Classical in
/-- The masked pairs of the solver: the coin for `j`, the real ones for the others. -/
noncomputable def eS (A : Gp) : Fin k → V × V := fun j' ↦
  if j' = j then σ.2.2.1 j
  else (σ.2.2.2.1.1 j' + σ.2.1 j' (key g k σ.1 (msgBS g C k P j i i' Δ σ A) j' false),
    σ.2.2.2.1.1 j' + Δ + σ.2.1 j' (key g k σ.1 (msgBS g C k P j i i' Δ σ A) j' true))

/-- The solver's run of the steps: answers and points of the key queries. -/
noncomputable def sim₁ (A : Gp) : ℕ → List (V × V × D) × List (Fin k × Gp)
  | 0 => ([], [])
  | s + 1 =>
    let Q := P.step (amsgS g C k j σ A) (sim₀ g C k P j i i' Δ σ A P.n₀).1 (realM C k Δ σ.2.2.2)
      (eS g C k P j i i' Δ σ A) (sim₁ A s).1
    ((sim₁ A s).1 ++ [(extH σ.2.2.2.2.1 Q.1.1 Q.1.2,
        kOr C k j i i' Δ σ (P.n₀ + s) ((sim₀ g C k P j i i' Δ σ A P.n₀).2 ++ (sim₁ A s).2) Q.2.1,
        G Q.2.2)],
      (sim₁ A s).2 ++ [Q.2.1])

/-- The key points of the solver's run. -/
noncomputable def ptsS (A : Gp) : List (Fin k × Gp) :=
  (sim₀ g C k P j i i' Δ σ A P.n₀).2 ++ (sim₁ g C k G P j i i' Δ σ A P.n₁).2

/-- **The solver `S_{j,i,i'}`** with coins `(Δ, σ)`: the difference of the points of the key
queries `i` and `i'`. It does not use `σ.1 j`. -/
noncomputable def solver : Gp → Gp := fun A ↦
  ((ptsS g C k G P j i i' Δ σ A).getD i (j, 0)).2 - ((ptsS g C k G P j i i' Δ σ A).getD i' (j, 0)).2

end Solver

/-! ### The map to the solver's coins -/

open Classical in
/-- **The map `Ψ_j`.** It keeps the secrets other than `a_j` (setting `a_j` to `0`), replaces the
key hash at the two key points of `j` by the junk of `j`, and stores the real masked pair of `j`
in place of that junk. -/
noncomputable def Ψ (Δ : V) (j : Fin k) (ω : Ω q k C.length V Gp) : ZMod q × Ω q k C.length V Gp :=
  (ω.1 j,
    (Function.update ω.1 j 0,
      fun j' y ↦
        if j' = j ∧ y = key g k ω.1 (msgB g k P ω.1 ω.2.1) j false then (ω.2.2.1 j).1
        else if j' = j ∧ y = key g k ω.1 (msgB g k P ω.1 ω.2.1) j true then (ω.2.2.1 j).2
        else ω.2.1 j' y,
      Function.update ω.2.2.1 j (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1 j),
      ω.2.2.2))

end GcZk.CO

namespace GcZk.CO

open Adaptive Auth RO

variable {V R D Gp : Type*} {q : ℕ} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup Gp]
  [Module (ZMod q) Gp] (g : Gp) (C : Circuit) (k : ℕ) (G : V × R → D) (P : Prover k V R D Gp)

/-! ### The right guess -/

section Right

variable {Δ : V} {ω : Ω q k C.length V Gp} {j : Fin k} {i i' : ℕ}

omit [Module (ZMod 2) V] in
theorem amsgS_Ψ (A : Gp) (hA : A = ω.1 j • g) :
    amsgS g C k j (Ψ g C k P Δ j ω).2 A = msgA g k ω.1 := by
  funext j'
  by_cases h : j' = j
  · subst h; simp [amsgS, hA, msgA]
  · simp [amsgS, h, msgA, Ψ]

theorem add_add_self' (u w : V) : u + w + u = w := by
  rw [add_comm u w, add_assoc, add_self_eq_zero', add_zero]

/-- **The answers to the key queries.** With the right guess, the solver answers each key query
of the real run as the real key hash. -/
theorem kOr_eq (hb : BothAt g C k G P Δ ω j i i') {t : ℕ} :
    kOr C k j i i' Δ (Ψ g C k P Δ j ω).2 t ((List.range t).map (realKP g C k G P Δ ω))
      (realKP g C k G P Δ ω t) =
      ω.2.1 (realKP g C k G P Δ ω t).1 (realKP g C k G P Δ ω t).2 := by
  obtain ⟨-, -, hi, hfi, hi', hfi'⟩ := hb
  set K0 := key g k ω.1 (msgB g k P ω.1 ω.2.1) j false
  set K1 := key g k ω.1 (msgB g k P ω.1 ω.2.1) j true
  have hgi : ∀ {u : ℕ}, u < t → ((List.range t).map (realKP g C k G P Δ ω)).getD u (j, 0) =
      realKP g C k G P Δ ω u := fun hu ↦ by simp [List.getD_eq_getElem?_getD, hu]
  unfold kOr
  have e0 : ((Ψ g C k P Δ j ω).2.2.2.1 j).1 + (Ψ g C k P Δ j ω).2.2.2.2.1.1 j = ω.2.1 j K0 := by
    simp only [Ψ, Function.update_self, masked]; exact add_add_self' _ _
  have e1 : ((Ψ g C k P Δ j ω).2.2.2.1 j).2 + ((Ψ g C k P Δ j ω).2.2.2.2.1.1 j + Δ) =
      ω.2.1 j K1 := by
    simp only [Ψ, Function.update_self, masked]; exact add_add_self' _ _
  split_ifs with t1 t2 t3 t4
  · subst t1; rw [hi]; exact e0
  · subst t2; rw [hi']; exact e1
  · rw [t3.2, hgi t3.1, hi]; exact e0
  · rw [t4.2, hgi t4.1, hi']; exact e1
  · -- the query is not at a key point of `j`
    have n0 : realKP g C k G P Δ ω t ≠ (j, K0) := by
      intro h
      rcases lt_trichotomy t i with h' | h' | h'
      · exact hfi t h' h
      · exact t1 h'
      · exact t3 ⟨h', by rw [hgi h', hi, h]⟩
    have n1 : realKP g C k G P Δ ω t ≠ (j, K1) := by
      intro h
      rcases lt_trichotomy t i' with h' | h' | h'
      · exact hfi' t h' h
      · exact t2 h'
      · exact t4 ⟨h', by rw [hgi h', hi', h]⟩
    have c0 : ¬ ((realKP g C k G P Δ ω t).1 = j ∧ (realKP g C k G P Δ ω t).2 = K0) :=
      fun h ↦ n0 (Prod.ext h.1 h.2)
    have c1 : ¬ ((realKP g C k G P Δ ω t).1 = j ∧ (realKP g C k G P Δ ω t).2 = K1) :=
      fun h ↦ n1 (Prod.ext h.1 h.2)
    simp only [Ψ]
    exact (ite_eq_right c0).trans (ite_eq_right c1)

/-- **The run before `B`.** -/
theorem sim₀_eq (hb : BothAt g C k G P Δ ω j i i') {t : ℕ} (ht : t ≤ P.n₀) :
    sim₀ g C k P j i i' Δ (Ψ g C k P Δ j ω).2 (ω.1 j • g) t =
      (Com.ans (oK k ω.2.1) (P.Q₀ (msgA g k ω.1)) t,
        (List.range t).map (realKP g C k G P Δ ω)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih := ih (by omega)
    have hq : P.Q₀ (amsgS g C k j (Ψ g C k P Δ j ω).2 (ω.1 j • g))
        (sim₀ g C k P j i i' Δ (Ψ g C k P Δ j ω).2 (ω.1 j • g) t).1 =
        realKP g C k G P Δ ω t := by
      rw [amsgS_Ψ g C k P _ rfl, ih]
      simp only [realKP, show t < P.n₀ by omega, ↓reduceIte]
    rw [sim₀, hq, ih, kOr_eq g C k G P hb]
    simp only [Com.ans, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine Prod.ext ?_ rfl
    simp only [realKP, show t < P.n₀ by omega, ↓reduceIte, oK]

theorem msgBS_eq (hb : BothAt g C k G P Δ ω j i i') :
    msgBS g C k P j i i' Δ (Ψ g C k P Δ j ω).2 (ω.1 j • g) = msgB g k P ω.1 ω.2.1 := by
  rw [msgBS, sim₀_eq g C k G P hb le_rfl, amsgS_Ψ g C k P _ rfl]; rfl

theorem eS_eq (hb : BothAt g C k G P Δ ω j i i') :
    eS g C k P j i i' Δ (Ψ g C k P Δ j ω).2 (ω.1 j • g) =
      masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1 := by
  funext j'
  unfold eS
  rw [msgBS_eq g C k G P hb]
  by_cases h : j' = j
  · subst h; simp [Ψ]
  · have hk : ∀ c, key g k (Function.update ω.1 j 0) (msgB g k P ω.1 ω.2.1) j' c =
        key g k ω.1 (msgB g k P ω.1 ω.2.1) j' c := fun c ↦ by
      simp [key, msgA, Function.update_of_ne h]
    simp [h, Ψ, masked, hk]

omit [Module (ZMod 2) V] [AddCommGroup Gp] [Module (ZMod q) Gp] in
theorem range_map_add (f : ℕ → Fin k × Gp) (n s : ℕ) :
    (List.range n).map f ++ (List.range s).map (fun s' ↦ f (n + s')) =
      (List.range (n + s)).map f := by
  rw [List.range_add, List.map_append, List.map_map]; rfl

/-- **The steps.** With the right guess, the solver's run of the steps is the real one. -/
theorem sim₁_eq (hb : BothAt g C k G P Δ ω j i i') {s : ℕ} (hs : s ≤ P.n₁) :
    sim₁ g C k G P j i i' Δ (Ψ g C k P Δ j ω).2 (ω.1 j • g) s =
      (Com.ans (o₁ C k G ω.2.2.2.2.1 ω.2.1)
        (P.step (msgA g k ω.1) (ans₀ g k P ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
          (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1)) s,
        (List.range s).map (fun s' ↦ realKP g C k G P Δ ω (P.n₀ + s'))) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have ih := ih (by omega)
    have hQ : P.step (amsgS g C k j (Ψ g C k P Δ j ω).2 (ω.1 j • g))
        (sim₀ g C k P j i i' Δ (Ψ g C k P Δ j ω).2 (ω.1 j • g) P.n₀).1
        (realM C k Δ (Ψ g C k P Δ j ω).2.2.2.2) (eS g C k P j i i' Δ (Ψ g C k P Δ j ω).2
          (ω.1 j • g)) (sim₁ g C k G P j i i' Δ (Ψ g C k P Δ j ω).2 (ω.1 j • g) s).1 =
        realQ g C k G P Δ ω s := by
      rw [amsgS_Ψ g C k P _ rfl, sim₀_eq g C k G P hb le_rfl, eS_eq g C k G P hb, ih]; rfl
    have hkp : (realQ g C k G P Δ ω s).2.1 = realKP g C k G P Δ ω (P.n₀ + s) := by
      simp only [realKP, show ¬ P.n₀ + s < P.n₀ by omega, ↓reduceIte, Nat.add_sub_cancel_left]
      rfl
    simp only [sim₁]
    rw [hQ, sim₀_eq g C k G P hb le_rfl, ih]
    simp only [range_map_add, hkp]
    rw [kOr_eq g C k G P hb]
    simp only [Com.ans, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine Prod.ext ?_ rfl
    rw [← hkp]
    rfl

theorem ptsS_eq (hb : BothAt g C k G P Δ ω j i i') :
    ptsS g C k G P j i i' Δ (Ψ g C k P Δ j ω).2 (ω.1 j • g) =
      (List.range (P.n₀ + P.n₁)).map (realKP g C k G P Δ ω) := by
  rw [ptsS, sim₀_eq g C k G P hb le_rfl, sim₁_eq g C k G P hb le_rfl, range_map_add]

/-- **The solver wins** on `a_j` with the coins of the image. -/
theorem wins_Ψ (hb : BothAt g C k G P Δ ω j i i') :
    SqDH.Wins g (solver g C k G P j i i' Δ (Ψ g C k P Δ j ω).2) (ω.1 j) := by
  have hb' := hb
  obtain ⟨hi, hi', h1, -, h2, -⟩ := hb'
  unfold SqDH.Wins solver
  rw [ptsS_eq g C k G P hb]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    List.getElem?_range hi', Option.map_some, Option.getD_some, h1, h2]
  simp only [key, msgA, Bool.false_eq_true, ↓reduceIte]
  exact SqDH.keys_sub g (ω.1 j) _

end Right

/-! ### Injectivity and counting -/

/-- **Injectivity.** `Ψ_j` is injective on the randomness where the first queries at the two key
points of `j` are `i` and `i'` and `a_j ≠ 0` (so that the key points differ). -/
theorem Ψ_injOn (Δ : V) (j : Fin k) (i i' : ℕ) :
    Set.InjOn (Ψ g C k P Δ j) {ω : Ω q k C.length V Gp | BothAt g C k G P Δ ω j i i' ∧
      key g k ω.1 (msgB g k P ω.1 ω.2.1) j false ≠ key g k ω.1 (msgB g k P ω.1 ω.2.1) j true} := by
  rintro ⟨a1, HK1, J1, ρ1⟩ ⟨hb1, hne1⟩ ⟨a2, HK2, J2, ρ2⟩ ⟨hb2, hne2⟩ he
  have hx : a1 j = a2 j := congrArg Prod.fst he
  have hσ := congrArg Prod.snd he
  simp only [Ψ, Prod.mk.injEq] at hσ
  obtain ⟨hu, hK, hJ, hρ⟩ := hσ
  have ha : a1 = a2 := by
    funext j'
    by_cases h : j' = j
    · subst h; exact hx
    · have := congrFun hu j'; simpa [Function.update_of_ne h] using this
  subst ha hρ
  -- the receiver messages coincide: both are the solver's
  have hB : msgB g k P a1 HK1 = msgB g k P a1 HK2 := by
    rw [← msgBS_eq g C k G P hb1, ← msgBS_eq g C k G P hb2]
    congr 1
    simp only [Ψ, hK, hJ]
  have hne := hne1
  simp only at hne
  set K0 := key g k a1 (msgB g k P a1 HK1) j false with hK0
  set K1 := key g k a1 (msgB g k P a1 HK1) j true with hK1
  have hm := congrFun hJ j
  simp only [Function.update_self, masked, ← hB, ← hK0, ← hK1, Prod.mk.injEq] at hm
  have hH : HK1 = HK2 := by
    funext j' y
    have h := congrFun (congrFun hK j') y
    rw [← hB] at h
    by_cases c0 : j' = j ∧ y = K0
    · obtain ⟨rfl, rfl⟩ := c0; exact add_left_cancel hm.1
    · by_cases c1 : j' = j ∧ y = K1
      · obtain ⟨rfl, rfl⟩ := c1; exact add_left_cancel hm.2
      · simpa [c0, c1, ← hK0, ← hK1] using h
  subst hH
  have hJJ : J1 = J2 := by
    funext j'
    by_cases h : j' = j
    · subst h
      have h0 := congrFun (congrFun hK j') K0
      have h1 := congrFun (congrFun hK j') K1
      simp only [← hK0, ← hK1, true_and, ↓reduceIte, Ne.symm hne] at h0 h1
      exact Prod.ext h0 (by simpa [Ne.symm hne] using h1)
    · simpa [Function.update_of_ne h] using congrFun hJ j'
  subst hJJ
  rfl

open Classical in
/-- **Both key points, counting form.** For fixed `G` and `Δ`, the real randomness where the prover
queries both key points of some input and no secret is `0` is at most the sum, over the input `j`
and the guesses `i ≠ i' < n₀ + n₁` (the two key points are distinct, so their first queries
are), of the pairs `(x, σ)` (with `σ.1 j = 0`, so that the coins do not
contain `a_j`) on which the solver `S_{j,i,i'}` wins. -/
theorem card_both_le [Fintype V] [DecidableEq V] [Fintype Gp] [DecidableEq Gp] [NeZero q]
    [Fact q.Prime] (hg : Function.Bijective fun b : ZMod q ↦ b • g) (Δ : V) :
    (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Both g C k G P Δ ω ∧ ¬ Zero C k ω).card ≤
      ∑ j : Fin k, ∑ ii ∈ (Finset.range (P.n₀ + P.n₁)).offDiag,
        (Finset.univ.filter fun xσ : ZMod q × Ω q k C.length V Gp ↦ xσ.2.1 j = 0 ∧
          SqDH.Wins g (solver g C k G P j ii.1 ii.2 Δ xσ.2) xσ.1).card := by
  -- the first queries at the two key points
  have first : ∀ (ω : Ω q k C.length V Gp) (j : Fin k) (c : Bool), HitsKey g C k G P Δ ω j c →
      ∃ t < P.n₀ + P.n₁, realKP g C k G P Δ ω t = (j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j c) ∧
        ∀ t' < t, realKP g C k G P Δ ω t' ≠ (j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j c) := by
    intro ω j c h
    have hex : ∃ t, t < P.n₀ + P.n₁ ∧
        realKP g C k G P Δ ω t = (j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j c) := by
      rcases h with ⟨t, ht, hq⟩ | ⟨s, hs, hq⟩
      · exact ⟨t, by omega, by simp only [realKP, ht, ↓reduceIte]; exact hq⟩
      · refine ⟨P.n₀ + s, by omega, ?_⟩
        simp only [realKP, show ¬ P.n₀ + s < P.n₀ by omega, ↓reduceIte, Nat.add_sub_cancel_left]
        exact hq
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun t' ht' h' ↦ ?_⟩
    exact Nat.find_min hex ht' ⟨by have := (Nat.find_spec hex).1; omega, h'⟩
  refine le_trans (Finset.card_le_card (t := Finset.univ.biUnion fun j : Fin k ↦
      (Finset.range (P.n₀ + P.n₁)).offDiag.biUnion fun ii ↦
        Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ BothAt g C k G P Δ ω j ii.1 ii.2 ∧
          key g k ω.1 (msgB g k P ω.1 ω.2.1) j false ≠
            key g k ω.1 (msgB g k P ω.1 ω.2.1) j true) fun ω hω ↦ ?_) ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    obtain ⟨⟨j, h0, h1⟩, hz⟩ := hω
    obtain ⟨i, hi, e0, f0⟩ := first ω j false h0
    obtain ⟨i', hi', e1, f1⟩ := first ω j true h1
    have ha : ω.1 j ≠ 0 := fun h ↦ hz ⟨j, h⟩
    have hne : i ≠ i' := by
      rintro rfl
      exact key_ne g k hg _ ha (congrArg Prod.snd (e0.symm.trans e1))
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_offDiag,
      Finset.mem_range, Finset.mem_filter]
    exact ⟨j, (i, i'), ⟨hi, hi', hne⟩, ⟨hi, hi', e0, f0, e1, f1⟩, key_ne g k hg _ ha⟩
  · refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ ↦
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ii _ ↦ ?_))
    refine Finset.card_le_card_of_injOn (Ψ g C k P Δ j) (fun ω hω ↦ ?_)
      ((Ψ_injOn g C k G P Δ j ii.1 ii.2).mono fun ω hω ↦ ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hω ⊢
      exact ⟨by simp [Ψ], wins_Ψ g C k G P hω.1⟩
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hω ⊢
      exact hω

end GcZk.CO
