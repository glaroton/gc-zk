/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.Authenticity

/-!
# Authenticity in the random oracle model

The hash is a uniformly random function `H : Fin n → V → V` (`n` = number of nodes) and `Δ` is
uniform on `V \ {0}`. An adversary sees the material, makes `q` adaptive queries to `H`, and
outputs a label. It wins if the label is the inactive output label `active + Δ`.

## Main result

* `GcZk.RO.rom_bound`: summed over `Δ ≠ 0`, the hash functions for which the adversary wins
  number at most `(q + 1) |V^(n × V)|`. So the success probability is at most
  `(q + 1) / (|V| - 1)`.

The active labels of the inputs and constants are fixed parameters. In the real scheme they are
`L + x Δ` with uniform zero-labels `L`, hence uniform and independent of `Δ`. A bound for every
fixed value is a bound on average. By `GcZk.Auth.garble_eq_idealMaterial`, the material here
(`realMat`) is the material of `GcZk.garble` for any seed with these active labels.

## Proof

Identical until bad. The *simulated* game computes the material with independent uniform pads
`K` instead of `H(i, S_i + Δ) + c_i Δ`, so nothing the adversary sees depends on `Δ`. For a
fixed `Δ`, the map `(H, J) ↦ (H_sim, K)` that moves the values of `H` at the inactive points
`(i, S_i + Δ)` into the pads is injective. A real win becomes a simulated win or a query at an
inactive point (`SimBad`). For fixed `(H_sim, K)`, a simulated win fixes `Δ`, and each query
hits the inactive points for at most one `Δ`. That gives at most `q + 1` values of `Δ`.
-/

namespace GcZk.RO

open Auth

variable {V : Type*} [AddCommGroup V]

/-! ### The trace of the ideal garbler -/

/-- The wires of the ideal garbler, which runs alongside the evaluator. -/
def idealWiresAux (H : ℕ → V → V) (inp : ℕ → Wire V) (Ac : ℕ → Bool → V)
    (pad : ℕ → V → Bool → V) : Circuit → List (Wire V) → List (Wire V)
  | [], ws => ws
  | n :: ns, ws =>
    idealWiresAux H inp Ac pad ns (ws ++ [evalNode H inp ws n (idealNode H Ac pad ws n)])

/-- The active selector label and the candidate XOR of a multiplexer. -/
def nodeMux (ws : List (Wire V)) : Node → Option (V × Bool)
  | .mux s z o => some ((ws.getD s (false, 0)).2,
      (ws.getD z (false, 0)).1 ^^ (ws.getD o (false, 0)).1)
  | _ => none

/-- `muxAt … i` is `some (S, c)` if the node at position `i` is a multiplexer with active
selector label `S` and candidate XOR `c`. The garbler reads `H` at `(i, S)` and the pad at
`(i, S, c)`. In the real scheme the *inactive point* is `(i, S + Δ)`. -/
def muxAt (H : ℕ → V → V) (inp : ℕ → Wire V) (Ac : ℕ → Bool → V) (pad : ℕ → V → Bool → V) :
    Circuit → List (Wire V) → ℕ → Option (V × Bool)
  | [], _, _ => none
  | n :: ns, ws, i => if i = ws.length then nodeMux ws n else
      muxAt H inp Ac pad ns (ws ++ [evalNode H inp ws n (idealNode H Ac pad ws n)]) i

theorem muxAt_lt (H : ℕ → V → V) (inp : ℕ → Wire V) (Ac : ℕ → Bool → V)
    (pad : ℕ → V → Bool → V) (C : Circuit) :
    ∀ {ws : List (Wire V)} {i : ℕ} {x : V × Bool}, muxAt H inp Ac pad C ws i = some x →
      ws.length ≤ i ∧ i < ws.length + C.length := by
  induction C with
  | nil => intro _ _ _ h; simp [muxAt] at h
  | cons n ns ih =>
    intro ws i x h
    simp only [muxAt] at h
    split_ifs at h with hi
    · simp [hi]
    · have := ih h; simp at this; simp; omega

theorem evalAux_ideal (H : ℕ → V → V) (inp : ℕ → Wire V) (Ac : ℕ → Bool → V)
    (pad : ℕ → V → Bool → V) (C : Circuit) : ∀ ws : List (Wire V),
      evalAux H inp C (idealAux H inp Ac pad C ws) ws = idealWiresAux H inp Ac pad C ws := by
  induction C with
  | nil => intro ws; simp [evalAux, idealWiresAux]
  | cons n ns ih => intro ws; simp only [idealAux, evalAux, idealWiresAux]; exact ih _

theorem node_congr {H H' : ℕ → V → V} {pad pad' : ℕ → V → Bool → V} (inp : ℕ → Wire V)
    (Ac : ℕ → Bool → V) (ws : List (Wire V)) (n : Node)
    (h : ∀ S c, nodeMux ws n = some (S, c) →
      H' ws.length S = H ws.length S ∧ pad' ws.length S c = pad ws.length S c) :
    idealNode H' Ac pad' ws n = idealNode H Ac pad ws n ∧
      evalNode H' inp ws n (idealNode H Ac pad ws n) =
        evalNode H inp ws n (idealNode H Ac pad ws n) := by
  cases n with
  | mux s z o =>
    obtain ⟨h1, h2⟩ := h _ _ rfl
    exact ⟨by simp only [idealNode, muxT, h1, h2], by simp only [idealNode, evalNode, h1]⟩
  | _ => simp [idealNode, evalNode]

/-- **Walk congruence.** The ideal garbler reads `H` and the pad only at the points `muxAt`
names. Two runs that agree there produce the same material, wires and trace. -/
theorem walk_congr (inp : ℕ → Wire V) (Ac : ℕ → Bool → V) (C : Circuit) :
    ∀ {H H' : ℕ → V → V} {pad pad' : ℕ → V → Bool → V} {ws : List (Wire V)},
      (∀ i S c, muxAt H inp Ac pad C ws i = some (S, c) →
        H' i S = H i S ∧ pad' i S c = pad i S c) →
      idealAux H' inp Ac pad' C ws = idealAux H inp Ac pad C ws ∧
        idealWiresAux H' inp Ac pad' C ws = idealWiresAux H inp Ac pad C ws ∧
        muxAt H' inp Ac pad' C ws = muxAt H inp Ac pad C ws := by
  induction C with
  | nil => intro _ _ _ _ _ _; exact ⟨rfl, rfl, rfl⟩
  | cons n ns ih =>
    intro H H' pad pad' ws h
    have hn := node_congr (H := H) (H' := H') (pad := pad) (pad' := pad') inp Ac ws n
      (fun S c hm ↦ h ws.length S c (by simp [muxAt, hm]))
    obtain ⟨e1, e2, e3⟩ := ih (H := H) (H' := H') (pad := pad) (pad' := pad')
      (ws := ws ++ [evalNode H inp ws n (idealNode H Ac pad ws n)]) (fun i S c hm ↦ by
        have hi : i ≠ ws.length := by have := (muxAt_lt _ _ _ _ _ hm).1; simp at this; omega
        exact h i S c (by simp [muxAt, hi, hm]))
    refine ⟨?_, ?_, ?_⟩
    · simp only [idealAux, hn.1, hn.2, e1]
    · simp only [idealWiresAux, hn.1, hn.2, e2]
    · funext i
      simp only [muxAt, hn.1, hn.2, e3]

/-! ### Oracles and adversaries -/

/-- A hash on `n` positions, extended by `0`. -/
def extH {n : ℕ} (H : Fin n → V → V) : ℕ → V → V :=
  fun i y ↦ if h : i < n then H ⟨i, h⟩ y else 0

/-- Pads on `n` positions, extended by `0`. -/
def extK {n : ℕ} (K : Fin n → V) : ℕ → V → Bool → V :=
  fun i _ _ ↦ if h : i < n then K ⟨i, h⟩ else 0

/-- The real pads `H(i, S + Δ) + c Δ` (`GcZk.Auth.realPad` with `Δ` explicit). -/
def rpad (H : ℕ → V → V) (Δ : V) : ℕ → V → Bool → V :=
  fun i S c ↦ H i (S + Δ) + if c then Δ else 0

/-- A deterministic adversary making adaptive queries to the hash. A randomized adversary is a
family of these indexed by its coins. -/
structure QAdv (V : Type*) where
  query : List (Material V) → List V → ℕ × V
  guess : List (Material V) → List V → V

/-- The answers to the first `k` queries, with oracle `O` and material `M`. -/
def answers (O : ℕ → V → V) (A : QAdv V) (M : List (Material V)) : ℕ → List V
  | 0 => []
  | k + 1 => answers O A M k ++
      [O (A.query M (answers O A M k)).1 (A.query M (answers O A M k)).2]

omit [AddCommGroup V] in
/-- **Identical until bad.** Oracles that agree at every query asked give the same answers. -/
theorem answers_congr (O O' : ℕ → V → V) (A : QAdv V) (M : List (Material V)) (q : ℕ)
    (h : ∀ k < q, O (A.query M (answers O' A M k)).1 (A.query M (answers O' A M k)).2 =
      O' (A.query M (answers O' A M k)).1 (A.query M (answers O' A M k)).2) :
    answers O A M q = answers O' A M q := by
  induction q with
  | zero => rfl
  | succ k ih =>
    have e := ih fun j hj ↦ h j (by omega)
    simp only [answers, e, h k (by omega)]

/-! ### The real and the simulated game -/

section Games

variable (inp : ℕ → Wire V) (Ac : ℕ → Bool → V) (C : Circuit) (out q : ℕ) (A : QAdv V)

/-- The real material for the hash `H` and offset `Δ`. -/
def realMat (Δ : V) (H : ℕ → V → V) : List (Material V) := idealMaterial H inp Ac (rpad H Δ) C

/-- The adversary wins the real game. -/
def RealWin (Δ : V) (HR : Fin C.length → V → V) : Prop :=
  A.guess (realMat inp Ac C Δ (extH HR)) (answers (extH HR) A (realMat inp Ac C Δ (extH HR)) q) =
    activeOut (extH HR) inp C out (realMat inp Ac C Δ (extH HR)) + Δ

/-- The simulated material: independent pads, no `Δ`. -/
def simMat (p : (Fin C.length → V → V) × (Fin C.length → V)) : List (Material V) :=
  idealMaterial (extH p.1) inp Ac (extK p.2) C

/-- The `k`-th query of the adversary in the simulated game. -/
def simQuery (p : (Fin C.length → V → V) × (Fin C.length → V)) (k : ℕ) : ℕ × V :=
  A.query (simMat inp Ac C p) (answers (extH p.1) A (simMat inp Ac C p) k)

/-- The adversary wins the simulated game for the offset `Δ`. -/
def SimWin (Δ : V) (p : (Fin C.length → V → V) × (Fin C.length → V)) : Prop :=
  A.guess (simMat inp Ac C p) (answers (extH p.1) A (simMat inp Ac C p) q) =
    activeOut (extH p.1) inp C out (simMat inp Ac C p) + Δ

/-- A query of the simulated game hits an inactive point `(i, S_i + Δ)`. -/
def SimBad (Δ : V) (p : (Fin C.length → V → V) × (Fin C.length → V)) : Prop :=
  ∃ k < q, ∃ S c, muxAt (extH p.1) inp Ac (extK p.2) C [] (simQuery inp Ac C A p k).1 =
    some (S, c) ∧ (simQuery inp Ac C A p k).2 = S + Δ

end Games

/-! ### From the real to the simulated game -/

section Injection

variable (inp : ℕ → Wire V) (Ac : ℕ → Bool → V) (C : Circuit) (Δ : V)

/-- The trace of the real game. -/
def realMux (HR : Fin C.length → V → V) : ℕ → Option (V × Bool) :=
  muxAt (extH HR) inp Ac (rpad (extH HR) Δ) C []

open Classical in
/-- Given a trace `m`, move the values of `H` at the inactive points `(i, S_i + Δ)` into the
pads, and put `J` in their place. -/
noncomputable def moveInactive (m : ℕ → Option (V × Bool))
    (p : (Fin C.length → V → V) × (Fin C.length → V)) :
    (Fin C.length → V → V) × (Fin C.length → V) :=
  (fun i y ↦ if ∃ S c, m i = some (S, c) ∧ y = S + Δ then p.2 i else p.1 i y,
    fun i ↦ (m i).elim (p.2 i) (fun Sc ↦ p.1 i (Sc.1 + Δ) + if Sc.2 then Δ else 0))

/-- The map from the real randomness `(H, J)` to the simulated randomness `(H_sim, K)`. -/
noncomputable def toSim (p : (Fin C.length → V → V) × (Fin C.length → V)) :
    (Fin C.length → V → V) × (Fin C.length → V) :=
  moveInactive C Δ (realMux inp Ac C Δ p.1) p

theorem toSim_walk (hΔ : Δ ≠ 0) (p : (Fin C.length → V → V) × (Fin C.length → V)) :
    idealAux (extH (toSim inp Ac C Δ p).1) inp Ac (extK (toSim inp Ac C Δ p).2) C [] =
        idealAux (extH p.1) inp Ac (rpad (extH p.1) Δ) C [] ∧
      idealWiresAux (extH (toSim inp Ac C Δ p).1) inp Ac (extK (toSim inp Ac C Δ p).2) C [] =
        idealWiresAux (extH p.1) inp Ac (rpad (extH p.1) Δ) C [] ∧
      muxAt (extH (toSim inp Ac C Δ p).1) inp Ac (extK (toSim inp Ac C Δ p).2) C [] =
        realMux inp Ac C Δ p.1 := by
  apply walk_congr
  intro i S c hm
  have hi : i < C.length := by simpa using (muxAt_lt _ _ _ _ _ hm).2
  have hm' : realMux inp Ac C Δ p.1 i = some (S, c) := hm
  refine ⟨?_, ?_⟩
  · have hne : ¬ ∃ S' c', realMux inp Ac C Δ p.1 i = some (S', c') ∧ S = S' + Δ := by
      rintro ⟨S', c', h1, h2⟩
      rw [hm'] at h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
      exact hΔ (by simpa using h2)
    simp only [extH, dite_eq_left hi, toSim, moveInactive]
    exact ite_eq_right hne
  · simp only [extK, extH, dite_eq_left hi, toSim, moveInactive, rpad]
    rw [show realMux inp Ac C Δ p.1 ↑(⟨i, hi⟩ : Fin C.length) = some (S, c) from hm']
    rfl

theorem moveInactive_injective (m : ℕ → Option (V × Bool)) :
    Function.Injective (moveInactive C Δ m) := by
  intro p p' h
  have h1 : ∀ i y, (moveInactive C Δ m p).1 i y = (moveInactive C Δ m p').1 i y :=
    fun i y ↦ by rw [h]
  have h2 : ∀ i, (moveInactive C Δ m p).2 i = (moveInactive C Δ m p').2 i :=
    fun i ↦ by rw [h]
  simp only [moveInactive] at h1 h2
  have hH : p.1 = p'.1 := by
    funext i y
    by_cases hb : ∃ S c, m i = some (S, c) ∧ y = S + Δ
    · obtain ⟨S, c, hs, rfl⟩ := hb
      have e2 := h2 i
      simp only [hs, Option.elim_some] at e2
      exact add_right_cancel e2
    · have e1 := h1 i y
      rwa [ite_eq_right hb, ite_eq_right hb] at e1
  refine Prod.ext hH (funext fun i ↦ ?_)
  cases hs : m i with
  | none => simpa [hs] using h2 i
  | some Sc =>
    have hb : ∃ S c, m i = some (S, c) ∧ Sc.1 + Δ = S + Δ := ⟨Sc.1, Sc.2, by simp [hs], rfl⟩
    have e1 := h1 i (Sc.1 + Δ)
    rwa [ite_eq_left hb, ite_eq_left hb] at e1

theorem toSim_injective (hΔ : Δ ≠ 0) : Function.Injective (toSim inp Ac C Δ) := by
  intro p p' h
  have m1 := (toSim_walk inp Ac C Δ hΔ p).2.2
  have m2 := (toSim_walk inp Ac C Δ hΔ p').2.2
  rw [h] at m1
  have hm : realMux inp Ac C Δ p.1 = realMux inp Ac C Δ p'.1 := m1.symm.trans m2
  have h' : moveInactive C Δ (realMux inp Ac C Δ p'.1) p =
      moveInactive C Δ (realMux inp Ac C Δ p'.1) p' := by
    have := h; unfold toSim at this; rwa [hm] at this
  exact moveInactive_injective C Δ _ h'

theorem activeOut_ideal (H : ℕ → V → V) (pad : ℕ → V → Bool → V) (out : ℕ) :
    activeOut H inp C out (idealMaterial H inp Ac pad C) =
      ((idealWiresAux H inp Ac pad C []).getD out (false, 0)).2 := by
  simp [activeOut, eval, idealMaterial, evalAux_ideal]

/-- A real win is a simulated win or a simulated query at an inactive point. -/
theorem realWin_toSim (hΔ : Δ ≠ 0) (out q : ℕ) (A : QAdv V)
    (p : (Fin C.length → V → V) × (Fin C.length → V)) (hw : RealWin inp Ac C out q A Δ p.1) :
    SimWin inp Ac C out q A Δ (toSim inp Ac C Δ p) ∨
      SimBad inp Ac C q A Δ (toSim inp Ac C Δ p) := by
  obtain ⟨w1, w2, w3⟩ := toSim_walk inp Ac C Δ hΔ p
  have hM : simMat inp Ac C (toSim inp Ac C Δ p) = realMat inp Ac C Δ (extH p.1) := w1
  have hout : activeOut (extH (toSim inp Ac C Δ p).1) inp C out
        (simMat inp Ac C (toSim inp Ac C Δ p)) =
      activeOut (extH p.1) inp C out (realMat inp Ac C Δ (extH p.1)) := by
    rw [simMat, realMat, activeOut_ideal, activeOut_ideal, w2]
  by_cases hb : SimBad inp Ac C q A Δ (toSim inp Ac C Δ p)
  · exact Or.inr hb
  left
  have hans : answers (extH p.1) A (realMat inp Ac C Δ (extH p.1)) q =
      answers (extH (toSim inp Ac C Δ p).1) A (realMat inp Ac C Δ (extH p.1)) q := by
    apply answers_congr
    intro k hk
    set Q := A.query (realMat inp Ac C Δ (extH p.1))
      (answers (extH (toSim inp Ac C Δ p).1) A (realMat inp Ac C Δ (extH p.1)) k)
    by_cases hi : Q.1 < C.length
    · have hQ : simQuery inp Ac C A (toSim inp Ac C Δ p) k = Q := by
        simp only [simQuery, hM, Q]
      have hnb : ¬ ∃ S c, realMux inp Ac C Δ p.1 Q.1 = some (S, c) ∧ Q.2 = S + Δ := by
        rintro ⟨S, c, h1, h2⟩
        exact hb ⟨k, hk, S, c, by rw [w3, hQ]; exact h1, by rw [hQ]; exact h2⟩
      simp only [extH, dite_eq_left hi, toSim, moveInactive]
      exact (ite_eq_right hnb).symm
    · simp [extH, hi]
  unfold SimWin
  rw [hout, hM, ← hans]
  exact hw

end Injection

/-! ### Counting -/

section Counting

variable [Fintype V] (inp : ℕ → Wire V) (Ac : ℕ → Bool → V) (C : Circuit) (out q : ℕ)
  (A : QAdv V)

open Classical in
/-- For fixed simulated randomness, at most `q + 1` offsets give a simulated win or a hit. -/
theorem card_simWin_or_bad (p : (Fin C.length → V → V) × (Fin C.length → V)) :
    (Finset.univ.filter fun Δ : V ↦ SimWin inp Ac C out q A Δ p ∨
      SimBad inp Ac C q A Δ p).card ≤ q + 1 := by
  set g := A.guess (simMat inp Ac C p) (answers (extH p.1) A (simMat inp Ac C p) q)
  set a := activeOut (extH p.1) inp C out (simMat inp Ac C p)
  let hit : ℕ → V := fun k ↦ (simQuery inp Ac C A p k).2 -
    ((muxAt (extH p.1) inp Ac (extK p.2) C [] (simQuery inp Ac C A p k).1).map Prod.fst).getD 0
  calc (Finset.univ.filter fun Δ : V ↦ SimWin inp Ac C out q A Δ p ∨
        SimBad inp Ac C q A Δ p).card
      ≤ (insert (g - a) ((Finset.range q).image hit)).card := by
        apply Finset.card_le_card
        intro Δ hΔ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΔ
        rcases hΔ with hw | ⟨k, hk, S, c, h1, h2⟩
        · refine Finset.mem_insert.2 (Or.inl ?_)
          change g = a + Δ at hw
          rw [hw]; abel
        · refine Finset.mem_insert.2 (Or.inr (Finset.mem_image.2 ⟨k, by simpa using hk, ?_⟩))
          simp only [hit, h1, h2, Option.map_some, Option.getD_some]
          abel
    _ ≤ (Finset.range q).card + 1 :=
          (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
    _ = q + 1 := by simp

open Classical in
/-- **Authenticity in the random oracle model.** Summed over the offsets `Δ ≠ 0`, the hash
functions for which a `q`-query adversary outputs the inactive output label number at most
`(q + 1)` times all hash functions. With `Δ` uniform on `V \ {0}` and `H` uniform, the success
probability is at most `(q + 1) / (|V| - 1)`. -/
theorem rom_bound :
    ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun HR : Fin C.length → V → V ↦ RealWin inp Ac C out q A Δ HR).card ≤
    (q + 1) * Fintype.card (Fin C.length → V → V) := by
  set P := (Fin C.length → V → V) × (Fin C.length → V)
  have hK : 0 < Fintype.card (Fin C.length → V) := Fintype.card_pos
  -- Each offset: real wins, times the junk, inject into simulated wins or hits.
  have step : ∀ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun HR : Fin C.length → V → V ↦ RealWin inp Ac C out q A Δ HR).card *
          Fintype.card (Fin C.length → V) ≤
        (Finset.univ.filter fun p : P ↦ SimWin inp Ac C out q A Δ p ∨
          SimBad inp Ac C q A Δ p).card := by
    intro Δ hΔ
    have hΔ : Δ ≠ 0 := by simpa using hΔ
    have hprod : (Finset.univ.filter fun HR : Fin C.length → V → V ↦
          RealWin inp Ac C out q A Δ HR).card * Fintype.card (Fin C.length → V) =
        (Finset.univ.filter fun p : P ↦ RealWin inp Ac C out q A Δ p.1).card := by
      rw [← Finset.card_univ (α := Fin C.length → V), ← Finset.card_product]
      congr 1
      ext p; simp
    rw [hprod]
    refine Finset.card_le_card_of_injOn (toSim inp Ac C Δ) (fun p hp ↦ ?_)
      ((toSim_injective inp Ac C Δ hΔ).injOn)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    exact realWin_toSim inp Ac C Δ hΔ out q A p hp
  -- Swap the sum and count offsets per simulated randomness.
  have swap : ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun p : P ↦ SimWin inp Ac C out q A Δ p ∨
        SimBad inp Ac C q A Δ p).card ≤ (q + 1) * Fintype.card P := by
    calc _ ≤ ∑ Δ : V, (Finset.univ.filter fun p : P ↦ SimWin inp Ac C out q A Δ p ∨
            SimBad inp Ac C q A Δ p).card :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ∑ p : P, (Finset.univ.filter fun Δ : V ↦ SimWin inp Ac C out q A Δ p ∨
            SimBad inp Ac C q A Δ p).card := by
          simp only [Finset.card_filter]
          exact Finset.sum_comm
      _ ≤ ∑ _p : P, (q + 1) := Finset.sum_le_sum fun p _ ↦ card_simWin_or_bad inp Ac C out q A p
      _ = (q + 1) * Fintype.card P := by simp [mul_comm]
  have total := (Finset.sum_le_sum step).trans swap
  rw [← Finset.sum_mul, Fintype.card_prod, ← mul_assoc] at total
  exact Nat.le_of_mul_le_mul_right total hK

end Counting

end GcZk.RO
