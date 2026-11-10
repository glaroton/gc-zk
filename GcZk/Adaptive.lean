/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.RandomOracle

/-!
# Adaptive authenticity: the real game without bad queries

In the adaptive authenticity game the adversary sees the material first, and then interleaves
queries to the hash with *label requests*: for an input `j` of its choice and a bit `b`, it
receives the label `L_j + b Δ`. Only the first request of an input counts; later requests of the
same input are answered with the label of the first bit. The requested bits form the input `x`
(unrequested bits are `0`), and the adversary wins if it outputs the inactive output label for `x`.

We call a query *bad* if it hits an inactive point `(i, S_i + Δ)` of the final `x`, where `S_i` is
the active label of the selector of the multiplexer at position `i`.

## Main results

* `GcZk.Adaptive.win_not_bad_bound`: summed over `Δ ≠ 0`, the randomness for which the adversary
  wins without a bad query is at most all the randomness. So the probability of winning without a
  bad query is at most `1 / (|V| - 1)`.
* `GcZk.Adaptive.win_le`: the probability of winning is at most `1 / (|V| - 1)` plus the probability
  of a bad query.

## Proof

The *simulated game* sends uniform ciphertexts and uniform active constant labels, answers each
label request with a uniform label whatever the bit, and answers queries with a random function.
Nothing in it depends on `Δ`, so for each simulated randomness at most one `Δ` makes the adversary
win.

For each `Δ ≠ 0`, the map `toAdSim` from the real randomness to the simulated one keeps the
requested labels, the active constant labels and the ciphertexts, and moves the hash values at the
inactive points of the final `x` into a junk component (`GcZk.RO.toSim`). Without a bad query the
simulated game on the image runs exactly as the real game (`simRun_toAdSim`). The image therefore
determines `x`, hence the zero-labels, and then the hash, so the map is injective on these runs
(`toAdSim_injOn`), and a real win becomes a simulated win (`simWin_toAdSim`).

The probability of a bad query is bounded in `GcZk.AdaptiveBound` (`GcZk.Adaptive.card_bad_le`),
which gives adaptive authenticity (`GcZk.Adaptive.adaptive_authenticity`).
-/

namespace GcZk.Adaptive

open Auth RO

variable {V : Type*} [AddCommGroup V]

/-! ### Interaction -/

/-- An action of the adversary: a query to the hash at gate `i`, or a request for the label of
the bit `b` of the input `j`. -/
inductive Act (V : Type*)
  | query (i : ℕ) (y : V)
  | req (j : ℕ) (b : Bool)

/-- A deterministic adaptive adversary. It sees the material and the answers so far. A randomized
adversary is a family of these indexed by its coins. -/
structure AAdv (V : Type*) where
  act : List (Material V) → List V → Act V
  guess : List (Material V) → List V → V

/-- The first `k` actions and answers, with the oracle `O`, which sees the earlier actions. -/
def run (O : List (Act V) → Act V → V) (A : AAdv V) (M : List (Material V)) :
    ℕ → List (Act V) × List V
  | 0 => ([], [])
  | k + 1 => ((run O A M k).1 ++ [A.act M (run O A M k).2],
      (run O A M k).2 ++ [O (run O A M k).1 (A.act M (run O A M k).2)])

omit [AddCommGroup V] in
/-- Oracles that agree on every action taken give the same run. -/
theorem run_congr (O O' : List (Act V) → Act V → V) (A : AAdv V) (M : List (Material V))
    (q : ℕ) (h : ∀ k < q, O (run O' A M k).1 (A.act M (run O' A M k).2) =
      O' (run O' A M k).1 (A.act M (run O' A M k).2)) :
    run O A M q = run O' A M q := by
  induction q with
  | zero => rfl
  | succ k ih =>
    have e := ih fun j hj ↦ h j (by omega)
    rw [run, run, e, h k (by omega)]

omit [AddCommGroup V] in
theorem run_prefix (O : List (Act V) → Act V → V) (A : AAdv V) (M : List (Material V))
    (k : ℕ) : ∀ d, ∃ rest, (run O A M (k + d)).1 = (run O A M k).1 ++ rest := by
  intro d
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    obtain ⟨rest, hr⟩ := ih
    exact ⟨rest ++ [A.act M (run O A M (k + d)).2], by
      rw [← add_assoc, run, hr, List.append_assoc]⟩

/-- The bit of the first request of the input `j`, if any. -/
def bitOf : List (Act V) → ℕ → Option Bool
  | [], _ => none
  | .req j' b :: as, j => if j' = j then some b else bitOf as j
  | .query _ _ :: as, j => bitOf as j

omit [AddCommGroup V] in
theorem bitOf_append (l l' : List (Act V)) (j : ℕ) :
    bitOf (l ++ l') j = (bitOf l j).or (bitOf l' j) := by
  induction l with
  | nil => simp [bitOf]
  | cons a l ih =>
    cases a with
    | query i y => simp [bitOf, ih]
    | req j' b => by_cases h : j' = j <;> simp [bitOf, h, ih]

/-- The input chosen by the actions `as`, on the inputs `j < m`. -/
def xOf (m : ℕ) (as : List (Act V)) (j : ℕ) : Bool :=
  if j < m then (bitOf as j).getD false else false

omit [AddCommGroup V] in
/-- At a request, the bit of the final input is the bit already requested, or the new one. -/
theorem xOf_run (O : List (Act V) → Act V → V) (A : AAdv V) (M : List (Material V))
    {m q k : ℕ} (hk : k < q) {j : ℕ} (hj : j < m) {b : Bool}
    (ha : A.act M (run O A M k).2 = .req j b) :
    xOf m (run O A M q).1 j = (bitOf (run O A M k).1 j).getD b := by
  obtain ⟨rest, hr⟩ := run_prefix O A M (k + 1) (q - (k + 1))
  rw [show k + 1 + (q - (k + 1)) = q by omega] at hr
  simp only [xOf, hj, ↓reduceIte]
  rw [hr, run, ha, bitOf_append, bitOf_append]
  cases bitOf (run O A M k).1 j <;> simp [bitOf]

/-! ### Extension by zero -/

/-- A function on `Fin k`, extended by `0`. -/
def extL {k : ℕ} (L : Fin k → V) : ℕ → V := fun j ↦ if h : j < k then L ⟨j, h⟩ else 0

/-! ### The shape of the material -/

theorem garbleAux_length (H : ℕ → V → V) (σ : Seed V) (C : Circuit) :
    ∀ bs : List V, (garbleAux H σ C bs).2.length = C.length := by
  induction C with
  | nil => intro _; rfl
  | cons n ns ih => intro bs; simp [garbleAux, ih]

/-- The material at position `k` is the material of node `k`, garbled after `k` zero-labels. -/
theorem garbleAux_getElem? (H : ℕ → V → V) (σ : Seed V) (C : Circuit) :
    ∀ (bs : List V) (k : ℕ) (hk : k < C.length), ∃ bs' : List V,
      bs'.length = bs.length + k ∧
        (garbleAux H σ C bs).2[k]? = some (garbleNode H σ bs' C[k]).2 := by
  induction C with
  | nil => intro _ k hk; simp at hk
  | cons n ns ih =>
    intro bs k hk
    cases k with
    | zero => exact ⟨bs, by simp, by simp [garbleAux]⟩
    | succ k =>
      obtain ⟨bs', h1, h2⟩ := ih (bs ++ [(garbleNode H σ bs n).1]) k (by simpa using hk)
      exact ⟨bs', by simp [h1]; omega, by simpa [garbleAux] using h2⟩

/-! ### The real game -/

section Games

variable [Module (ZMod 2) V] (C : Circuit) (m out q : ℕ) (A : AAdv V)

/-- The randomness of both games. In the real game: the zero-labels `L` of the inputs and `Lc` of
the constants, the hash `H` and a junk component `J` (used only by the proof). In the simulated
game: the requested labels `R`, the active constant labels, the hash and the ciphertexts. -/
abbrev Rand (V : Type*) (m n : ℕ) := ((Fin m → V) × (Fin n → V)) × ((Fin n → V → V) × (Fin n → V))

/-- The seed with offset `Δ` and zero-labels `L`, `Lc`. -/
def seed (Δ : V) (L : Fin m → V) (Lc : Fin C.length → V) : Seed V := ⟨Δ, extL L, extL Lc⟩

/-- The real oracle: the hash, and the label of the first requested bit of an input. -/
def realO (Δ : V) (L : Fin m → V) (H : Fin C.length → V → V) : List (Act V) → Act V → V
  | _, .query i y => extH H i y
  | as, .req j b => if h : j < m then lab Δ (L ⟨j, h⟩) ((bitOf as j).getD b) else 0

/-- The real material. -/
def realM (Δ : V) (p : Rand V m C.length) : List (Material V) :=
  (garble (extH p.2.1) (seed C m Δ p.1.1 p.1.2) C).2

/-- The `k` first steps of the real game. -/
def realRun (Δ : V) (p : Rand V m C.length) (k : ℕ) : List (Act V) × List V :=
  run (realO C m Δ p.1.1 p.2.1) A (realM C m Δ p) k

/-- The active input wires of the final input of the real game. -/
def realInp (Δ : V) (p : Rand V m C.length) : ℕ → Wire V :=
  activeInputs (seed C m Δ p.1.1 p.1.2) (xOf m (realRun C m A Δ p q).1)

/-- The adversary outputs the inactive output label of the final input. -/
def RealWin (Δ : V) (p : Rand V m C.length) : Prop :=
  A.guess (realM C m Δ p) (realRun C m A Δ p q).2 =
    activeOut (extH p.2.1) (realInp C m q A Δ p) C out (realM C m Δ p) + Δ

/-- Some query hits an inactive point `(i, S_i + Δ)` of the final input. -/
def RealBad (Δ : V) (p : Rand V m C.length) : Prop :=
  ∃ k < q, ∃ i y, A.act (realM C m Δ p) (realRun C m A Δ p k).2 = .query i y ∧
    ∃ S c, realMux (realInp C m q A Δ p) (realAc (seed C m Δ p.1.1 p.1.2)) C Δ p.2.1 i =
      some (S, c) ∧ y = S + Δ

/-! ### The simulated game -/

/-- The simulated material of a node: an active constant label or a ciphertext. -/
def simNode (Ac T : ℕ → V) (i : ℕ) : Node → Material V
  | .const _ => .const (Ac i)
  | .mux _ _ _ => .mux (T i)
  | _ => .free

/-- The simulated material, from the active constant labels and the ciphertexts. -/
def simM (s : Rand V m C.length) : List (Material V) :=
  C.mapIdx fun i n ↦ simNode (extL s.1.2) (extL s.2.2) i n

/-- The simulated oracle: the hash, and the label `R_j` whatever the bit. -/
def simO (R : Fin m → V) (H : Fin C.length → V → V) : List (Act V) → Act V → V
  | _, .query i y => extH H i y
  | _, .req j _ => extL R j

/-- The `k` first steps of the simulated game. -/
def simRun (s : Rand V m C.length) (k : ℕ) : List (Act V) × List V :=
  run (simO C m s.1.1 s.2.1) A (simM C m s) k

/-- The adversary wins the simulated game for the offset `Δ`. Only this condition uses `Δ`. -/
def SimWin (Δ : V) (s : Rand V m C.length) : Prop :=
  A.guess (simM C m s) (simRun C m A s q).2 =
    activeOut (extH s.2.1) (fun j ↦ (xOf m (simRun C m A s q).1 j, extL s.1.1 j)) C out
      (simM C m s) + Δ

/-! ### From the real to the simulated randomness -/

/-- The bit of a constant node at position `i` (`false` elsewhere). -/
def constBit (i : ℕ) : Bool :=
  match C[i]? with
  | some (.const b) => b
  | _ => false

omit [AddCommGroup V] [Module (ZMod 2) V] in
/-- The ciphertext of the material at position `i`, if it is a multiplexer. -/
def cipher (M : List (Material V)) (i : ℕ) : Option V :=
  match M[i]? with
  | some (.mux T) => some T
  | _ => none

/-- The map from the real to the simulated randomness, for the offset `Δ`. The requested labels
and the active constant labels are the real ones; the hash is the real one, with its values at
the inactive points of the final input replaced by the junk (`GcZk.RO.toSim`); the ciphertexts
are the real ones, and the pads of `GcZk.RO.toSim` fill the positions that are not
multiplexers. -/
noncomputable def toAdSim (Δ : V) (p : Rand V m C.length) : Rand V m C.length :=
  ((fun j ↦ lab Δ (p.1.1 j) (xOf m (realRun C m A Δ p q).1 j),
      fun i ↦ lab Δ (p.1.2 i) (constBit C i)),
    ((toSim (realInp C m q A Δ p) (realAc (seed C m Δ p.1.1 p.1.2)) C Δ p.2).1,
      fun i ↦ (cipher (realM C m Δ p) i).getD
        ((toSim (realInp C m q A Δ p) (realAc (seed C m Δ p.1.1 p.1.2)) C Δ p.2).2 i)))

omit [Module (ZMod 2) V] in
/-- **The simulated material of the image is the real material.** -/
theorem simM_toAdSim (Δ : V) (p : Rand V m C.length) :
    simM C m (toAdSim C m q A Δ p) = realM C m Δ p := by
  apply List.ext_getElem?
  intro k
  rw [simM, List.getElem?_mapIdx]
  by_cases hk : k < C.length
  · obtain ⟨bs', hl, he⟩ := garbleAux_getElem? (extH p.2.1) (seed C m Δ p.1.1 p.1.2) C [] k hk
    have hb : bs'.length = k := by simpa using hl
    have hM : (realM C m Δ p)[k]? =
        some (garbleNode (extH p.2.1) (seed C m Δ p.1.1 p.1.2) bs' C[k]).2 := he
    rw [hM, List.getElem?_eq_getElem hk, Option.map_some]
    congr 1
    cases hc : C[k] with
    | input j => rfl
    | xor a b => rfl
    | const b =>
      simp [simNode, garbleNode, extL, hk, toAdSim, constBit, hc, hb, seed]
    | mux s z o =>
      rw [hc] at hM
      simp [simNode, garbleNode, extL, hk, toAdSim, cipher, hM]
  · have hl : (realM C m Δ p).length = C.length := garbleAux_length _ _ _ _
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    rfl

/-- The real material is the material of `GcZk.RO`, for any input. -/
theorem realM_eq (Δ : V) (p : Rand V m C.length) (x : ℕ → Bool) :
    realM C m Δ p = realMat (activeInputs (seed C m Δ p.1.1 p.1.2) x)
      (realAc (seed C m Δ p.1.1 p.1.2)) C Δ (extH p.2.1) :=
  garble_eq_idealMaterial _ _ x C

omit [Module (ZMod 2) V] in
/-- **Identical until bad.** Without a bad query, the simulated game on the image runs exactly
as the real game. -/
theorem simRun_toAdSim_le (Δ : V) (p : Rand V m C.length) (hb : ¬ RealBad C m q A Δ p)
    {j : ℕ} (hj : j ≤ q) :
    simRun C m A (toAdSim C m q A Δ p) j = realRun C m A Δ p j := by
  unfold simRun realRun
  rw [simM_toAdSim]
  apply run_congr
  intro k hk
  have hk : k < q := by omega
  cases ha : A.act (realM C m Δ p) (run (realO C m Δ p.1.1 p.2.1) A (realM C m Δ p) k).2 with
  | query i y =>
    simp only [simO, realO, extH]
    by_cases hi : i < C.length
    · simp only [hi, ↓reduceDIte, toAdSim, toSim, moveInactive]
      apply ite_eq_right
      rintro ⟨S, c, h1, h2⟩
      exact hb ⟨k, hk, i, y, ha, S, c, h1, h2⟩
    · simp [hi]
  | req j b =>
    simp only [simO, realO, extL]
    by_cases hj : j < m
    · simp only [hj, ↓reduceDIte, toAdSim, realRun]
      rw [xOf_run _ A _ hk hj ha]
    · simp [hj]

omit [Module (ZMod 2) V] in
/-- **Identical until bad.** Without a bad query, the simulated game on the image runs exactly
as the real game. -/
theorem simRun_toAdSim (Δ : V) (p : Rand V m C.length) (hb : ¬ RealBad C m q A Δ p) :
    simRun C m A (toAdSim C m q A Δ p) q = realRun C m A Δ p q :=
  simRun_toAdSim_le C m q A Δ p hb le_rfl

/-- The active output label is the same with the hash of the image. -/
theorem activeOut_toAdSim (Δ : V) (hΔ : Δ ≠ 0) (p : Rand V m C.length) :
    activeOut (extH (toAdSim C m q A Δ p).2.1) (realInp C m q A Δ p) C out (realM C m Δ p) =
      activeOut (extH p.2.1) (realInp C m q A Δ p) C out (realM C m Δ p) := by
  set inp := realInp C m q A Δ p
  set Ac := realAc (seed C m Δ p.1.1 p.1.2)
  obtain ⟨w1, w2, -⟩ := toSim_walk inp Ac C Δ hΔ p.2
  have hM : realM C m Δ p = idealMaterial (extH p.2.1) inp Ac (rpad (extH p.2.1) Δ) C :=
    realM_eq C m Δ p _
  have e1 : realM C m Δ p = idealMaterial (extH (toSim inp Ac C Δ p.2).1) inp Ac
      (extK (toSim inp Ac C Δ p.2).2) C := hM.trans w1.symm
  calc activeOut (extH (toAdSim C m q A Δ p).2.1) inp C out (realM C m Δ p)
      = activeOut (extH (toSim inp Ac C Δ p.2).1) inp C out (idealMaterial
          (extH (toSim inp Ac C Δ p.2).1) inp Ac (extK (toSim inp Ac C Δ p.2).2) C) := by
        rw [← e1]; rfl
    _ = ((idealWiresAux (extH (toSim inp Ac C Δ p.2).1) inp Ac
          (extK (toSim inp Ac C Δ p.2).2) C []).getD out (false, 0)).2 :=
        activeOut_ideal inp Ac C _ _ out
    _ = ((idealWiresAux (extH p.2.1) inp Ac (rpad (extH p.2.1) Δ) C []).getD out
          (false, 0)).2 := by rw [w2]
    _ = activeOut (extH p.2.1) inp C out (realM C m Δ p) := by
        rw [hM]; exact (activeOut_ideal inp Ac C _ _ out).symm

/-- **A real win without a bad query is a simulated win.** -/
theorem simWin_toAdSim (Δ : V) (hΔ : Δ ≠ 0) (p : Rand V m C.length)
    (hb : ¬ RealBad C m q A Δ p) (hw : RealWin C m out q A Δ p) :
    SimWin C m out q A Δ (toAdSim C m q A Δ p) := by
  have hr := simRun_toAdSim C m q A Δ p hb
  have hinp : (fun j ↦ (xOf m (simRun C m A (toAdSim C m q A Δ p) q).1 j,
      extL (toAdSim C m q A Δ p).1.1 j)) = realInp C m q A Δ p := by
    funext j
    rw [hr]
    by_cases hj : j < m
    · simp [realInp, activeInputs, toAdSim, extL, seed, hj]
    · simp [realInp, activeInputs, extL, seed, hj, xOf]
  unfold SimWin
  rw [hinp, simM_toAdSim, hr, activeOut_toAdSim C m out q A Δ hΔ p]
  exact hw

omit [Module (ZMod 2) V] in
/-- The ideal garbler determines the pads at the multiplexers from its material. -/
theorem idealAux_pad_inj (H : ℕ → V → V) (inp : ℕ → Wire V) (Ac : ℕ → Bool → V) :
    ∀ (C : Circuit) {P P' : ℕ → V} {ws : List (Wire V)},
      idealAux H inp Ac (fun i _ _ ↦ P i) C ws = idealAux H inp Ac (fun i _ _ ↦ P' i) C ws →
        ∀ k (hk : k < C.length) s z o, C[k] = .mux s z o → P (ws.length + k) = P' (ws.length + k)
  | [], _, _, _, _, k, hk => by simp at hk
  | n :: ns, P, P', ws, h, k, hk => by
    intro s z o hc
    simp only [idealAux, List.cons.injEq] at h
    obtain ⟨hn, ht⟩ := h
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hc
      subst hc
      simp only [idealNode, muxT, Material.mux.injEq] at hn
      simpa using add_left_cancel hn
    | succ k =>
      rw [hn] at ht
      have := idealAux_pad_inj H inp Ac ns ht k (by simpa using hk) s z o (by simpa using hc)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

omit [Module (ZMod 2) V] in
theorem lab_left_inj {Δ a a' : V} {b : Bool} (h : lab Δ a b = lab Δ a' b) : a = a' := by
  simpa [lab] using h

/-- **Injectivity.** For `Δ ≠ 0`, the map to the simulated randomness is injective on the real
randomness without a bad query. -/
theorem toAdSim_injOn (Δ : V) (hΔ : Δ ≠ 0) :
    Set.InjOn (toAdSim C m q A Δ) {p | ¬ RealBad C m q A Δ p} := by
  rintro ⟨⟨L, Lc⟩, ⟨H, J⟩⟩ hp ⟨⟨L', Lc'⟩, ⟨H', J'⟩⟩ hp' he
  simp only [Set.mem_ofPred_eq] at hp hp'
  have hr := simRun_toAdSim C m q A Δ _ hp
  have hr' := simRun_toAdSim C m q A Δ _ hp'
  rw [he] at hr
  have hx : xOf m (realRun C m A Δ ((L, Lc), (H, J)) q).1 =
      xOf m (realRun C m A Δ ((L', Lc'), (H', J')) q).1 := by rw [← hr, hr']
  have hMM : realM C m Δ ((L, Lc), (H, J)) = realM C m Δ ((L', Lc'), (H', J')) := by
    rw [← simM_toAdSim C m q A Δ, he, simM_toAdSim]
  simp only [toAdSim, Prod.mk.injEq] at he
  obtain ⟨⟨hR, hA⟩, hH, hT⟩ := he
  have hL : L = L' := funext fun j ↦ by
    have := congrFun hR j
    rw [hx] at this
    exact lab_left_inj this
  have hLc : Lc = Lc' := funext fun i ↦ lab_left_inj (congrFun hA i)
  subst hL hLc
  have hI : realInp C m q A Δ ((L, Lc), (H, J)) = realInp C m q A Δ ((L, Lc), (H', J')) := by
    unfold realInp; rw [hx]
  set inp := realInp C m q A Δ ((L, Lc), (H, J))
  set Ac := realAc (seed C m Δ L Lc)
  rw [← hI] at hH hT
  suffices hHJ : (H, J) = (H', J') by rw [hHJ]
  apply toSim_injective inp Ac C Δ hΔ
  refine Prod.ext hH (funext fun i ↦ ?_)
  have hi := i.2
  -- the material of the ideal garbler with the pads of each side
  have w : ∀ p : (Fin C.length → V → V) × (Fin C.length → V),
      realInp C m q A Δ ((L, Lc), p) = inp →
      idealAux (extH (toSim inp Ac C Δ p).1) inp Ac (extK (toSim inp Ac C Δ p).2) C [] =
        realM C m Δ ((L, Lc), p) := by
    intro p hp
    rw [(toSim_walk inp Ac C Δ hΔ p).1]
    have := realM_eq C m Δ ((L, Lc), p) (xOf m (realRun C m A Δ ((L, Lc), p) q).1)
    rw [this]
    simp only [realMat, idealMaterial]
    rw [show activeInputs (seed C m Δ ((L, Lc), p).1.1 ((L, Lc), p).1.2)
      (xOf m (realRun C m A Δ ((L, Lc), p) q).1) = inp from hp]
  have w1 := w (H, J) rfl
  have w2 := w (H', J') hI.symm
  obtain ⟨bs', -, hb⟩ := garbleAux_getElem? (extH H) (seed C m Δ L Lc) C [] i hi
  have hb : (realM C m Δ ((L, Lc), (H, J)))[(i : ℕ)]? =
      some (garbleNode (extH H) (seed C m Δ L Lc) bs' C[(i : ℕ)]).2 := hb
  cases hc : C[(i : ℕ)] with
  | mux s z o =>
    have e : idealAux (extH (toSim inp Ac C Δ (H, J)).1) inp Ac (extK (toSim inp Ac C Δ (H, J)).2)
        C [] = idealAux (extH (toSim inp Ac C Δ (H, J)).1) inp Ac
          (extK (toSim inp Ac C Δ (H', J')).2) C [] := by
      rw [w1, hMM, ← w2, hH]
    have := idealAux_pad_inj (extH (toSim inp Ac C Δ (H, J)).1) inp Ac C
      (P := extL (toSim inp Ac C Δ (H, J)).2) (P' := extL (toSim inp Ac C Δ (H', J')).2)
      (ws := []) e i hi s z o hc
    simpa [extL, hi] using this
  | _ =>
    have h0 : cipher (realM C m Δ ((L, Lc), (H, J))) i = none := by
      simp [cipher, hb, hc, garbleNode]
    have := congrFun hT i
    beta_reduce at this
    rw [h0, ← hMM, h0] at this
    simpa using this

/-! ### Counting -/

section Counting

variable [Fintype V] [DecidableEq V]

open Classical in
/-- **A win without a bad query.** Summed over the offsets `Δ ≠ 0`, the randomness for which the
adversary wins without a bad query is at most all the randomness. With `Δ` uniform on `V \ {0}`
and the zero-labels and the hash uniform, the probability of winning without a bad query is at
most `1 / (|V| - 1)`. (The junk component `J` of `Rand` is not used by the real game; it is
uniform and independent, so it does not change the probability.) -/
theorem win_not_bad_bound :
    ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun p : Rand V m C.length ↦
        RealWin C m out q A Δ p ∧ ¬ RealBad C m q A Δ p).card ≤
      Fintype.card (Rand V m C.length) := by
  calc _ ≤ ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
        (Finset.univ.filter fun s : Rand V m C.length ↦ SimWin C m out q A Δ s).card := by
        refine Finset.sum_le_sum fun Δ hΔ ↦ ?_
        have hΔ : Δ ≠ 0 := by simpa using hΔ
        refine Finset.card_le_card_of_injOn (toAdSim C m q A Δ) (fun p hp ↦ ?_)
          ((toAdSim_injOn C m q A Δ hΔ).mono fun p hp ↦ ?_)
        · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
          exact simWin_toAdSim C m out q A Δ hΔ p hp.2 hp.1
        · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
          exact hp.2
    _ ≤ ∑ Δ : V, (Finset.univ.filter fun s : Rand V m C.length ↦ SimWin C m out q A Δ s).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ∑ s : Rand V m C.length, (Finset.univ.filter fun Δ : V ↦ SimWin C m out q A Δ s).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ _s : Rand V m C.length, 1 := by
        refine Finset.sum_le_sum fun s _ ↦ Finset.card_le_one.2 fun a ha b hb ↦ ?_
        have ha : SimWin C m out q A a s := (Finset.mem_filter.1 ha).2
        have hb : SimWin C m out q A b s := (Finset.mem_filter.1 hb).2
        exact add_left_cancel (ha.symm.trans hb)
    _ = Fintype.card (Rand V m C.length) := by simp

open Classical in
/-- **Reduction to the bad event.** The probability of winning the adaptive game is at most
`1 / (|V| - 1)` plus the probability of a bad query. -/
theorem win_le :
    ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun p : Rand V m C.length ↦ RealWin C m out q A Δ p).card ≤
      Fintype.card (Rand V m C.length) + ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
        (Finset.univ.filter fun p : Rand V m C.length ↦ RealBad C m q A Δ p).card := by
  refine le_trans ?_ (Nat.add_le_add_right (win_not_bad_bound C m out q A) _)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun Δ _ ↦ ?_
  refine le_trans (Finset.card_le_card fun p hp ↦ ?_) (Finset.card_union_le _ _)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hp ⊢
  by_cases hb : RealBad C m q A Δ p
  · exact Or.inr hb
  · exact Or.inl ⟨hp, hb⟩

end Counting

end Games

end GcZk.Adaptive
