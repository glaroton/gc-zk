/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.AdaptiveBound
import GcZk.SquareDH

/-!
# Soundness with the Chou–Orlandi OT: the OT layer as label requests

The verifier sends `A_j = a_j • g` for each input `j < k`. A cheating prover makes `n₀` queries to
the key hash `H_K`, sends `B`, receives the material and the masked label pairs
`e_j = (L_j + H_K(j, a_j • B_j), L_j + Δ + H_K(j, a_j • (B_j - A_j)))`, and makes `n₁` steps, each
with one query to the garbling hash `H`, one to `H_K` and one to the commitment oracle `G` (fixed
here); then it commits. The event `Ext` is that the first query to `G` answered with the commitment
is at the target, the `1`-label of the output.

The adversary `adv γ` of the adaptive authenticity game (`GcZk.Adaptive`) runs the prover with
coins `γ = (a, H_K', e')`. It takes `2` actions per input before the masked pairs and `2` per step
after: a request for the label of a key point, or a query to `H` (a query outside the circuit when
there is nothing to do). The map `Φ` from the real randomness to the coins and the randomness of the
adaptive game moves the values of `H_K` at the key points that are not queried early into the masked
pairs (blueprint, Definition `def:co-map`).

## Main results

* `GcZk.CO.run_eq`: outside `Both`, when the two key points of every input differ (in particular
  outside `Zero`), the prover's run inside `adv` is the real run.
* `GcZk.CO.Φ_injOn`: `Φ` is injective on that set.
* `GcZk.CO.realWin_of_ext`: a real `Ext` is a win of `adv` in the adaptive game.
-/

namespace GcZk.CO

open Adaptive Auth RO

variable {V R D Gp : Type*}

/-- A cheating prover with `k` OT inputs. -/
structure Prover (k : ℕ) (V R D Gp : Type*) where
  n₀ : ℕ
  Q₀ : (Fin k → Gp) → List V → Fin k × Gp
  msgB : (Fin k → Gp) → List V → Fin k → Gp
  n₁ : ℕ
  step : (Fin k → Gp) → List V → List (Material V) → (Fin k → V × V) → List (V × V × D) →
    (ℕ × V) × (Fin k × Gp) × (V × R)
  commit : (Fin k → Gp) → List V → List (Material V) → (Fin k → V × V) → List (V × V × D) → D

section Game

variable {q : ℕ} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup Gp] [Module (ZMod q) Gp]
  (g : Gp) (C : Circuit) (k : ℕ) (G : V × R → D) (P : Prover k V R D Gp)

/-- The sender's messages. -/
def msgA (a : Fin k → ZMod q) : Fin k → Gp := fun j ↦ a j • g

/-- The key hash as an oracle on pairs. -/
def oK (HK : Fin k → Gp → V) : Fin k × Gp → V := fun x ↦ HK x.1 x.2

/-- The answers to the key queries before `B`. -/
def ans₀ (a : Fin k → ZMod q) (HK : Fin k → Gp → V) : List V :=
  Com.ans (oK k HK) (P.Q₀ (msgA g k a)) P.n₀

/-- The receiver messages. -/
def msgB (a : Fin k → ZMod q) (HK : Fin k → Gp → V) : Fin k → Gp :=
  P.msgB (msgA g k a) (ans₀ g k P a HK)

/-- The key point of the bit `c` of input `j`: `a_j • B_j` for `0`, `a_j • (B_j - A_j)` for `1`. -/
def key (a : Fin k → ZMod q) (B : Fin k → Gp) (j : Fin k) (c : Bool) : Gp :=
  if c then a j • (B j - msgA g k a j) else a j • B j

/-- The key point `(j, K^c_j)` is queried before `B`. -/
def Early (a : Fin k → ZMod q) (HK : Fin k → Gp → V) (j : Fin k) (c : Bool) : Prop :=
  Com.Hits (oK k HK) (P.Q₀ (msgA g k a)) P.n₀ (j, key g k a (msgB g k P a HK) j c)

/-- `Early` for an input given by a natural number (false for `j ≥ k`). -/
def EarlyN (a : Fin k → ZMod q) (HK : Fin k → Gp → V) (j : ℕ) (c : Bool) : Prop :=
  ∃ h : j < k, Early g k P a HK ⟨j, h⟩ c

/-- The masked label pairs. -/
def masked (a : Fin k → ZMod q) (HK : Fin k → Gp → V) (Δ : V) (L : Fin k → V) :
    Fin k → V × V := fun j ↦
  (L j + HK j (key g k a (msgB g k P a HK) j false),
    L j + Δ + HK j (key g k a (msgB g k P a HK) j true))

/-- The three oracles of a step. -/
def o₁ (H : Fin C.length → V → V) (HK : Fin k → Gp → V) :
    (ℕ × V) × (Fin k × Gp) × (V × R) → V × V × D :=
  fun x ↦ (extH H x.1.1 x.1.2, HK x.2.1.1 x.2.1.2, G x.2.2)

/-- The label of the first query to `G` answered with the commitment (`0` if none). -/
noncomputable def guessOf (A : Fin k → Gp) (a₀ : List V) (M : List (Material V))
    (e : Fin k → V × V) (c : List (V × V × D)) : V := by
  classical
  exact if h : ∃ s < P.n₁, (c.getD s (0, 0, P.commit A a₀ M e c)).2.2 = P.commit A a₀ M e c ∧
      s < c.length then
    (P.step A a₀ M e (c.take (Nat.find h))).2.2.1
  else 0

/-- The real randomness: secrets, key hash, junk, and the randomness of the adaptive game. -/
abbrev Ω (q : ℕ) (k n : ℕ) (V Gp : Type*) :=
  (Fin k → ZMod q) × (Fin k → Gp → V) × (Fin k → V × V) × Rand V k n

/-- The answers of the `n₁` steps of the real game. -/
def ans₁ (Δ : V) (ω : Ω q k C.length V Gp) : List (V × V × D) :=
  Com.ans (o₁ C k G ω.2.2.2.2.1 ω.2.1)
    (P.step (msgA g k ω.1) (ans₀ g k P ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
      (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1)) P.n₁

/-- The target label: the `1`-label of the output. -/
def target (out : ℕ) (Δ : V) (ρ : Rand V k C.length) : V := (zeroL C k Δ ρ).getD out 0 + Δ

/-- **The event `Ext`.** -/
def Ext (out : ℕ) (Δ : V) (ω : Ω q k C.length V Gp) : Prop :=
  guessOf k P (msgA g k ω.1) (ans₀ g k P ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
      (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1) (ans₁ g C k G P Δ ω) = target C k out Δ ω.2.2.2

/-- Some secret is `0`. -/
def Zero (ω : Ω q k C.length V Gp) : Prop := ∃ j, ω.1 j = 0

/-- The key query of step `s` of the real game. -/
def kq₁ (Δ : V) (ω : Ω q k C.length V Gp) (s : ℕ) : Fin k × Gp :=
  (P.step (msgA g k ω.1) (ans₀ g k P ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
      (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1)
      (Com.ans (o₁ C k G ω.2.2.2.2.1 ω.2.1)
        (P.step (msgA g k ω.1) (ans₀ g k P ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
          (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1)) s)).2.1

/-- The prover queries the key point `(j, K^c_j)` before it commits. -/
def HitsKey (Δ : V) (ω : Ω q k C.length V Gp) (j : Fin k) (c : Bool) : Prop :=
  Early g k P ω.1 ω.2.1 j c ∨
    ∃ s < P.n₁, kq₁ g C k G P Δ ω s = (j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j c)

/-- The prover queries both key points of some input. -/
def Both (Δ : V) (ω : Ω q k C.length V Gp) : Prop :=
  ∃ j, HitsKey g C k G P Δ ω j false ∧ HitsKey g C k G P Δ ω j true

/-! ### The adversary of the adaptive game -/

/-- Pick a component of a pair by a bit. -/
def sel {α : Type*} (c : Bool) (p : α × α) : α := if c then p.2 else p.1

/-- The coins of the adversary: the secrets, a key hash and masked pairs. -/
abbrev Γ (q k : ℕ) (V Gp : Type*) := (Fin k → ZMod q) × (Fin k → Gp → V) × (Fin k → V × V)

open Classical in
/-- The bit of a key point that is not early, if the key query is at one. -/
noncomputable def keyBit (a : Fin k → ZMod q) (HK : Fin k → Gp → V) (x : Fin k × Gp) :
    Option Bool :=
  if x.2 = key g k a (msgB g k P a HK) x.1 false ∧ ¬ Early g k P a HK x.1 false then some false
  else if x.2 = key g k a (msgB g k P a HK) x.1 true ∧ ¬ Early g k P a HK x.1 true then some true
  else none

open Classical in
/-- The masked pairs built by the adversary from the answers `as` of the adaptive game: for an early
key point, the requested label (at position `2 j + c`) plus the key hash. -/
noncomputable def eSim (γ : Γ q k V Gp) (as : List V) : Fin k → V × V := fun j ↦
  (if Early g k P γ.1 γ.2.1 j false then
      as.getD (2 * j) 0 + γ.2.1 j (key g k γ.1 (msgB g k P γ.1 γ.2.1) j false)
    else (γ.2.2 j).1,
   if Early g k P γ.1 γ.2.1 j true then
      as.getD (2 * j + 1) 0 + γ.2.1 j (key g k γ.1 (msgB g k P γ.1 γ.2.1) j true)
    else (γ.2.2 j).2)

/-- The adversary's answer to the key query `x` of step `s`. -/
noncomputable def hkAns (γ : Γ q k V Gp) (as : List V) (s : ℕ) (x : Fin k × Gp) : V :=
  match keyBit g k P γ.1 γ.2.1 x with
  | some c => sel c (eSim g k P γ as x.1) + as.getD (2 * k + 2 * s + 1) 0
  | none => γ.2.1 x.1 x.2

/-- The answers of the steps of the prover replayed by the adversary. -/
noncomputable def cs (γ : Γ q k V Gp) (M : List (Material V)) (as : List V) :
    ℕ → List (V × V × D)
  | 0 => []
  | s + 1 => cs γ M as s ++
      [(as.getD (2 * k + 2 * s) 0,
        hkAns g k P γ as s (P.step (msgA g k γ.1) (ans₀ g k P γ.1 γ.2.1) M
          (eSim g k P γ as) (cs γ M as s)).2.1,
        G (P.step (msgA g k γ.1) (ans₀ g k P γ.1 γ.2.1) M (eSim g k P γ as) (cs γ M as s)).2.2)]

open Classical in
/-- **The adversary `adv γ`.** Two actions per input, then two per step of the prover. -/
noncomputable def adv (γ : Γ q k V Gp) : AAdv V where
  act M as :=
    if as.length < 2 * k then
      if EarlyN g k P γ.1 γ.2.1 (as.length / 2) (as.length % 2 = 1) then
        .req (as.length / 2) (as.length % 2 = 1)
      else .query C.length 0
    else
      if (as.length - 2 * k) % 2 = 0 then
        .query (P.step (msgA g k γ.1) (ans₀ g k P γ.1 γ.2.1) M (eSim g k P γ as)
          (cs g k G P γ M as ((as.length - 2 * k) / 2))).1.1
          (P.step (msgA g k γ.1) (ans₀ g k P γ.1 γ.2.1) M (eSim g k P γ as)
          (cs g k G P γ M as ((as.length - 2 * k) / 2))).1.2
      else
        match keyBit g k P γ.1 γ.2.1 (P.step (msgA g k γ.1) (ans₀ g k P γ.1 γ.2.1) M
          (eSim g k P γ as) (cs g k G P γ M as ((as.length - 2 * k) / 2))).2.1 with
        | some c => .req (P.step (msgA g k γ.1) (ans₀ g k P γ.1 γ.2.1) M (eSim g k P γ as)
            (cs g k G P γ M as ((as.length - 2 * k) / 2))).2.1.1 c
        | none => .query C.length 0
  guess M as :=
    guessOf k P (msgA g k γ.1) (ans₀ g k P γ.1 γ.2.1) M (eSim g k P γ as)
      (cs g k G P γ M as P.n₁)

/-! ### The map to the coins -/

open Classical in
/-- **The map `Φ`.** It moves the values of `H_K` at the key points that are not early into the
masked pairs, and keeps the junk where they are early. -/
noncomputable def Φ (Δ : V) (ω : Ω q k C.length V Gp) : Ω q k C.length V Gp :=
  (ω.1,
    fun j y ↦
      if y = key g k ω.1 (msgB g k P ω.1 ω.2.1) j false ∧ ¬ Early g k P ω.1 ω.2.1 j false then
        (ω.2.2.1 j).1
      else if y = key g k ω.1 (msgB g k P ω.1 ω.2.1) j true ∧ ¬ Early g k P ω.1 ω.2.1 j true then
        (ω.2.2.1 j).2
      else ω.2.1 j y,
    fun j ↦
      (if Early g k P ω.1 ω.2.1 j false then (ω.2.2.1 j).1
        else (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1 j).1,
       if Early g k P ω.1 ω.2.1 j true then (ω.2.2.1 j).2
        else (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1 j).2),
    ω.2.2.2)

omit [Module (ZMod 2) V] in
/-- **Step 1 of the prover.** The key hash of the image answers the early queries as the real
one. -/
theorem ans_Φ (Δ : V) (ω : Ω q k C.length V Gp) {t : ℕ} (ht : t ≤ P.n₀) :
    Com.ans (oK k (Φ g C k P Δ ω).2.1) (P.Q₀ (msgA g k ω.1)) t =
      Com.ans (oK k ω.2.1) (P.Q₀ (msgA g k ω.1)) t := by
  refine Com.ans_congr _ _ _ _ fun t' ht' ↦ ?_
  simp only [Φ, oK]
  set x := P.Q₀ (msgA g k ω.1) (Com.ans (oK k ω.2.1) (P.Q₀ (msgA g k ω.1)) t')
  have hE : ∀ c, x.2 = key g k ω.1 (msgB g k P ω.1 ω.2.1) x.1 c →
      Early g k P ω.1 ω.2.1 x.1 c := fun c hc ↦ ⟨t', by omega, Prod.ext rfl hc⟩
  split_ifs with h1 h2
  · exact absurd (hE false h1.1) h1.2
  · exact absurd (hE true h2.1) h2.2
  · rfl

omit [Module (ZMod 2) V] in
theorem ans₀_Φ (Δ : V) (ω : Ω q k C.length V Gp) :
    ans₀ g k P (Φ g C k P Δ ω).1 (Φ g C k P Δ ω).2.1 = ans₀ g k P ω.1 ω.2.1 :=
  ans_Φ g C k P Δ ω le_rfl

omit [Module (ZMod 2) V] in
theorem msgB_Φ (Δ : V) (ω : Ω q k C.length V Gp) :
    msgB g k P (Φ g C k P Δ ω).1 (Φ g C k P Δ ω).2.1 = msgB g k P ω.1 ω.2.1 := by
  simp only [msgB, ans₀_Φ]; rfl

omit [Module (ZMod 2) V] in
theorem early_Φ (Δ : V) (ω : Ω q k C.length V Gp) (j : Fin k) (c : Bool) :
    Early g k P (Φ g C k P Δ ω).1 (Φ g C k P Δ ω).2.1 j c ↔ Early g k P ω.1 ω.2.1 j c := by
  unfold Early Com.Hits
  rw [msgB_Φ]
  constructor
  · rintro ⟨t, ht, hq⟩
    exact ⟨t, ht, by rw [← ans_Φ g C k P Δ ω ht.le]; exact hq⟩
  · rintro ⟨t, ht, hq⟩
    exact ⟨t, ht, by rw [show (Φ g C k P Δ ω).1 = ω.1 from rfl, ans_Φ g C k P Δ ω ht.le]; exact hq⟩

/-! ### The expected answers -/

/-- The query of step `s` of the real game. -/
def realQ (Δ : V) (ω : Ω q k C.length V Gp) (s : ℕ) : (ℕ × V) × (Fin k × Gp) × (V × R) :=
  P.step (msgA g k ω.1) (ans₀ g k P ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
    (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1)
    (Com.ans (o₁ C k G ω.2.2.2.2.1 ω.2.1)
      (P.step (msgA g k ω.1) (ans₀ g k P ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
        (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1)) s)

open Classical in
/-- The answer of the adaptive game to the action at position `t`, when the adversary runs the
real prover: the requested labels, the answers of `H`, and `0` for the padding queries. -/
noncomputable def Ef (Δ : V) (ω : Ω q k C.length V Gp) (t : ℕ) : V :=
  if t < 2 * k then
    if h : t / 2 < k then
      if Early g k P ω.1 ω.2.1 ⟨t / 2, h⟩ (t % 2 = 1) then
        lab Δ (ω.2.2.2.1.1 ⟨t / 2, h⟩) (t % 2 = 1)
      else 0
    else 0
  else if (t - 2 * k) % 2 = 0 then
    extH ω.2.2.2.2.1 (realQ g C k G P Δ ω ((t - 2 * k) / 2)).1.1
      (realQ g C k G P Δ ω ((t - 2 * k) / 2)).1.2
  else
    match keyBit g k P ω.1 ω.2.1 (realQ g C k G P Δ ω ((t - 2 * k) / 2)).2.1 with
    | some c => lab Δ (ω.2.2.2.1.1 (realQ g C k G P Δ ω ((t - 2 * k) / 2)).2.1.1) c
    | none => 0

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem keyBit_congr {a : Fin k → ZMod q} {HK HK' : Fin k → Gp → V}
    (h1 : msgB g k P a HK = msgB g k P a HK')
    (h2 : ∀ j c, Early g k P a HK j c ↔ Early g k P a HK' j c)
    (x : Fin k × Gp) : keyBit g k P a HK x = keyBit g k P a HK' x := by
  have e : ∀ c, Early g k P a HK x.1 c = Early g k P a HK' x.1 c := fun c ↦ propext (h2 _ _)
  unfold keyBit
  rw [h1, e false, e true]

omit [Module (ZMod 2) V] in
theorem keyBit_Φ (Δ : V) (ω : Ω q k C.length V Gp) (x : Fin k × Gp) :
    keyBit g k P (Φ g C k P Δ ω).1 (Φ g C k P Δ ω).2.1 x = keyBit g k P ω.1 ω.2.1 x :=
  keyBit_congr g k P (msgB_Φ g C k P Δ ω) (early_Φ g C k P Δ ω) x

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem keyBit_some {a : Fin k → ZMod q} {HK : Fin k → Gp → V} {x : Fin k × Gp} {c : Bool}
    (h : keyBit g k P a HK x = some c) :
    x.2 = key g k a (msgB g k P a HK) x.1 c ∧ ¬ Early g k P a HK x.1 c := by
  unfold keyBit at h
  split_ifs at h with h1 h2 <;> cases h
  · exact h1
  · exact h2

omit [Module (ZMod 2) V] in
/-- Off the replaced points, the key hash of the image is the real one. -/
theorem hk_Φ_none (Δ : V) (ω : Ω q k C.length V Gp) {x : Fin k × Gp}
    (h : keyBit g k P ω.1 ω.2.1 x = none) : (Φ g C k P Δ ω).2.1 x.1 x.2 = ω.2.1 x.1 x.2 := by
  unfold keyBit at h
  simp only [Φ]
  split_ifs at h ⊢
  rfl

/-- The coins of the image. -/
noncomputable def γΦ (Δ : V) (ω : Ω q k C.length V Gp) : Γ q k V Gp :=
  ((Φ g C k P Δ ω).1, (Φ g C k P Δ ω).2.1, (Φ g C k P Δ ω).2.2.1)

omit [Module (ZMod 2) V] in
open Classical in
theorem Ef_lt (Δ : V) (ω : Ω q k C.length V Gp) (j : Fin k) (c : Bool) :
    Ef g C k G P Δ ω (2 * j + if c then 1 else 0) =
      if Early g k P ω.1 ω.2.1 j c then lab Δ (ω.2.2.2.1.1 j) c else 0 := by
  have h1 : (2 * (j : ℕ) + if c then 1 else 0) < 2 * k := by have := j.2; split_ifs <;> omega
  have h2 : (2 * (j : ℕ) + if c then 1 else 0) / 2 = j := by split_ifs <;> omega
  have h3 : decide ((2 * (j : ℕ) + if c then 1 else 0) % 2 = 1) = c := by
    cases c <;> simp
  unfold Ef
  generalize (2 * (j : ℕ) + if c then 1 else 0) = t at h1 h2 h3 ⊢
  have ht : t / 2 < k := by rw [h2]; exact j.2
  have hj : (⟨t / 2, ht⟩ : Fin k) = j := Fin.ext h2
  simp only [h1, ↓reduceIte, ht, ↓reduceDIte, hj, h3]

omit [Module (ZMod 2) V] in
theorem eSim_Φ (Δ : V) (ω : Ω q k C.length V Gp)
    (hne : ∀ j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j false ≠
      key g k ω.1 (msgB g k P ω.1 ω.2.1) j true) (as : List V)
    (has : ∀ i < 2 * k, as.getD i 0 = Ef g C k G P Δ ω i) :
    eSim g k P (γΦ g C k P Δ ω) as = masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1 := by
  funext j
  have hj := j.2
  have i0 : (2 * (j : ℕ) + if false then 1 else 0) < 2 * k := by
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]; omega
  have i1 : (2 * (j : ℕ) + if true then 1 else 0) < 2 * k := by
    simp only [↓reduceIte]; omega
  have e0 := has _ i0
  have e1 := has _ i1
  rw [Ef_lt] at e0 e1
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at e0 e1
  simp only [eSim, γΦ]
  have hmB := msgB_Φ g C k P Δ ω
  refine Prod.ext ?_ ?_
  · by_cases hf : Early g k P ω.1 ω.2.1 j false
    · have hf' := (early_Φ g C k P Δ ω j false).2 hf
      simp only [hf', ↓reduceIte, hmB]
      simp only [hf, ↓reduceIte, lab_false] at e0
      rw [e0]
      simp [Φ, masked, hf, hne j]
    · have hf' : ¬ Early g k P (Φ g C k P Δ ω).1 (Φ g C k P Δ ω).2.1 j false :=
        fun h ↦ hf ((early_Φ g C k P Δ ω j false).1 h)
      simp only [hf', ↓reduceIte]
      simp [Φ, hf]
  · by_cases ht : Early g k P ω.1 ω.2.1 j true
    · have ht' := (early_Φ g C k P Δ ω j true).2 ht
      simp only [ht', ↓reduceIte, hmB]
      simp only [ht, ↓reduceIte, lab_true] at e1
      rw [e1]
      simp [Φ, masked, ht, (hne j).symm, add_assoc]
    · have ht' : ¬ Early g k P (Φ g C k P Δ ω).1 (Φ g C k P Δ ω).2.1 j true :=
        fun h ↦ ht ((early_Φ g C k P Δ ω j true).1 h)
      simp only [ht', ↓reduceIte]
      simp [Φ, ht]

omit [Module (ZMod 2) V] in
open Classical in
theorem Ef_even (Δ : V) (ω : Ω q k C.length V Gp) (s : ℕ) :
    Ef g C k G P Δ ω (2 * k + 2 * s) =
      extH ω.2.2.2.2.1 (realQ g C k G P Δ ω s).1.1 (realQ g C k G P Δ ω s).1.2 := by
  unfold Ef
  have h1 : ¬ 2 * k + 2 * s < 2 * k := by omega
  have h2 : (2 * k + 2 * s - 2 * k) % 2 = 0 := by omega
  have h3 : (2 * k + 2 * s - 2 * k) / 2 = s := by omega
  simp only [h1, ↓reduceIte, h2, h3]

omit [Module (ZMod 2) V] in
open Classical in
theorem Ef_odd (Δ : V) (ω : Ω q k C.length V Gp) (s : ℕ) :
    Ef g C k G P Δ ω (2 * k + 2 * s + 1) =
      match keyBit g k P ω.1 ω.2.1 (realQ g C k G P Δ ω s).2.1 with
      | some c => lab Δ (ω.2.2.2.1.1 (realQ g C k G P Δ ω s).2.1.1) c
      | none => 0 := by
  unfold Ef
  have h1 : ¬ 2 * k + 2 * s + 1 < 2 * k := by omega
  have h2 : ¬ (2 * k + 2 * s + 1 - 2 * k) % 2 = 0 := by omega
  have h3 : (2 * k + 2 * s + 1 - 2 * k) / 2 = s := by omega
  simp only [h1, ↓reduceIte, h2, h3]

omit [Module (ZMod 2) V] in
theorem keyBit_Φ' (Δ : V) (ω : Ω q k C.length V Gp) (x : Fin k × Gp) :
    keyBit g k P ω.1 (Φ g C k P Δ ω).2.1 x = keyBit g k P ω.1 ω.2.1 x :=
  keyBit_Φ g C k P Δ ω x

/-- **The steps of the prover.** With the expected answers, the adversary replays the real steps. -/
theorem cs_Φ (Δ : V) (ω : Ω q k C.length V Gp)
    (hne : ∀ j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j false ≠
      key g k ω.1 (msgB g k P ω.1 ω.2.1) j true) (as : List V) (s : ℕ)
    (has : ∀ i < 2 * k + 2 * s, as.getD i 0 = Ef g C k G P Δ ω i) :
    cs g k G P (γΦ g C k P Δ ω) (realM C k Δ ω.2.2.2) as s =
      Com.ans (o₁ C k G ω.2.2.2.2.1 ω.2.1)
        (P.step (msgA g k ω.1) (ans₀ g k P ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
          (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1)) s := by
  have hE := eSim_Φ g C k G P Δ ω hne as fun i hi ↦ has i (by omega)
  have h0 : ans₀ g k P (γΦ g C k P Δ ω).1 (γΦ g C k P Δ ω).2.1 = ans₀ g k P ω.1 ω.2.1 :=
    ans₀_Φ g C k P Δ ω
  have hγ : γΦ g C k P Δ ω = (ω.1, (Φ g C k P Δ ω).2.1, (Φ g C k P Δ ω).2.2.1) := rfl
  rw [hγ] at hE h0 ⊢
  dsimp only at hE h0 ⊢
  induction s with
  | zero => rfl
  | succ s ih =>
    have ih := ih fun i hi ↦ has i (by omega)
    rw [cs, Com.ans, ih, hE, h0]
    congr 2
    set x := (P.step (msgA g k ω.1) (ans₀ g k P ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
      (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1) (Com.ans (o₁ C k G ω.2.2.2.2.1 ω.2.1)
        (P.step (msgA g k ω.1) (ans₀ g k P ω.1 ω.2.1) (realM C k Δ ω.2.2.2)
          (masked g k P ω.1 ω.2.1 Δ ω.2.2.2.1.1)) s)) with hx
    have hQ : realQ g C k G P Δ ω s = x := rfl
    simp only [o₁]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · rw [has _ (by omega), Ef_even, hQ]
    · unfold hkAns
      rw [keyBit_Φ']
      have hodd := has (2 * k + 2 * s + 1) (by omega)
      rw [Ef_odd, hQ] at hodd
      cases hb : keyBit g k P ω.1 ω.2.1 x.2.1 with
      | none => exact hk_Φ_none g C k P Δ ω hb
      | some c =>
        rw [hb] at hodd
        simp only at hodd
        rw [hodd, hE]
        obtain ⟨hk, -⟩ := keyBit_some g k P hb
        have hab : ∀ u w : V, u + w + u = w := fun u w ↦ by
          rw [add_comm u w, add_assoc, add_self_eq_zero', add_zero]
        dsimp only
        rw [hk]
        cases c
        · simp only [sel, masked, lab_false, Bool.false_eq_true, ↓reduceIte]; exact hab _ _
        · simp only [sel, masked, lab_true, ↓reduceIte]; exact hab _ _

/-! ### The run in the adaptive game -/

open Classical in
/-- The action of the adversary at position `t`, in terms of the real run. -/
noncomputable def IA (Δ : V) (ω : Ω q k C.length V Gp) (t : ℕ) : Act V :=
  if t < 2 * k then
    if EarlyN g k P ω.1 ω.2.1 (t / 2) (t % 2 = 1) then .req (t / 2) (t % 2 = 1)
    else .query C.length 0
  else if (t - 2 * k) % 2 = 0 then
    .query (realQ g C k G P Δ ω ((t - 2 * k) / 2)).1.1 (realQ g C k G P Δ ω ((t - 2 * k) / 2)).1.2
  else
    match keyBit g k P ω.1 ω.2.1 (realQ g C k G P Δ ω ((t - 2 * k) / 2)).2.1 with
    | some c => .req (realQ g C k G P Δ ω ((t - 2 * k) / 2)).2.1.1 c
    | none => .query C.length 0

/-- The expected answers to the first `t` actions. -/
noncomputable def El (Δ : V) (ω : Ω q k C.length V Gp) (t : ℕ) : List V :=
  (List.range t).map (Ef g C k G P Δ ω)

omit [Module (ZMod 2) V] in
theorem El_getD (Δ : V) (ω : Ω q k C.length V Gp) {t i : ℕ} (hi : i < t) :
    (El g C k G P Δ ω t).getD i 0 = Ef g C k G P Δ ω i := by
  simp [El, List.getD_eq_getElem?_getD, hi]

/-- **The actions of the adversary** are the intended ones, while the answers are the expected
ones. -/
theorem act_eq (Δ : V) (ω : Ω q k C.length V Gp)
    (hne : ∀ j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j false ≠
      key g k ω.1 (msgB g k P ω.1 ω.2.1) j true) (t : ℕ) :
    (adv g C k G P (γΦ g C k P Δ ω)).act (realM C k Δ ω.2.2.2) (El g C k G P Δ ω t) =
      IA g C k G P Δ ω t := by
  have hlen : (El g C k G P Δ ω t).length = t := by simp [El]
  unfold adv IA
  dsimp only
  rw [hlen]
  by_cases h1 : t < 2 * k
  · have he : EarlyN g k P (γΦ g C k P Δ ω).1 (γΦ g C k P Δ ω).2.1 (t / 2) (t % 2 = 1) ↔
        EarlyN g k P ω.1 ω.2.1 (t / 2) (t % 2 = 1) := by
      unfold EarlyN
      exact exists_congr fun h ↦ early_Φ g C k P Δ ω ⟨t / 2, h⟩ _
    by_cases h3 : EarlyN g k P ω.1 ω.2.1 (t / 2) (t % 2 = 1)
    · simp only [h1, ↓reduceIte, h3, he.2 h3]
    · have h3' : ¬ EarlyN g k P (γΦ g C k P Δ ω).1 (γΦ g C k P Δ ω).2.1 (t / 2) (t % 2 = 1) :=
        fun h ↦ h3 (he.1 h)
      simp only [h1, ↓reduceIte, h3, h3']
  · simp only [h1, ↓reduceIte]
    set s := (t - 2 * k) / 2
    have hs : 2 * k + 2 * s ≤ t := by omega
    have hcs := cs_Φ g C k G P Δ ω hne (El g C k G P Δ ω t) s
      (fun i hi ↦ El_getD g C k G P Δ ω (by omega))
    have hE := eSim_Φ g C k G P Δ ω hne (El g C k G P Δ ω t)
      (fun i hi ↦ El_getD g C k G P Δ ω (by omega))
    have h0 : ans₀ g k P (γΦ g C k P Δ ω).1 (γΦ g C k P Δ ω).2.1 = ans₀ g k P ω.1 ω.2.1 :=
      ans₀_Φ g C k P Δ ω
    have hQ : P.step (msgA g k (γΦ g C k P Δ ω).1) (ans₀ g k P (γΦ g C k P Δ ω).1
        (γΦ g C k P Δ ω).2.1) (realM C k Δ ω.2.2.2) (eSim g k P (γΦ g C k P Δ ω)
          (El g C k G P Δ ω t)) (cs g k G P (γΦ g C k P Δ ω) (realM C k Δ ω.2.2.2)
            (El g C k G P Δ ω t) s) = realQ g C k G P Δ ω s := by
      rw [h0, hE, hcs]; rfl
    rw [hQ]
    by_cases h4 : (t - 2 * k) % 2 = 0
    · simp only [h4, ↓reduceIte]
    · simp only [h4, ↓reduceIte]
      rw [show keyBit g k P (γΦ g C k P Δ ω).1 (γΦ g C k P Δ ω).2.1 = keyBit g k P ω.1 ω.2.1
        from funext (keyBit_Φ g C k P Δ ω)]

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem bitOf_mem {l : List (Act V)} {j : ℕ} {b : Bool} (h : bitOf l j = some b) :
    Act.req j b ∈ l := by
  induction l with
  | nil => simp [bitOf] at h
  | cons a l ih =>
    cases a with
    | query i y => simp only [bitOf] at h; exact List.mem_cons_of_mem _ (ih h)
    | req j' b' =>
      simp only [bitOf] at h
      split_ifs at h with hj
      · cases h; subst hj; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

omit [Module (ZMod 2) V] in
theorem both_of {Δ : V} {ω : Ω q k C.length V Gp} {j : Fin k} {b c : Bool}
    (hb : HitsKey g C k G P Δ ω j b) (hc : HitsKey g C k G P Δ ω j c) (hne : b ≠ c) :
    Both g C k G P Δ ω := by
  cases b <;> cases c
  · exact absurd rfl hne
  · exact ⟨j, hb, hc⟩
  · exact ⟨j, hc, hb⟩
  · exact absurd rfl hne

omit [Module (ZMod 2) V] in
open Classical in
/-- The earlier actions of the adversary: the requests are for early key points before the masked
pairs, and for key points that are not early afterwards. -/
theorem IA_req {Δ : V} {ω : Ω q k C.length V Gp} {t : ℕ} {j : ℕ} {b : Bool}
    (h : IA g C k G P Δ ω t = .req j b) :
    (t < 2 * k ∧ j = t / 2 ∧ b = decide (t % 2 = 1) ∧ EarlyN g k P ω.1 ω.2.1 j b) ∨
    (2 * k ≤ t ∧ (t - 2 * k) % 2 = 1 ∧
      ∃ x : Fin k × Gp, x = (realQ g C k G P Δ ω ((t - 2 * k) / 2)).2.1 ∧ (x.1 : ℕ) = j ∧
        keyBit g k P ω.1 ω.2.1 x = some b) := by
  unfold IA at h
  by_cases h1 : t < 2 * k
  · simp only [h1, ↓reduceIte] at h
    by_cases h2 : EarlyN g k P ω.1 ω.2.1 (t / 2) (t % 2 = 1)
    · simp only [h2, ↓reduceIte, Act.req.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨h1, rfl, rfl, h2⟩
    · simp only [h2, ↓reduceIte, reduceCtorEq] at h
  · simp only [h1, ↓reduceIte] at h
    by_cases h3 : (t - 2 * k) % 2 = 0
    · simp only [h3, ↓reduceIte, reduceCtorEq] at h
    · simp only [h3, ↓reduceIte] at h
      right
      refine ⟨by omega, by omega, _, rfl, ?_⟩
      split at h
      · next c hc => cases h; exact ⟨rfl, hc⟩
      · cases h

omit [Module (ZMod 2) V] in
/-- A request of the adversary at step `s` is at a key point that the prover queries. -/
theorem hitsKey_of_keyBit {Δ : V} {ω : Ω q k C.length V Gp} {s : ℕ} (hs : s < P.n₁) {c : Bool}
    (h : keyBit g k P ω.1 ω.2.1 (realQ g C k G P Δ ω s).2.1 = some c) :
    HitsKey g C k G P Δ ω (realQ g C k G P Δ ω s).2.1.1 c :=
  Or.inr ⟨s, hs, Prod.ext rfl (keyBit_some g k P h).1⟩

omit [Module (ZMod 2) V] in
open Classical in
/-- **The answers of the adaptive game** to the intended actions are the expected ones, when the
prover does not query both key points of an input. -/
theorem answer_eq {Δ : V} {ω : Ω q k C.length V Gp} (hb : ¬ Both g C k G P Δ ω) {t : ℕ}
    (ht : t < 2 * k + 2 * P.n₁) :
    realO C k Δ ω.2.2.2.1.1 ω.2.2.2.2.1 ((List.range t).map (IA g C k G P Δ ω))
      (IA g C k G P Δ ω t) = Ef g C k G P Δ ω t := by
  -- an earlier request of the same input
  have hprev : ∀ {j : ℕ} {b : Bool},
      bitOf ((List.range t).map (IA g C k G P Δ ω)) j = some b →
        ∃ t' < t, IA g C k G P Δ ω t' = .req j b := by
    intro j b h
    obtain ⟨t', ht', he⟩ := List.mem_map.1 (bitOf_mem h)
    exact ⟨t', List.mem_range.1 ht', he⟩
  by_cases h1 : t < 2 * k
  · have hIA : IA g C k G P Δ ω t = if EarlyN g k P ω.1 ω.2.1 (t / 2) (t % 2 = 1) then
        .req (t / 2) (t % 2 = 1) else .query C.length 0 := by
      unfold IA; simp only [h1, ↓reduceIte]
    have hj : t / 2 < k := by omega
    have htj : t = 2 * ((⟨t / 2, hj⟩ : Fin k) : ℕ) + if decide (t % 2 = 1) then 1 else 0 := by
      simp only; split_ifs with h <;> simp at h <;> omega
    by_cases h2 : EarlyN g k P ω.1 ω.2.1 (t / 2) (t % 2 = 1)
    · rw [hIA]
      simp only [h2, ↓reduceIte]
      obtain ⟨hj', he⟩ := h2
      have hbit : (bitOf ((List.range t).map (IA g C k G P Δ ω)) (t / 2)).getD
          (t % 2 = 1) = decide (t % 2 = 1) := by
        cases hbo : bitOf ((List.range t).map (IA g C k G P Δ ω)) (t / 2) with
        | none => rfl
        | some b =>
          obtain ⟨t', ht', hIA'⟩ := hprev hbo
          rcases IA_req g C k G P hIA' with ⟨-, hj2, rfl, ⟨hj3, he'⟩⟩ | ⟨h1', -⟩
          · simp only [Option.getD_some]
            by_contra hbc
            exact hb (both_of g C k G P (Or.inl he') (Or.inl he) (by
              intro h; apply hbc; convert h using 2))
          · omega
      simp only [realO, hj, ↓reduceDIte, hbit]
      conv_rhs => rw [htj, Ef_lt]
      simp only [show Early g k P ω.1 ω.2.1 ⟨t / 2, hj⟩ (t % 2 = 1) from he, ↓reduceIte]
    · rw [hIA]
      simp only [h2, ↓reduceIte]
      simp only [realO, extH, lt_irrefl, ↓reduceDIte]
      conv_rhs => rw [htj, Ef_lt]
      simp only [show ¬ Early g k P ω.1 ω.2.1 ⟨t / 2, hj⟩ (t % 2 = 1) from fun h ↦ h2 ⟨hj, h⟩,
        ↓reduceIte]
  · set s := (t - 2 * k) / 2 with hsdef
    have hs : s < P.n₁ := by omega
    by_cases h3 : (t - 2 * k) % 2 = 0
    · have htt : t = 2 * k + 2 * s := by omega
      have hIA : IA g C k G P Δ ω t = .query (realQ g C k G P Δ ω s).1.1
          (realQ g C k G P Δ ω s).1.2 := by
        unfold IA; simp only [h1, ↓reduceIte, h3, hsdef]
      rw [hIA]
      conv_rhs => rw [htt, Ef_even]
      rfl
    · have htt : t = 2 * k + 2 * s + 1 := by omega
      have hIA : IA g C k G P Δ ω t =
          match keyBit g k P ω.1 ω.2.1 (realQ g C k G P Δ ω s).2.1 with
          | some c => .req (realQ g C k G P Δ ω s).2.1.1 c
          | none => .query C.length 0 := by
        unfold IA; simp only [h1, ↓reduceIte, h3, hsdef]
      rw [hIA]
      conv_rhs => rw [htt, Ef_odd]
      cases hkb : keyBit g k P ω.1 ω.2.1 (realQ g C k G P Δ ω s).2.1 with
      | none => simp [realO, extH]
      | some c =>
        set x := (realQ g C k G P Δ ω s).2.1 with hx
        have hbit : (bitOf ((List.range t).map (IA g C k G P Δ ω)) x.1).getD c = c := by
          cases hbo : bitOf ((List.range t).map (IA g C k G P Δ ω)) x.1 with
          | none => rfl
          | some b =>
            obtain ⟨t', ht', hIA'⟩ := hprev hbo
            simp only [Option.getD_some]
            by_contra hbc
            have hc := hitsKey_of_keyBit g C k G P hs hkb
            rcases IA_req g C k G P hIA' with ⟨-, hj2, -, ⟨hj3, he'⟩⟩ | ⟨-, -, x', hx', hj', hkb'⟩
            · have hfin : (⟨(x.1 : ℕ), hj3⟩ : Fin k) = x.1 := Fin.ext rfl
              rw [hfin] at he'
              exact hb (both_of g C k G P (Or.inl he') hc hbc)
            · have hfin : x'.1 = x.1 := Fin.ext hj'
              have hs' : (t' - 2 * k) / 2 < P.n₁ := by omega
              have hb' := hitsKey_of_keyBit g C k G P hs' (by rw [← hx']; exact hkb')
              rw [← hx', hfin] at hb'
              exact hb (both_of g C k G P hb' hc hbc)
        simp only [realO, x.1.2, ↓reduceDIte, Fin.eta, hbit]

/-- **Same run.** Outside `Both`, with distinct key points, the run of the adversary in the adaptive
game with the randomness of the image takes the intended actions and gets the expected answers. -/
theorem run_eq {Δ : V} {ω : Ω q k C.length V Gp}
    (hne : ∀ j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j false ≠
      key g k ω.1 (msgB g k P ω.1 ω.2.1) j true) (hb : ¬ Both g C k G P Δ ω) {t : ℕ}
    (ht : t ≤ 2 * k + 2 * P.n₁) :
    run (realO C k Δ ω.2.2.2.1.1 ω.2.2.2.2.1) (adv g C k G P (γΦ g C k P Δ ω))
        (realM C k Δ ω.2.2.2) t =
      ((List.range t).map (IA g C k G P Δ ω), El g C k G P Δ ω t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run, ih (by omega), act_eq g C k G P Δ ω hne t, answer_eq g C k G P hb (by omega)]
    simp [El, List.range_succ]

/-- **Wins.** For an unsatisfiable circuit, outside `Both` and with distinct key points, a real
`Ext` is a win of the adversary with the coins of the image in the adaptive game with `2k + 2n₁`
actions. -/
theorem realWin_of_ext (out : ℕ) (hC : ∀ x, (plain x C).getD out false = false) {Δ : V}
    {ω : Ω q k C.length V Gp}
    (hne : ∀ j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j false ≠
      key g k ω.1 (msgB g k P ω.1 ω.2.1) j true) (hb : ¬ Both g C k G P Δ ω)
    (he : Ext g C k G P out Δ ω) :
    Adaptive.RealWin C k out (2 * k + 2 * P.n₁) (adv g C k G P (γΦ g C k P Δ ω)) Δ ω.2.2.2 := by
  unfold Adaptive.RealWin realRun
  rw [run_eq g C k G P hne hb le_rfl]
  have hE := eSim_Φ g C k G P Δ ω hne (El g C k G P Δ ω (2 * k + 2 * P.n₁))
    (fun i hi ↦ El_getD g C k G P Δ ω (by omega))
  have hcs := cs_Φ g C k G P Δ ω hne (El g C k G P Δ ω (2 * k + 2 * P.n₁)) P.n₁
    (fun i hi ↦ El_getD g C k G P Δ ω hi)
  have h0 : ans₀ g k P (γΦ g C k P Δ ω).1 (γΦ g C k P Δ ω).2.1 = ans₀ g k P ω.1 ω.2.1 :=
    ans₀_Φ g C k P Δ ω
  have hg : (adv g C k G P (γΦ g C k P Δ ω)).guess (realM C k Δ ω.2.2.2)
      (El g C k G P Δ ω (2 * k + 2 * P.n₁)) = target C k out Δ ω.2.2.2 := by
    simp only [adv]
    rw [h0, hE, hcs]
    exact he
  rw [hg, target]
  congr 1
  -- the active output label is the zero-label, since the output value is `0`
  have e := eval_garble (extH ω.2.2.2.2.1) (seed C k Δ ω.2.2.2.1.1 ω.2.2.2.1.2)
    (xOf k ((List.range (2 * k + 2 * P.n₁)).map (IA g C k G P Δ ω))) C out
  rw [activeOut, realInp, realRun, run_eq g C k G P hne hb le_rfl]
  rw [show realM C k Δ ω.2.2.2 = (garble (extH ω.2.2.2.2.1) (seed C k Δ ω.2.2.2.1.1
    ω.2.2.2.1.2) C).2 from rfl, e, hC, lab_false]
  rfl

/-! ### Injectivity -/

omit [Module (ZMod 2) V] in
/-- **Injectivity.** With distinct key points, `Φ` is injective. -/
theorem Φ_injOn (Δ : V) :
    Set.InjOn (Φ g C k P Δ) {ω : Ω q k C.length V Gp | ∀ j,
      key g k ω.1 (msgB g k P ω.1 ω.2.1) j false ≠ key g k ω.1 (msgB g k P ω.1 ω.2.1) j true} := by
  rintro ⟨a, HK1, J1, ρ⟩ h1 ⟨a2, HK2, J2, ρ2⟩ h2 he
  simp only [Set.mem_ofPred_eq] at h1 h2
  have ha : a = a2 := congrArg Prod.fst he
  have hρ : ρ = ρ2 := congrArg (fun x : Ω q k C.length V Gp ↦ x.2.2.2) he
  subst ha hρ
  have hK : (Φ g C k P Δ (a, HK1, J1, ρ)).2.1 = (Φ g C k P Δ (a, HK2, J2, ρ)).2.1 :=
    congrArg (fun x : Ω q k C.length V Gp ↦ x.2.1) he
  have hJ : (Φ g C k P Δ (a, HK1, J1, ρ)).2.2.1 = (Φ g C k P Δ (a, HK2, J2, ρ)).2.2.1 :=
    congrArg (fun x : Ω q k C.length V Gp ↦ x.2.2.1) he
  -- the early part of the run
  have hans : ans₀ g k P a HK1 = ans₀ g k P a HK2 := by
    rw [← ans₀_Φ g C k P Δ (a, HK1, J1, ρ), ← ans₀_Φ g C k P Δ (a, HK2, J2, ρ)]
    exact congrArg (ans₀ g k P a) hK
  have hB : msgB g k P a HK1 = msgB g k P a HK2 := by simp only [msgB, hans]
  have hE : ∀ j c, Early g k P a HK1 j c ↔ Early g k P a HK2 j c := by
    intro j c
    rw [← early_Φ g C k P Δ (a, HK1, J1, ρ), ← early_Φ g C k P Δ (a, HK2, J2, ρ)]
    exact Iff.of_eq (congrArg (fun H ↦ Early g k P a H j c) hK)
  have hne := h1
  -- the key hash
  have hH : HK1 = HK2 := by
    funext j y
    have kK := congrFun (congrFun hK j) y
    have kJ := congrFun hJ j
    simp only [Φ] at kK kJ
    rw [hB] at kK
    set K0 := key g k a (msgB g k P a HK2) j false
    set K1 := key g k a (msgB g k P a HK2) j true
    by_cases c0 : y = K0 ∧ ¬ Early g k P a HK1 j false
    · have c0' : ¬ Early g k P a HK2 j false := fun h ↦ c0.2 ((hE j false).2 h)
      have := congrArg Prod.fst kJ
      simp only [c0.2, c0', ↓reduceIte, masked, hB] at this
      rw [c0.1]; exact add_left_cancel this
    · by_cases c1 : y = K1 ∧ ¬ Early g k P a HK1 j true
      · have c1' : ¬ Early g k P a HK2 j true := fun h ↦ c1.2 ((hE j true).2 h)
        have := congrArg Prod.snd kJ
        simp only [c1.2, c1', ↓reduceIte, masked, hB] at this
        rw [c1.1]; exact add_left_cancel this
      · have c0' : ¬ (y = K0 ∧ ¬ Early g k P a HK2 j false) :=
          fun h ↦ c0 ⟨h.1, fun h' ↦ h.2 ((hE j false).1 h')⟩
        have c1' : ¬ (y = K1 ∧ ¬ Early g k P a HK2 j true) :=
          fun h ↦ c1 ⟨h.1, fun h' ↦ h.2 ((hE j true).1 h')⟩
        simp only [c0, c1, c0', c1', ↓reduceIte] at kK
        exact kK
  subst hH
  -- the junk
  have hJJ : J1 = J2 := by
    funext j
    have kK0 := congrFun (congrFun hK j) (key g k a (msgB g k P a HK1) j false)
    have kK1 := congrFun (congrFun hK j) (key g k a (msgB g k P a HK1) j true)
    have kJ := congrFun hJ j
    simp only [Φ] at kK0 kK1 kJ
    refine Prod.ext ?_ ?_
    · by_cases e0 : Early g k P a HK1 j false
      · simpa [e0] using congrArg Prod.fst kJ
      · simpa [e0] using kK0
    · by_cases e1 : Early g k P a HK1 j true
      · simpa [e1] using congrArg Prod.snd kJ
      · simpa [e1, (hne j).symm] using kK1
  subst hJJ
  rfl

/-- **Distinct key points.** If `a_j ≠ 0` the two key points of `j` differ: their difference is
`(a_j * a_j) • g`. -/
theorem key_ne [Fact q.Prime] (hg : Function.Bijective fun b : ZMod q ↦ b • g)
    {a : Fin k → ZMod q} (B : Fin k → Gp) {j : Fin k} (ha : a j ≠ 0) :
    key g k a B j false ≠ key g k a B j true := by
  intro h
  have hd : key g k a B j false - key g k a B j true = (a j * a j) • g := by
    simp only [key, msgA, Bool.false_eq_true, ↓reduceIte]
    exact SqDH.keys_sub g (a j) (B j)
  rw [h, sub_self] at hd
  have : a j * a j = 0 := hg.1 (by simpa using hd.symm)
  exact ha (mul_self_eq_zero.1 this)

/-! ### Counting -/

section Count

variable [Fintype V] [DecidableEq V] [Fintype Gp] [DecidableEq Gp] [NeZero q]

open Classical in
/-- **The OT layer, counting form.** For an unsatisfiable circuit and fixed `G`, summed over
`Δ ≠ 0`, the real randomness with `Ext`, outside `Both` and with distinct key points, satisfies
`|V| · Σ_Δ # ≤ |Γ| (|V| + Q (|V| + (|V| - 1))) |Rand|` with `Q = 2k + 2n₁`: with `Δ` uniform on
`V \ {0}` and the rest uniform, its probability is at most `(Q + 1) / (|V| - 1) + Q / |V|`. -/
theorem card_ext_le (out : ℕ) (hC : ∀ x, (plain x C).getD out false = false) :
    Fintype.card V * ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Ext g C k G P out Δ ω ∧
        ¬ Both g C k G P Δ ω ∧ ∀ j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j false ≠
          key g k ω.1 (msgB g k P ω.1 ω.2.1) j true).card ≤
      Fintype.card (Γ q k V Gp) * (Fintype.card V * Fintype.card (Rand V k C.length) +
        (2 * k + 2 * P.n₁) * ((Fintype.card V + (Fintype.card V - 1)) *
          Fintype.card (Rand V k C.length))) := by
  set Q := 2 * k + 2 * P.n₁
  set W := fun (γ : Γ q k V Gp) (Δ : V) ↦
    (Finset.univ.filter fun ρ : Rand V k C.length ↦
      Adaptive.RealWin C k out Q (adv g C k G P γ) Δ ρ).card
  -- each offset: inject into the wins of the adversaries
  have step : ∀ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
      (Finset.univ.filter fun ω : Ω q k C.length V Gp ↦ Ext g C k G P out Δ ω ∧
        ¬ Both g C k G P Δ ω ∧ ∀ j, key g k ω.1 (msgB g k P ω.1 ω.2.1) j false ≠
          key g k ω.1 (msgB g k P ω.1 ω.2.1) j true).card ≤ ∑ γ : Γ q k V Gp, W γ Δ := by
    intro Δ _
    have hsum : ∑ γ : Γ q k V Gp, W γ Δ = (Finset.univ.filter fun p : Γ q k V Gp ×
        Rand V k C.length ↦ Adaptive.RealWin C k out Q (adv g C k G P p.1) Δ p.2).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type (f := fun p : Γ q k V Gp × Rand V k C.length ↦
        if Adaptive.RealWin C k out Q (adv g C k G P p.1) Δ p.2 then 1 else 0)]
      refine Finset.sum_congr rfl fun γ _ ↦ ?_
      simp only [W, Finset.card_filter]
    rw [hsum]
    refine Finset.card_le_card_of_injOn (fun ω ↦ (γΦ g C k P Δ ω, ω.2.2.2)) (fun ω hω ↦ ?_)
      (fun ω1 h1 ω2 h2 he ↦ ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hω ⊢
      exact realWin_of_ext g C k G P out hC hω.2.2 hω.2.1 hω.1
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h1 h2
      refine Φ_injOn g C k P Δ h1.2.2 h2.2.2 ?_
      have e1 := congrArg Prod.fst he
      have e2 := congrArg Prod.snd he
      simp only [γΦ, Prod.mk.injEq] at e1 e2
      exact Prod.ext e1.1 (Prod.ext e1.2.1 (Prod.ext e1.2.2 e2))
  calc Fintype.card V * _ ≤ Fintype.card V * ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)),
        ∑ γ : Γ q k V Gp, W γ Δ := Nat.mul_le_mul_left _ (Finset.sum_le_sum step)
    _ = ∑ γ : Γ q k V Gp, Fintype.card V * ∑ Δ ∈ Finset.univ.filter (· ≠ (0 : V)), W γ Δ := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _γ : Γ q k V Gp, (Fintype.card V * Fintype.card (Rand V k C.length) +
          Q * ((Fintype.card V + (Fintype.card V - 1)) * Fintype.card (Rand V k C.length))) :=
        Finset.sum_le_sum fun γ _ ↦ card_win_le C k Q (adv g C k G P γ) out
    _ = _ := by simp

end Count

end Game

end GcZk.CO
