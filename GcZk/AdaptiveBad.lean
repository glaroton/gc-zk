/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.Adaptive
import GcZk.LinearPart

/-!
# Adaptive authenticity: bad steps

A query that is bad for the final input (`GcZk.Adaptive.RealBad`) is not decided at the time of
the query. A *bad step* is: a query `(i, y)` at a multiplexer whose selector `s` is known at that
step (its linear part is `0`) and `y` is its inactive point for the input requested so far, or
whose selector is unknown and `y` is either of its two points `Z_s`, `Z_s + Δ`.

## Main results

* `GcZk.Adaptive.realMux_some`: the active selector label recorded by the ideal garbler is
  `lab Δ Z_s v_s`, with the zero-label of the real garbling and the value of the selector.
* `GcZk.Adaptive.exists_badStep`: a query bad for the final input gives a bad step.
* `GcZk.Adaptive.not_realBad_of_first`: if no step before `k` is bad, the game truncated to `k`
  steps has no query bad for its final input.
-/

namespace GcZk.Adaptive

open Auth RO

variable {V : Type*} [AddCommGroup V]

/-! ### The trace of the ideal garbler, position by position -/

omit [AddCommGroup V] in
theorem idealWiresAux_prefix [AddCommGroup V] (H : ℕ → V → V) (inp : ℕ → Wire V)
    (Ac : ℕ → Bool → V) (pad : ℕ → V → Bool → V) :
    ∀ (ns : Circuit) (ws : List (Wire V)), ∃ rest, idealWiresAux H inp Ac pad ns ws = ws ++ rest
  | [], ws => ⟨[], by simp [idealWiresAux]⟩
  | n :: ns, ws => by
    obtain ⟨rest, h⟩ := idealWiresAux_prefix H inp Ac pad ns
      (ws ++ [evalNode H inp ws n (idealNode H Ac pad ws n)])
    exact ⟨evalNode H inp ws n (idealNode H Ac pad ws n) :: rest, by
      simp only [idealWiresAux]; rw [h]; simp⟩

/-- `muxAt` at a position `i` reads the node at `i` and the trace before `i`. -/
theorem muxAt_some (H : ℕ → V → V) (inp : ℕ → Wire V) (Ac : ℕ → Bool → V)
    (pad : ℕ → V → Bool → V) :
    ∀ (ns : Circuit) (ws : List (Wire V)) (i : ℕ) (r : V × Bool),
      muxAt H inp Ac pad ns ws i = some r →
        ∃ k, ∃ hk : k < ns.length, i = ws.length + k ∧
          nodeMux ((idealWiresAux H inp Ac pad ns ws).take i) ns[k] = some r
  | [], _, _, _, h => by simp [muxAt] at h
  | n :: ns, ws, i, r, h => by
    simp only [muxAt] at h
    split_ifs at h with hi
    · refine ⟨0, by simp, by simp [hi], ?_⟩
      obtain ⟨rest, hr⟩ := idealWiresAux_prefix H inp Ac pad (n :: ns) ws
      rw [hr, hi, List.take_left']
      · simpa using h
      · rfl
    · obtain ⟨k, hk, h1, h2⟩ := muxAt_some H inp Ac pad ns _ i r h
      refine ⟨k + 1, by simpa using hk, by simp at h1; omega, ?_⟩
      simpa [idealWiresAux] using h2

section Bridge

variable [Module (ZMod 2) V] (C : Circuit) (m : ℕ)

/-- The zero-labels of the real garbling. -/
def zeroL (Δ : V) (p : Rand V m C.length) : List V :=
  (garble (extH p.2.1) (seed C m Δ p.1.1 p.1.2) C).1

/-- The zero-label of position `s` as read at position `i` (`0` if `s` is not earlier). -/
def zr (Δ : V) (p : Rand V m C.length) (i s : ℕ) : V :=
  if s < i then (zeroL C m Δ p).getD s 0 else 0

/-- **The active selector label.** For any input `x`, if the ideal garbler records the active
selector label `S` at position `i`, then the node at `i` is a multiplexer and `S` is the label
of the value of its selector, `lab Δ Z_s v_s`, as read at `i`. -/
theorem realMux_some (Δ : V) (p : Rand V m C.length) (x : ℕ → Bool) {i : ℕ} {S : V} {c : Bool}
    (h : realMux (activeInputs (seed C m Δ p.1.1 p.1.2) x) (realAc (seed C m Δ p.1.1 p.1.2)) C Δ
      p.2.1 i = some (S, c)) :
    ∃ s z o, C[i]? = some (.mux s z o) ∧ S = lab Δ (zr C m Δ p i s) (Lin.rv x C i s) := by
  obtain ⟨k, hk, rfl, h2⟩ := muxAt_some _ _ _ _ C [] i (S, c) h
  simp only [List.length_nil, zero_add] at h2 ⊢
  rw [List.getElem?_eq_getElem hk]
  cases hn : C[k] with
  | mux s z o =>
    refine ⟨s, z, o, rfl, ?_⟩
    rw [hn] at h2
    simp only [nodeMux, Option.some.injEq, Prod.mk.injEq] at h2
    rw [← h2.1]
    -- the trace is the evaluation of the real material
    have hW : idealWiresAux (extH p.2.1) (activeInputs (seed C m Δ p.1.1 p.1.2) x)
        (realAc (seed C m Δ p.1.1 p.1.2)) (rpad (extH p.2.1) Δ) C [] =
        eval (extH p.2.1) (activeInputs (seed C m Δ p.1.1 p.1.2) x) C (realM C m Δ p) := by
      rw [realM_eq C m Δ p x, eval, realMat, idealMaterial, evalAux_ideal]
    rw [hW]
    by_cases hs : s < k
    · have e := eval_garble (extH p.2.1) (seed C m Δ p.1.1 p.1.2) x C s
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hs, ↓reduceIte] at e ⊢
      rw [show realM C m Δ p = (garble (extH p.2.1) (seed C m Δ p.1.1 p.1.2) C).2 from rfl, e]
      simp only [zr, hs, ↓reduceIte, Lin.rv, zeroL, List.getD_eq_getElem?_getD]
      have hp := Lin.plain_getD x C s
      simp only [List.getD_eq_getElem?_getD] at hp
      rw [hp]
      rfl
    · simp [hs, zr, Lin.rv, lab]
  | _ => rw [hn] at h2; simp [nodeMux] at h2

end Bridge

/-! ### Requested inputs -/

/-- The inputs requested by the actions `as`. The inputs `j ≥ m` count as requested: their value
is always `0` and their label `0`. -/
def reqAt (m : ℕ) (as : List (Act V)) (j : ℕ) : Bool := decide (m ≤ j) || (bitOf as j).isSome

omit [AddCommGroup V] in
/-- The final input agrees, on the inputs requested before step `k`, with the input requested
before step `k`. -/
theorem xOf_agree (O : List (Act V) → Act V → V) (A : AAdv V) (M : List (Material V)) (m : ℕ)
    {k q : ℕ} (hkq : k ≤ q) {j : ℕ} (hj : reqAt m (run O A M k).1 j = true) :
    xOf m (run O A M q).1 j = xOf m (run O A M k).1 j := by
  obtain ⟨rest, hr⟩ := run_prefix O A M k (q - k)
  rw [show k + (q - k) = q by omega] at hr
  rw [hr]
  unfold xOf
  by_cases hm : j < m
  · simp only [hm, ↓reduceIte, bitOf_append]
    have : (bitOf (run O A M k).1 j).isSome = true := by
      simpa [reqAt, show ¬ m ≤ j by omega] using hj
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 this
    simp [hb]
  · simp [hm]

omit [AddCommGroup V] in
/-- Requested inputs stay requested. -/
theorem reqAt_mono (O : List (Act V) → Act V → V) (A : AAdv V) (M : List (Material V)) (m : ℕ)
    {j k : ℕ} (hjk : j ≤ k) {t : ℕ} (ht : reqAt m (run O A M j).1 t = true) :
    reqAt m (run O A M k).1 t = true := by
  obtain ⟨rest, hr⟩ := run_prefix O A M j (k - j)
  rw [show j + (k - j) = k by omega] at hr
  rw [hr]
  simp only [reqAt, Bool.or_eq_true, decide_eq_true_eq, bitOf_append] at ht ⊢
  rcases ht with h | h
  · exact Or.inl h
  · right; obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h; simp [hb]

/-! ### Bad steps -/

section Bad

variable [Module (ZMod 2) V] (C : Circuit) (m : ℕ) (A : AAdv V)

/-- The input requested before step `k`. -/
def xAt (Δ : V) (p : Rand V m C.length) (k : ℕ) : ℕ → Bool := xOf m (realRun C m A Δ p k).1

/-- The inputs requested before step `k`. -/
def rqAt (Δ : V) (p : Rand V m C.length) (k : ℕ) : ℕ → Bool := reqAt m (realRun C m A Δ p k).1

/-- **Bad step.** The action at step `k` is a query `(i, y)` at a multiplexer with selector `s`,
and either `s` is known at step `k` and `y` is its inactive point for the input requested so far,
or `s` is unknown and `y` is one of its two points. -/
def BadStep (Δ : V) (p : Rand V m C.length) (k : ℕ) : Prop :=
  ∃ i y s z o, A.act (realM C m Δ p) (realRun C m A Δ p k).2 = .query i y ∧
    C[i]? = some (.mux s z o) ∧
    (Lin.rl (xAt C m A Δ p k) (rqAt C m A Δ p k) C i s = 0 →
      y = lab Δ (zr C m Δ p i s) (!Lin.rv (xAt C m A Δ p k) C i s)) ∧
    (Lin.rl (xAt C m A Δ p k) (rqAt C m A Δ p k) C i s ≠ 0 →
      y = zr C m Δ p i s ∨ y = zr C m Δ p i s + Δ)

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem lab_add_delta [AddCommGroup V] [Module (ZMod 2) V] (Δ L : V) (b : Bool) :
    lab Δ L b + Δ = lab Δ L (!b) := by
  cases b <;> simp [lab, add_assoc, add_self_eq_zero']

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem lab_add_delta_mem [AddCommGroup V] [Module (ZMod 2) V] (Δ L : V) (b : Bool) :
    lab Δ L b + Δ = L ∨ lab Δ L b + Δ = L + Δ := by
  cases b <;> simp [lab, add_assoc, add_self_eq_zero']

/-- **A query bad for the final input gives a bad step.** -/
theorem exists_badStep (Δ : V) (p : Rand V m C.length) {q : ℕ} (hb : RealBad C m q A Δ p) :
    ∃ k < q, BadStep C m A Δ p k := by
  obtain ⟨k, hk, i, y, ha, S, c, hm, hy⟩ := hb
  obtain ⟨s, z, o, hC, hS⟩ := realMux_some C m Δ p (xOf m (realRun C m A Δ p q).1) hm
  refine ⟨k, hk, i, y, s, z, o, ha, hC, fun hkn ↦ ?_, fun _ ↦ ?_⟩
  · have e := Lin.rv_eq_of_known (xAt C m A Δ p k) (xOf m (realRun C m A Δ p q).1)
      (rqAt C m A Δ p k) C (fun j hj ↦ xOf_agree _ A _ m hk.le hj) hkn
    rw [hy, hS, e, lab_add_delta]
  · rw [hy, hS]; exact lab_add_delta_mem _ _ _

/-- **The first bad step.** If no step before `k` is bad, the game truncated to `k` steps has no
query bad for its final input. -/
theorem not_realBad_of_first (Δ : V) (p : Rand V m C.length) {k : ℕ}
    (hf : ∀ j < k, ¬ BadStep C m A Δ p j) : ¬ RealBad C m k A Δ p := by
  rintro ⟨j, hj, i, y, ha, S, c, hm, hy⟩
  obtain ⟨s, z, o, hC, hS⟩ := realMux_some C m Δ p (xOf m (realRun C m A Δ p k).1) hm
  refine hf j hj ⟨i, y, s, z, o, ha, hC, fun hkn ↦ ?_, fun _ ↦ ?_⟩
  · have e := Lin.rv_eq_of_known (xAt C m A Δ p j) (xOf m (realRun C m A Δ p k).1)
      (rqAt C m A Δ p j) C (fun t ht ↦ xOf_agree _ A _ m hj.le ht) hkn
    rw [hy, hS, e, lab_add_delta]
  · rw [hy, hS]; exact lab_add_delta_mem _ _ _

/-! ### The image of a first bad step -/

/-- The simulated active label of position `s` as read at position `i`, for the input requested
before step `k` of the simulated game. -/
def simX (σ : Rand V m C.length) (k i s : ℕ) : V :=
  if s < i then
    ((eval (extH σ.2.1) (fun j ↦ (xOf m (simRun C m A σ k).1 j, extL σ.1.1 j)) C
      (simM C m σ)).getD s (false, 0)).2
  else 0

/-- No query before step `k` hits the active point of a selector unknown at step `k`. -/
def Fresh (σ : Rand V m C.length) (k : ℕ) : Prop :=
  ∀ j < k, ∀ i y s z o, A.act (simM C m σ) (simRun C m A σ j).2 = .query i y →
    C[i]? = some (.mux s z o) →
    Lin.rl (xOf m (simRun C m A σ k).1) (reqAt m (simRun C m A σ k).1) C i s ≠ 0 →
      y ≠ simX C m A σ k i s

/-- The condition met by the image of a first bad step at `k`, in the simulated game: the action
at step `k` is a query `(i, y)` at a multiplexer with selector `s`, and either `y` is the
simulated active label of `s` plus `Δ`, or `s` is unknown, `y` is its simulated active label and
no earlier query hits the active point of a selector unknown at step `k`. -/
def SimBadAt (Δ : V) (σ : Rand V m C.length) (k : ℕ) : Prop :=
  ∃ i y s z o, A.act (simM C m σ) (simRun C m A σ k).2 = .query i y ∧
    C[i]? = some (.mux s z o) ∧
    (y = simX C m A σ k i s + Δ ∨
      (Lin.rl (xOf m (simRun C m A σ k).1) (reqAt m (simRun C m A σ k).1) C i s ≠ 0 ∧
        y = simX C m A σ k i s ∧ Fresh C m A σ k))

/-- The simulated wires of the image are the real wires, for the input requested before the
truncation. -/
theorem simX_toAdSim (Δ : V) (hΔ : Δ ≠ 0) (p : Rand V m C.length) {k : ℕ}
    (hb : ¬ RealBad C m k A Δ p) (i s : ℕ) :
    simX C m A (toAdSim C m k A Δ p) k i s =
      lab Δ (zr C m Δ p i s) (Lin.rv (xAt C m A Δ p k) C i s) := by
  have hr := simRun_toAdSim C m k A Δ p hb
  have hinp : (fun j ↦ (xOf m (simRun C m A (toAdSim C m k A Δ p) k).1 j,
      extL (toAdSim C m k A Δ p).1.1 j)) = realInp C m k A Δ p := by
    funext j
    rw [hr]
    by_cases hj : j < m
    · simp [realInp, activeInputs, toAdSim, extL, seed, hj]
    · simp [realInp, activeInputs, extL, seed, hj, xOf]
  unfold simX
  rw [hinp, simM_toAdSim]
  by_cases hs : s < i
  · simp only [hs, ↓reduceIte]
    -- the wires with the hash of the image are the real wires
    set inp := realInp C m k A Δ p
    set Ac := realAc (seed C m Δ p.1.1 p.1.2)
    obtain ⟨w1, w2, -⟩ := toSim_walk inp Ac C Δ hΔ p.2
    have hM : realM C m Δ p = idealMaterial (extH p.2.1) inp Ac (rpad (extH p.2.1) Δ) C :=
      realM_eq C m Δ p _
    have e1 : realM C m Δ p = idealMaterial (extH (toSim inp Ac C Δ p.2).1) inp Ac
        (extK (toSim inp Ac C Δ p.2).2) C := hM.trans w1.symm
    have hW : eval (extH (toAdSim C m k A Δ p).2.1) inp C (realM C m Δ p) =
        eval (extH p.2.1) inp C (realM C m Δ p) := by
      calc eval (extH (toAdSim C m k A Δ p).2.1) inp C (realM C m Δ p)
          = idealWiresAux (extH (toSim inp Ac C Δ p.2).1) inp Ac
              (extK (toSim inp Ac C Δ p.2).2) C [] := by
            conv_lhs => rw [e1]
            exact evalAux_ideal _ _ _ _ C []
        _ = idealWiresAux (extH p.2.1) inp Ac (rpad (extH p.2.1) Δ) C [] := w2
        _ = eval (extH p.2.1) inp C (realM C m Δ p) := by
            rw [hM]; exact (evalAux_ideal _ _ _ _ C []).symm
    rw [hW]
    have e := eval_garble (extH p.2.1) (seed C m Δ p.1.1 p.1.2) (xAt C m A Δ p k) C s
    rw [show realM C m Δ p = (garble (extH p.2.1) (seed C m Δ p.1.1 p.1.2) C).2 from rfl]
    simp only [inp, realInp, xAt] at e ⊢
    rw [e]
    have hp := Lin.plain_getD (xOf m (realRun C m A Δ p k).1) C s
    simp only [zr, hs, ↓reduceIte, Lin.rv, zeroL, hp]
    rfl
  · simp [hs, zr, Lin.rv, lab]

/-- **The image of a first bad step.** If step `k` is the first bad step, the image under the
map for the game truncated to `k` steps satisfies `SimBadAt` at `k`. -/
theorem simBadAt_toAdSim (Δ : V) (hΔ : Δ ≠ 0) (p : Rand V m C.length) {k : ℕ}
    (hk : BadStep C m A Δ p k) (hf : ∀ j < k, ¬ BadStep C m A Δ p j) :
    SimBadAt C m A Δ (toAdSim C m k A Δ p) k := by
  have hb := not_realBad_of_first C m A Δ p hf
  have hrun : ∀ j ≤ k, simRun C m A (toAdSim C m k A Δ p) j = realRun C m A Δ p j :=
    fun j hj ↦ simRun_toAdSim_le C m k A Δ p hb hj
  have hM := simM_toAdSim C m k A Δ p
  have hX := simX_toAdSim C m A Δ hΔ p hb
  have hfresh : Fresh C m A (toAdSim C m k A Δ p) k := by
    intro j hj i' y' s' z' o' ha' hC' hne hy'
    rw [hrun k le_rfl] at hne
    rw [hX] at hy'
    rw [hM, hrun j hj.le] at ha'
    refine hf j hj ⟨i', y', s', z', o', ha', hC', fun hkn' ↦ ?_, fun _ ↦ ?_⟩
    · exact absurd (Lin.rl_known_mono (xAt C m A Δ p j) (xAt C m A Δ p k) (rqAt C m A Δ p j)
        (rqAt C m A Δ p k) C (fun t ht ↦ reqAt_mono _ A _ m hj.le ht)
        (fun t ht ↦ xOf_agree _ A _ m hj.le ht) hkn') hne
    · rw [hy']
      cases Lin.rv (xAt C m A Δ p k) C i' s' <;> simp [lab]
  obtain ⟨i, y, s, z, o, ha, hC, h1, h2⟩ := hk
  refine ⟨i, y, s, z, o, by rw [hM, hrun k le_rfl]; exact ha, hC, ?_⟩
  rw [hX, hrun k le_rfl]
  by_cases hkn : Lin.rl (xAt C m A Δ p k) (rqAt C m A Δ p k) C i s = 0
  · left; rw [h1 hkn, lab_add_delta]
  · rcases h2 hkn with hy | hy
    · cases hv : Lin.rv (xAt C m A Δ p k) C i s
      · right
        exact ⟨hkn, by simp [hy, lab], hfresh⟩
      · left; simp [hy, lab, add_assoc, add_self_eq_zero']
    · cases hv : Lin.rv (xAt C m A Δ p k) C i s
      · left; simp [hy, lab]
      · right
        exact ⟨hkn, by simp [hy, lab], hfresh⟩

end Bad

end GcZk.Adaptive
