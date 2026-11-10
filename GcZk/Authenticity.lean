/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.Jko

/-!
# Authenticity of privacy-free Free-XOR garbling

An evaluator who knows the material and the active labels of an input `x` can compute every
active label. The inactive label of a wire is the active one plus `Δ`, so authenticity (no
inactive output label) amounts to: the evaluator cannot find `Δ`.

The *ideal garbler* `idealMaterial` produces the material of a circuit from the active input
labels, the active labels of the constants, the hash `H` and one *pad* per multiplexer, and it
never uses `Δ`. The material of a multiplexer at position `i` with active selector label `S` is

  `T = H(i, S) + Z_act + O_act + pad_i`.

## Main results

* `GcZk.Auth.garble_eq_idealMaterial`: the real material is the ideal material with the pads
  `pad_i = H(i, S + Δ) + c_i Δ`. Here `S + Δ` is the inactive selector label and `c_i` is the
  XOR of the two candidate values. So **`Δ` reaches the evaluator's view only through the
  hashes of inactive selector labels.**
* `GcZk.Auth.exists_pads`: the same statement with the pads indexed by position only.
* `GcZk.Auth.ideal_bound`: if the pads are uniform and independent of `Δ`, an adversary that
  sees the material (and knows `x`, the active labels and `H`) outputs the inactive output label
  for at most `|V|^m` of the `(|V| - 1) |V|^m` pairs `(Δ, pads)`. Its success probability
  is at most `1 / (|V| - 1)`.
* `GcZk.Jko.authWin_iff`: the authenticity game of `GcZk.Jko` is the game of outputting
  `active output label + Δ`.

## The random oracle argument

The step from the real scheme to the ideal model is the random oracle argument. With `H` a
random oracle, `H(i, S + Δ)` is uniform and independent of the rest of the view as long as the
adversary never queries `(i, S + Δ)`. Each query `(i, y)` hits only if `Δ = y + S_i`. The
standard bound for `q` queries is then about `(q + 1) / (|V| - 1)`. The query accounting of that
argument (identical-until-bad) is formalized in `GcZk.RandomOracle` (`GcZk.RO.rom_bound`) and
`GcZk.Security` (`GcZk.Sec.garble_rom_bound`), not in this file.
-/

namespace GcZk.Auth

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The ciphertext of the ideal garbler for a multiplexer at position `ws.length`. -/
def muxT (H : ℕ → V → V) (pad : ℕ → V → Bool → V) (ws : List (Wire V)) (s z o : ℕ) : V :=
  H ws.length (ws.getD s (false, 0)).2 + (ws.getD z (false, 0)).2 + (ws.getD o (false, 0)).2 +
    pad ws.length (ws.getD s (false, 0)).2
      ((ws.getD z (false, 0)).1 ^^ (ws.getD o (false, 0)).1)

/-- The material the ideal garbler produces for one node, from the evaluated earlier wires.
`Ac i b` is the active label of a constant `b` at position `i`. It does not use `Δ`. -/
def idealNode (H : ℕ → V → V) (Ac : ℕ → Bool → V) (pad : ℕ → V → Bool → V)
    (ws : List (Wire V)) : Node → Material V
  | .input _ => .free
  | .const b => .const (Ac ws.length b)
  | .xor _ _ => .free
  | .mux s z o => .mux (muxT H pad ws s z o)

/-- The ideal garbler runs alongside the evaluator. -/
def idealAux (H : ℕ → V → V) (inp : ℕ → Wire V) (Ac : ℕ → Bool → V)
    (pad : ℕ → V → Bool → V) : Circuit → List (Wire V) → List (Material V)
  | [], _ => []
  | n :: ns, ws => idealNode H Ac pad ws n ::
      idealAux H inp Ac pad ns (ws ++ [evalNode H inp ws n (idealNode H Ac pad ws n)])

/-- The material of the ideal garbler. -/
def idealMaterial (H : ℕ → V → V) (inp : ℕ → Wire V) (Ac : ℕ → Bool → V)
    (pad : ℕ → V → Bool → V) (C : Circuit) : List (Material V) :=
  idealAux H inp Ac pad C []

/-! ### The real material is ideal -/

/-- The active labels of the constants of the real garbling. -/
def realAc (σ : Seed V) : ℕ → Bool → V := fun i b ↦ lab σ.delta (σ.const i) b

/-- The pads of the real garbling: the hash of the inactive selector label, shifted by `Δ` when
the two candidates differ. -/
def realPad (H : ℕ → V → V) (σ : Seed V) : ℕ → V → Bool → V :=
  fun i S c ↦ H i (S + σ.delta) + if c then σ.delta else 0

theorem idealNode_eq (H : ℕ → V → V) (σ : Seed V) (n : Node) {bs : List V} {vs : List Bool}
    {ws : List (Wire V)} (h : Good σ.delta bs vs ws) :
    idealNode H (realAc σ) (realPad H σ) ws n = (garbleNode H σ bs n).2 := by
  obtain ⟨-, hw, hg⟩ := h
  cases n with
  | input j => rfl
  | const b => simp [idealNode, garbleNode, realAc, hw]
  | xor a b => rfl
  | mux s z o =>
    simp only [idealNode, garbleNode, muxT, realPad, hg s, hg z, hg o, hw, Material.mux.injEq]
    have hΔ : bs.getD s 0 + σ.delta + σ.delta = bs.getD s 0 := by
      rw [add_assoc, add_self_eq_zero', add_zero]
    cases vs.getD s false <;> cases vs.getD z false <;> cases vs.getD o false <;>
      simp only [lab_false, lab_true, hΔ, Bool.xor_false, Bool.xor_true, Bool.not_false,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, add_zero] <;>
      abel_nf <;> simp only [two_zsmul_eq_zero', zero_add]

theorem idealAux_eq (H : ℕ → V → V) (σ : Seed V) (x : ℕ → Bool) (C : Circuit) :
    ∀ {bs : List V} {vs : List Bool} {ws : List (Wire V)}, Good σ.delta bs vs ws →
      idealAux H (activeInputs σ x) (realAc σ) (realPad H σ) C ws = (garbleAux H σ C bs).2 := by
  induction C with
  | nil => intro _ _ _ _; rfl
  | cons n ns ih =>
    intro bs vs ws h
    simp only [idealAux, garbleAux, idealNode_eq H σ n h]
    exact congrArg _ (ih (good_snoc H σ x n h))

/-- **The real material is ideal.** The material of the real garbling is the material of the
ideal garbler, which does not use `Δ`, with the pads `H(i, S + Δ) + c Δ`. -/
theorem garble_eq_idealMaterial (H : ℕ → V → V) (σ : Seed V) (x : ℕ → Bool) (C : Circuit) :
    (garble H σ C).2 = idealMaterial H (activeInputs σ x) (realAc σ) (realPad H σ) C :=
  (idealAux_eq H σ x C (good_nil σ.delta)).symm

omit [Module (ZMod 2) V] in
/-- The ideal garbler on the nodes after `ws` reads the pads only at positions `≥ ws.length`. -/
theorem idealAux_congr (H : ℕ → V → V) (inp : ℕ → Wire V) (Ac : ℕ → Bool → V) (C : Circuit) :
    ∀ {pad pad' : ℕ → V → Bool → V} {ws : List (Wire V)},
      (∀ i, ws.length ≤ i → pad i = pad' i) →
        idealAux H inp Ac pad C ws = idealAux H inp Ac pad' C ws := by
  induction C with
  | nil => intro _ _ _ _; rfl
  | cons n ns ih =>
    intro pad pad' ws h
    have hn : idealNode H Ac pad ws n = idealNode H Ac pad' ws n := by
      cases n <;> simp [idealNode, muxT, h ws.length le_rfl]
    simp only [idealAux, hn]
    exact congrArg _ (ih fun i hi ↦ h i (by simp at hi; omega))

omit [Module (ZMod 2) V] in
/-- Any pads can be replaced by pads that depend on the position only. -/
theorem idealAux_exists_pads (H : ℕ → V → V) (inp : ℕ → Wire V) (Ac : ℕ → Bool → V)
    (C : Circuit) : ∀ (pad : ℕ → V → Bool → V) (ws : List (Wire V)), ∃ K : ℕ → V,
      idealAux H inp Ac pad C ws = idealAux H inp Ac (fun i _ _ ↦ K i) C ws := by
  induction C with
  | nil => intro _ _; exact ⟨0, rfl⟩
  | cons n ns ih =>
    intro pad ws
    obtain ⟨K, hK⟩ := ih pad (ws ++ [evalNode H inp ws n (idealNode H Ac pad ws n)])
    let c : V := match n with
      | .mux s z o => pad ws.length (ws.getD s (false, 0)).2
          ((ws.getD z (false, 0)).1 ^^ (ws.getD o (false, 0)).1)
      | _ => 0
    refine ⟨Function.update K ws.length c, ?_⟩
    have hn : idealNode H Ac pad ws n =
        idealNode H Ac (fun i _ _ ↦ Function.update K ws.length c i) ws n := by
      cases n <;> simp [idealNode, muxT, c]
    simp only [idealAux, ← hn, hK]
    refine congrArg _ (idealAux_congr H inp Ac ns fun i hi ↦ ?_)
    have : i ≠ ws.length := by simp at hi; omega
    simp [Function.update_of_ne this]

/-- **The real material with position pads.** For every seed there are pads `K`, one per
position, with which the ideal garbler (which does not use `Δ`) produces the real material.
`K i` is `H(i, S_i + Δ) + c_i Δ` at a multiplexer. -/
theorem exists_pads (H : ℕ → V → V) (σ : Seed V) (x : ℕ → Bool) (C : Circuit) :
    ∃ K : ℕ → V, (garble H σ C).2 =
      idealMaterial H (activeInputs σ x) (realAc σ) (fun i _ _ ↦ K i) C := by
  obtain ⟨K, hK⟩ := idealAux_exists_pads H (activeInputs σ x) (realAc σ) C (realPad H σ) []
  exact ⟨K, (garble_eq_idealMaterial H σ x C).trans hK⟩

/-! ### The bound in the ideal model -/

/-- The active output label, as the evaluator computes it from the material. -/
def activeOut (H : ℕ → V → V) (inp : ℕ → Wire V) (C : Circuit) (out : ℕ)
    (M : List (Material V)) : V :=
  ((eval H inp C M).getD out (false, 0)).2

/-- The ideal material with pads `K : Fin m → V` (pad `0` beyond `m`). -/
def padMaterial (H : ℕ → V → V) (inp : ℕ → Wire V) (Ac : ℕ → Bool → V) (C : Circuit) (m : ℕ)
    (K : Fin m → V) : List (Material V) :=
  idealMaterial H inp Ac (fun i _ _ ↦ if h : i < m then K ⟨i, h⟩ else 0) C

omit [Module (ZMod 2) V] in
/-- **Authenticity in the ideal model.** Fix the circuit, the active input labels, the active
constant labels and `H`. For any adversary `Z` that sees the material, the pairs `(Δ, K)` with
`Δ ≠ 0` for which `Z` outputs the inactive output label `active + Δ` number at most `|V|^m`.
With `Δ` uniform on `V \ {0}` and `K` uniform on `V^m`, the success probability is at most
`1 / (|V| - 1)`. The bound holds for every fixed active labels and `H`, hence also on average
over any distribution of them independent of `(Δ, K)`. -/
theorem ideal_bound [Fintype V] [DecidableEq V] (H : ℕ → V → V) (inp : ℕ → Wire V)
    (Ac : ℕ → Bool → V) (C : Circuit) (out m : ℕ) (Z : List (Material V) → V) :
    (Finset.univ.filter fun p : V × (Fin m → V) ↦ p.1 ≠ 0 ∧
        Z (padMaterial H inp Ac C m p.2) =
          activeOut H inp C out (padMaterial H inp Ac C m p.2) + p.1).card ≤
      Fintype.card (Fin m → V) := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn Prod.snd (fun _ _ ↦ Finset.mem_univ _) ?_
  intro p hp q hq hpq
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
  have h1 : p.1 = q.1 := by
    have := hp.2; rw [hpq] at this
    exact add_left_cancel (this.symm.trans hq.2)
  exact Prod.ext h1 hpq

end GcZk.Auth

namespace GcZk.Jko

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The authenticity game of `GcZk.Jko` is the game of outputting `active output label + Δ`,
where the active output label is computed by the evaluator from the material. -/
theorem authWin_iff (H : ℕ → V → V) (C : Circuit) (out : ℕ) (σ : Seed V) (A : Prover V) :
    AuthWin H C out σ A ↔
      A.respond (garble H σ C).2 (fun j ↦ (activeInputs σ A.choice j).2) =
        Auth.activeOut H (activeInputs σ A.choice) C out (garble H σ C).2 + σ.delta := by
  rw [AuthWin, Auth.activeOut, eval_garble]
  cases (plain A.choice C).getD out false <;>
    simp only [Bool.not_false, Bool.not_true, lab_false, lab_true]
  rw [add_assoc, add_self_eq_zero', add_zero]

end GcZk.Jko
