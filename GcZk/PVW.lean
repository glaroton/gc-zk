/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
import GcZk.EndToEnd

/-!
# The dual-mode OT of Peikert, Vaikuntanathan and Waters

We write the DDH instance of the dual-mode cryptosystem of [PVW08, Sect. 5.3] additively, in a
group `Gp` of prime order `q`. The messy-mode common string is `(g₀, h₀, g₁, h₁)` with
`h_b = x_b • g_b`, where the `g_b` are nonzero and `x₀ ≠ x₁`; the trapdoor is `(x₀, x₁)`.
* A receiver with choice `σ` and secret `r` sends `pk = (r • g_σ, r • h_σ)`.
* The sender encrypts `m` on branch `b` with coins `(s, t)` as
  `(s • g_b + t • h_b, s • pk₁ + t • pk₂ + m)` (built on `Randomize` of [PVW08, Lemma 5.1]).
* The receiver decrypts `(c₀, c₁)` as `c₁ - r • c₀`.

Branch `b` of a key `pk` is *messy* when `pk₂ ≠ x_b • pk₁`: then encryption on branch `b` is a
bijection from the coins to `Gp × Gp`, whatever the message (`enc_bijective`), so a ciphertext with
uniform coins is uniform and carries no information. This is the second case of
[PVW08, Lemma 5.1], in the exact form.

## Extraction and the degenerate key

`FindMessy` of [PVW08, Sect. 5.3] outputs `0` if `pk₂ ≠ x₀ • pk₁` and `1` otherwise, arguing that
in the second case `pk₂ = x₀ • pk₁ ≠ x₁ • pk₁`. This needs `pk₁ ≠ 0`: for the key `pk = (0, 0)`
both branches leak the message (`enc_zero_key`). The version of August 2008 does not check this;
the revision of January 2019 does, since its sender outputs nothing when `pk₁ = 0` (the identity, in
multiplicative notation). We follow the revision: the sender rejects `pk₁ = 0`, and then one branch
of every key is messy (`messy_of_ext`), and the receiver's choice is extracted as the other one
(`ext`).

## Main results

* `GcZk.PVW.dec_enc`: decryption is correct on the receiver's branch.
* `GcZk.PVW.enc_bijective`: on a messy branch, encryption is a bijection of the coins.
* `GcZk.PVW.messy_of_ext`: if `pk₁ ≠ 0`, the branch other than `ext pk` is messy.
* `GcZk.PVW.enc_zero_key`: on the key `(0, 0)` the second component of the ciphertext is the
  message.

## References

* [PVW08] C. Peikert, V. Vaikuntanathan, B. Waters, *A framework for efficient and composable
  oblivious transfer*, CRYPTO 2008, LNCS 5157, 554–571. Full version, IACR ePrint 2007/348, revised
  January 23, 2019.
-/

namespace GcZk.PVW

variable {q : ℕ} {Gp : Type*} [AddCommGroup Gp] [Module (ZMod q) Gp]

/-- A common string `(g₀, h₀, g₁, h₁)`: public group elements only. -/
structure Crs (Gp : Type*) where
  g : Bool → Gp
  h : Bool → Gp

/-- A messy-mode common string with trapdoor `t = (x₀, x₁)`: the `g_b` are nonzero,
`h_b = x_b • g_b`, and `x₀ ≠ x₁`. -/
structure Crs.Messy (c : Crs Gp) (t : Bool → ZMod q) : Prop where
  g_ne : ∀ b, c.g b ≠ 0
  x_ne : t false ≠ t true
  h_eq : ∀ b, c.h b = t b • c.g b

/-- The receiver's key for the choice `σ` and the secret `r`. -/
def keyGen (c : Crs Gp) (σ : Bool) (r : ZMod q) : Gp × Gp := (r • c.g σ, r • c.h σ)

/-- Encryption of `m` on branch `b` with coins `st`. -/
def enc (c : Crs Gp) (pk : Gp × Gp) (b : Bool) (m : Gp) (st : ZMod q × ZMod q) : Gp × Gp :=
  (st.1 • c.g b + st.2 • c.h b, st.1 • pk.1 + st.2 • pk.2 + m)

/-- Decryption with the secret `r`. -/
def dec (r : ZMod q) (ct : Gp × Gp) : Gp := ct.2 - r • ct.1

/-- **Correctness** on the receiver's branch. -/
theorem dec_enc (c : Crs Gp) (σ : Bool) (r : ZMod q) (m : Gp) (st : ZMod q × ZMod q) :
    dec r (enc c (keyGen c σ r) σ m st) = m := by
  simp only [dec, enc, keyGen, smul_add, smul_smul, mul_comm r]
  abel

/-- **The degenerate key.** On the key `(0, 0)`, every ciphertext carries the message in clear. -/
theorem enc_zero_key (c : Crs Gp) (b : Bool) (m : Gp) (st : ZMod q × ZMod q) :
    (enc c (0, 0) b m st).2 = m := by
  simp [enc]

variable (q) in
/-- A decryption-mode common string: `h_b = x • g_b` for a common `x`, and `g₁ = y • g₀` with
`y ≠ 0`. -/
def Crs.Dec (c : Crs Gp) : Prop :=
  ∃ x y : ZMod q, y ≠ 0 ∧ c.g true = y • c.g false ∧ ∀ b, c.h b = x • c.g b

/-- In decryption mode the key of the choice `1` with secret `r` is the key of the choice `0` with
secret `y r`. This is trapdoor key generation in [PVW08, Sect. 5.3]. -/
theorem keyGen_dec (c : Crs Gp) {x y : ZMod q} (hy : c.g true = y • c.g false)
    (hh : ∀ b, c.h b = x • c.g b) (r : ZMod q) : keyGen c true r = keyGen c false (y * r) := by
  simp only [keyGen, hh, hy, smul_smul, Prod.mk.injEq]
  constructor <;> congr 1 <;> ring

/-- The extracted choice, with the trapdoor `t`: `false` if `pk₂ = x₀ • pk₁`, `true` otherwise. -/
def ext [DecidableEq Gp] (t : Bool → ZMod q) (pk : Gp × Gp) : Bool :=
  !decide (pk.2 = t false • pk.1)

section Prime

variable [Fact q.Prime]

/-- **Messy branch.** If `pk₁ ≠ 0`, the branch other than `ext pk` is messy. -/
theorem messy_of_ext (c : Crs Gp) {t : Bool → ZMod q} (hc : c.Messy t) [DecidableEq Gp]
    {pk : Gp × Gp} (hpk : pk.1 ≠ 0) : pk.2 ≠ t (!ext t pk) • pk.1 := by
  by_cases h : pk.2 = t false • pk.1
  · have he : ext t pk = false := by simp [ext, h]
    rw [he, Bool.not_false, h]
    intro h'
    have : (t false - t true) • pk.1 = 0 := by rw [sub_smul, h', sub_self]
    rcases smul_eq_zero.1 this with h0 | h0
    · exact hc.x_ne (sub_eq_zero.1 h0)
    · exact hpk h0
  · have he : ext t pk = true := by simp [ext, h]
    rwa [he, Bool.not_true]

/-- **Encryption on a messy branch is a bijection of the coins.** This is the exact form of the
second case of [PVW08, Lemma 5.1]. -/
theorem enc_bijective [Fintype Gp] (hcard : Fintype.card Gp = q) (c : Crs Gp) {b : Bool}
    {s : ZMod q} (hg : c.g b ≠ 0) (hh : c.h b = s • c.g b) {pk : Gp × Gp} (hpk : pk.2 ≠ s • pk.1)
    (m : Gp) :
    Function.Bijective (enc (q := q) c pk b m) := by
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun st st' h ↦ ?_, by simp [hcard]⟩
  simp only [enc, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  set ds := st.1 - st'.1
  set dt := st.2 - st'.2
  have e1 : (ds + dt * s) • c.g b = 0 := by
    have : (ds + dt * s) • c.g b =
        (st.1 • c.g b + st.2 • c.h b) - (st'.1 • c.g b + st'.2 • c.h b) := by
      simp only [ds, dt, hh]; module
    rw [this, h1, sub_self]
  have hs : ds + dt * s = 0 := (smul_eq_zero.1 e1).resolve_right hg
  have e2 : dt • (pk.2 - s • pk.1) = 0 := by
    have : dt • (pk.2 - s • pk.1) =
        (st.1 • pk.1 + st.2 • pk.2 + m) - (st'.1 • pk.1 + st'.2 • pk.2 + m) -
          (ds + dt * s) • pk.1 := by
      simp only [ds, dt]; module
    rw [this, h2, sub_self, hs, zero_smul, sub_zero]
  have ht : dt = 0 := (smul_eq_zero.1 e2).resolve_right (sub_ne_zero.2 hpk)
  have hs' : ds = 0 := by rw [ht, zero_mul, add_zero] at hs; exact hs
  exact Prod.ext (sub_eq_zero.1 hs') (sub_eq_zero.1 ht)

end Prime

end GcZk.PVW
