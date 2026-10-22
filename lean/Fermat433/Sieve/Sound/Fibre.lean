/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Mathlib

/-!
# Soundness of the checker, part 3b: fibres of multiplication by the cofactor

Let `G` be a finite abelian group of order `ℓc`, `ℓ` prime, `ℓ ∤ c`. Then every fibre of `Q ↦ c • Q`
has at most `c` elements, so `c` distinct elements of a fibre are the whole fibre. This is what lets
the checker certify that no point of `X(𝔽_q)` reaches a target by listing only `c` points.

The proof: by Cauchy's theorem `G` has an element `g` of order `ℓ`, and `g = c • (k • g)` for `k` an
inverse of `c` modulo `ℓ`, so `⟨g⟩` lies in the image of `c • ·`. Hence `ℓ` divides the size of the
image, the kernel has at most `c` elements, and a fibre is a translate of the kernel.
-/

namespace Fermat433.Sieve

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem ncard_fibre_nsmul_le {ℓ : ℕ} (hℓ : ℓ.Prime) (c : ℕ) (hG : Nat.card G = c * ℓ)
    (hc : ¬ ℓ ∣ c) (T : G) : {Q : G | c • Q = T}.ncard ≤ c := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let φ : G →+ G := nsmulAddMonoidHom c
  obtain ⟨g, hg⟩ :=
    exists_prime_addOrderOf_dvd_card' (G := G) ℓ (by rw [hG]; exact dvd_mul_left _ _)
  -- `g` is in the image of `c • ·`
  have hcop : Nat.Coprime c ℓ :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hc))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, c * k % ℓ = 1 := by
    refine ⟨(c : ZMod ℓ)⁻¹.val, ?_⟩
    have h := ZMod.coe_mul_inv_eq_one c hcop
    rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, h, ZMod.val_one]
  have hgr : g ∈ φ.range := by
    refine ⟨k • g, ?_⟩
    change c • k • g = g
    rw [smul_smul, ← mod_addOrderOf_nsmul, hg, hk, one_nsmul]
  -- `ℓ` divides the size of the image, so the kernel has at most `c` elements
  have hdvd : ℓ ∣ Nat.card φ.range := by
    have := AddSubgroup.card_dvd_of_le ((AddSubgroup.zmultiples_le).mpr hgr)
    rwa [Nat.card_zmultiples, hg] at this
  have hker : Nat.card φ.ker ≤ c := by
    have h := AddSubgroup.card_ker_mul_card_range φ
    rw [hG] at h
    obtain ⟨m, hm⟩ := hdvd
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => by
      have := Nat.card_pos (α := φ.range)
      rw [hm, h0, mul_zero] at this
      exact lt_irrefl 0 this
    rw [hm] at h
    have hkm : Nat.card φ.ker * m = c :=
      Nat.eq_of_mul_eq_mul_left hℓ.pos (by
        rw [show ℓ * (Nat.card φ.ker * m) = Nat.card φ.ker * (ℓ * m) by ring, h, mul_comm])
    rw [← hkm]
    exact Nat.le_mul_of_pos_right _ hm0
  -- a fibre is a translate of the kernel
  rcases Set.eq_empty_or_nonempty {Q : G | c • Q = T} with he | ⟨Q0, hQ0⟩
  · rw [he, Set.ncard_empty]; exact Nat.zero_le _
  · have hsub : {Q : G | c • Q = T} ⊆ (Q0 + ·) '' (φ.ker : Set G) := by
      intro Q hQ
      refine ⟨Q - Q0, ?_, by simp⟩
      change c • (Q - Q0) = 0
      rw [nsmul_sub, hQ, (show c • Q0 = T from hQ0), sub_self]
    calc {Q : G | c • Q = T}.ncard ≤ ((Q0 + ·) '' (φ.ker : Set G)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (φ.ker : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = Nat.card φ.ker := rfl
      _ ≤ c := hker

/-- `c` distinct elements of a fibre of `c • ·` are all of it. -/
theorem mem_of_fibre {ℓ c : ℕ} (hℓ : ℓ.Prime) (hG : Nat.card G = c * ℓ) (hc : ¬ ℓ ∣ c) {T : G}
    (L : List G) (hnd : L.Nodup) (hlen : L.length = c) (hL : ∀ Q ∈ L, c • Q = T)
    {Q : G} (hQ : c • Q = T) : Q ∈ L := by
  classical
  have hsub : (L.toFinset : Set G) ⊆ {Q : G | c • Q = T} := fun x hx => hL x (by simpa using hx)
  have hcard : (L.toFinset : Set G).ncard = c := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen]
  have heq : (L.toFinset : Set G) = {Q : G | c • Q = T} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact ncard_fibre_nsmul_le hℓ c hG hc T)
      (Set.toFinite _)
  have : Q ∈ (L.toFinset : Set G) := heq ▸ hQ
  simpa using this

end Fermat433.Sieve
