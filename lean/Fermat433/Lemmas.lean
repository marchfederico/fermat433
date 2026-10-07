/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Statement

/-!
# Elementary lemmas used by the reduction
-/

open ZT

namespace Fermat433

/-- `p` divides every coordinate of `v`. -/
def DvdAll (p : ℤ) (v : ZT) : Prop := p ∣ v.r0 ∧ p ∣ v.r1 ∧ p ∣ v.r2

lemma DvdAll.mul_left {p : ℤ} {v : ZT} (h : DvdAll p v) (u : ZT) : DvdAll p (u * v) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [mul_r0, mul_r1, mul_r2]
  · exact dvd_add (dvd_mul_of_dvd_right h0 _) (dvd_mul_of_dvd_right
      (dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)) _)
  · exact dvd_add (dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h0 _))
      (dvd_mul_of_dvd_right h2 _)
  · exact dvd_add (dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _))
      (dvd_mul_of_dvd_right h0 _)

lemma DvdAll.mul_right {p : ℤ} {v : ZT} (h : DvdAll p v) (u : ZT) : DvdAll p (v * u) := by
  rw [mul_comm]; exact h.mul_left u

lemma DvdAll.neg {p : ℤ} {v : ZT} (h : DvdAll p v) : DvdAll p (-v) := by
  obtain ⟨h0, h1, h2⟩ := h
  exact ⟨(dvd_neg).2 h0, (dvd_neg).2 h1, (dvd_neg).2 h2⟩

lemma DvdAll.dvd_N {p : ℤ} {v : ZT} (h : DvdAll p v) : p ∣ N v := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := h
  exact ⟨p ^ 2 * N ⟨a, b, c⟩, by simp only [N, ha, hb, hc]; ring⟩

/-- A prime dividing two integers of which one is odd is impossible to have dividing 2. -/
lemma not_dvd_two_of_dvd_odd {p n : ℤ} (hp : Prime p) (hn : Odd n) (hpn : p ∣ n) : ¬ p ∣ 2 := by
  intro h2
  obtain ⟨m, rfl⟩ := hn
  have : p ∣ 1 := (Int.dvd_add_right (dvd_mul_of_dvd_left h2 m)).mp hpn
  exact hp.not_isUnit (isUnit_of_dvd_one this)

/-- An integer with no prime factor is `±1`. -/
lemma eq_one_or_neg_one {e : ℤ} (h : ∀ p : ℤ, Prime p → p ∣ e → False) : e = 1 ∨ e = -1 := by
  by_contra hne
  have : e.natAbs ≠ 1 := by
    intro h1; rcases Int.natAbs_eq e with h' | h' <;> rw [h1] at h' <;> simp_all
  obtain ⟨p, hp, hpe⟩ := Int.exists_prime_and_dvd this
  exact h p hp hpe

/-- `17` is not a square (it is not a square mod 3). -/
lemma sq_ne_17 (x : ℤ) : x ^ 2 ≠ 17 := by
  intro h
  have h3 := congrArg (Int.cast : ℤ → ZMod 3) h
  push_cast at h3
  generalize (x : ZMod 3) = X at h3
  revert X; decide

/-- If `d² = uv` and `u, v` have no common prime factor except possibly 2, which then divides
`v` exactly once, then `u ∈ {±m², ±2m²}`. This is the twist-class computation of Lemma A.3. -/
lemma sq_class {d u v : ℤ} (h : d ^ 2 = u * v)
    (H1 : ∀ p : ℤ, Prime p → p ∣ u → p ∣ v → p ∣ 2) (H2 : 2 ∣ u → 2 ∣ v → ¬ 4 ∣ v) :
    ∃ m : ℤ, u = m ^ 2 ∨ u = -m ^ 2 ∨ u = 2 * m ^ 2 ∨ u = -(2 * m ^ 2) := by
  by_cases h2 : (2 : ℤ) ∣ u ∧ 2 ∣ v
  · obtain ⟨⟨u', rfl⟩, ⟨v', rfl⟩⟩ := h2
    have hv' : Odd v' := by
      rw [← Int.not_even_iff_odd, even_iff_two_dvd]
      intro ⟨w, hw⟩; exact H2 (dvd_mul_right 2 u') (dvd_mul_right 2 v') ⟨w, by rw [hw]; ring⟩
    have hd : (2 : ℤ) ∣ d := Int.prime_two.dvd_of_dvd_pow (n := 2) ⟨u' * 2 * v', by rw [h]; ring⟩
    obtain ⟨e, rfl⟩ := hd
    have he : u' * v' = e ^ 2 := by linarith
    have hcop : IsCoprime u' v' := by
      apply isCoprime_of_prime_dvd
      · rintro ⟨-, rfl⟩; exact absurd hv' (by decide)
      · intro p hp hpu hpv
        exact not_dvd_two_of_dvd_odd hp hv' hpv
          (H1 p hp (dvd_mul_of_dvd_right hpu 2) (dvd_mul_of_dvd_right hpv 2))
    obtain ⟨m, hm | hm⟩ := Int.sq_of_isCoprime hcop he
    · exact ⟨m, Or.inr (Or.inr (Or.inl (by rw [hm])))⟩
    · exact ⟨m, Or.inr (Or.inr (Or.inr (by rw [hm]; ring)))⟩
  · have hcop : IsCoprime u v := by
      apply isCoprime_of_prime_dvd
      · rintro ⟨rfl, rfl⟩; exact h2 ⟨dvd_zero 2, dvd_zero 2⟩
      · intro p hp hpu hpv
        have hassoc := hp.associated_of_dvd Int.prime_two (H1 p hp hpu hpv)
        exact h2 ⟨hassoc.dvd_iff_dvd_left.mp hpu, hassoc.dvd_iff_dvd_left.mp hpv⟩
    obtain ⟨m, hm | hm⟩ := Int.sq_of_isCoprime hcop h.symm
    · exact ⟨m, Or.inl hm⟩
    · exact ⟨m, Or.inr (Or.inl hm)⟩

end Fermat433
