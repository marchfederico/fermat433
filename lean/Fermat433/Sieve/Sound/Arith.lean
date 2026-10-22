/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Mathlib
import Fermat433.Sieve.Check

/-!
# Soundness of the checker, part 1: arithmetic modulo `q`

The checker computes on natural-number representatives. Here each operation is shown to compute
what it claims in `ZMod q`: `powMod` is exponentiation, `inv` is the inverse when `q` is prime,
`sub` is subtraction, `ofInt` is the cast from `ℤ`, and `euler` detects non-squares.
-/

namespace Fermat433.Sieve

lemma powModAux_cast (q : ℕ) :
    ∀ (fuel b e : ℕ), e < 2 ^ fuel → (powModAux fuel b e q : ZMod q) = (b : ZMod q) ^ e := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e he
    obtain rfl : e = 0 := by simpa using he
    simp [powModAux, ZMod.natCast_mod]
  | succ n ih =>
    intro b e he
    unfold powModAux
    by_cases h0 : e = 0
    · simp [h0, ZMod.natCast_mod]
    · have hlt : e / 2 < 2 ^ n := by rw [pow_succ] at he; omega
      have hrec := ih (b * b % q) (e / 2) hlt
      simp only [h0, ite_false]
      have hb : ((b * b % q : ℕ) : ZMod q) ^ (e / 2) = (b : ZMod q) ^ (2 * (e / 2)) := by
        rw [ZMod.natCast_mod, Nat.cast_mul, pow_mul, sq]
      split_ifs with hodd
      · rw [ZMod.natCast_mod, Nat.cast_mul, hrec, hb, ← pow_succ]
        congr 1; omega
      · rw [hrec, hb]; congr 1; omega

lemma powMod_cast (b e q : ℕ) (he : e < 2 ^ 64) :
    (powMod b e q : ZMod q) = (b : ZMod q) ^ e := by
  rw [powMod, powModAux_cast q 64 _ e he, ZMod.natCast_mod]

lemma powModAux_lt {q : ℕ} (hq : 0 < q) :
    ∀ (fuel b e : ℕ), powModAux fuel b e q < q := by
  intro fuel
  induction fuel with
  | zero => intro b e; simp [powModAux, Nat.mod_lt _ hq]
  | succ n ih =>
    intro b e
    unfold powModAux
    split_ifs
    · exact Nat.mod_lt _ hq
    · exact Nat.mod_lt _ hq
    · exact ih _ _

lemma powMod_lt {q : ℕ} (hq : 0 < q) (b e : ℕ) : powMod b e q < q := powModAux_lt hq _ _ _

/-- `inv` is the inverse modulo an odd prime. -/
lemma inv_cast {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) (a : ℕ) (hq64 : q < 2 ^ 64) :
    (inv a q : ZMod q) = (a : ZMod q)⁻¹ := by
  have h2 : 2 ≤ q := hq.out.two_le
  rw [inv, powMod_cast _ _ _ (by omega)]
  by_cases ha : (a : ZMod q) = 0
  · rw [ha, inv_zero, zero_pow (by omega)]
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show q - 2 + 1 = q - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one ha

lemma sub_cast {q : ℕ} (hq : 0 < q) (a b : ℕ) : (sub a b q : ZMod q) = a - b := by
  rw [sub, ZMod.natCast_mod, Nat.cast_sub (by have := Nat.mod_lt b hq; omega), Nat.cast_add,
    ZMod.natCast_self, ZMod.natCast_mod]
  ring

lemma sub_lt {q : ℕ} (hq : 0 < q) (a b : ℕ) : sub a b q < q := Nat.mod_lt _ hq

lemma ofInt_cast (z : ℤ) {q : ℕ} (hq : 0 < q) : (ofInt z q : ZMod q) = z := by
  have h : 0 ≤ z % (q : ℤ) := Int.emod_nonneg _ (by omega)
  rw [ofInt, ← Int.cast_natCast, Int.toNat_of_nonneg h, ZMod.intCast_mod]

lemma ofInt_lt (z : ℤ) {q : ℕ} (hq : 0 < q) : ofInt z q < q := by
  have h1 : 0 ≤ z % (q : ℤ) := Int.emod_nonneg _ (by omega)
  have h2 : z % (q : ℤ) < q := Int.emod_lt_of_pos _ (by omega)
  rw [ofInt]; omega

/-- If Euler's criterion gives `q − 1`, then `a` is not a square modulo `q` (for odd prime `q`). -/
lemma not_isSquare_of_euler {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) (hq64 : q < 2 ^ 64)
    (a : ℕ) (h : euler a q = q - 1) : ¬ IsSquare (a : ZMod q) := by
  have h2 : 2 ≤ q := hq.out.two_le
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (hq.out.odd_of_ne_two hq2)
  have hcast := congrArg (fun n : ℕ => (n : ZMod q)) h
  simp only [euler] at hcast
  rw [powMod_cast _ _ _ (by omega), Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one,
    zero_sub] at hcast
  intro hsq
  by_cases ha : (a : ZMod q) = 0
  · rw [ha, zero_pow (by omega)] at hcast
    exact one_ne_zero (neg_eq_zero.mp hcast.symm)
  · have := (ZMod.euler_criterion q ha).mp hsq
    rw [show (q - 1) / 2 = q / 2 by omega, this] at hcast
    have h0 : ((2 : ℕ) : ZMod q) = 0 := by push_cast; linear_combination hcast
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 q).mp h0)
    omega

end Fermat433.Sieve
