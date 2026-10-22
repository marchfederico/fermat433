/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Sieve.Sound.Curve

/-!
# Soundness of the checker, part 3a: counting points

`Curve.order` computes `q + 1 + Σₓ (rhs(x) / q)` with Euler's criterion. Here it is shown to be the
number of points of the Mathlib curve: each `x` contributes `1 + χ(rhs x)` affine points, where `χ`
is the quadratic character (`quadraticChar_card_sqrts`), and the point at infinity adds one.
-/

namespace Fermat433.Sieve

open WeierstrassCurve WeierstrassCurve.Affine Finset

lemma foldl_add_eq {α : Type*} (f : α → ℤ) :
    ∀ (l : List α) (a : ℤ), l.foldl (fun acc x => acc + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by
    simp only [List.foldl_cons, foldl_add_eq f l, List.map_cons, List.sum_cons]; ring

lemma list_sum_range (f : ℕ → ℤ) : ∀ n, ((List.range n).map f).sum = ∑ x ∈ range n, f x
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, sum_range_succ]
    simp

lemma sum_range_zmod {q : ℕ} [NeZero q] (f : ZMod q → ℤ) :
    ∑ x ∈ range q, f (x : ZMod q) = ∑ x : ZMod q, f x := by
  refine sum_nbij' (fun x => (x : ZMod q)) (fun z => z.val) (by simp) (by simp [ZMod.val_lt])
    (fun x hx => ZMod.val_cast_of_lt (mem_range.mp hx)) (fun z _ => ZMod.natCast_zmod_val z)
    (fun _ _ => rfl)

variable {q : ℕ} [hq : Fact q.Prime]

/-- The checker's three-way test on `euler a q` is the quadratic character of `a`. -/
lemma euler_eq_char (hq2 : q ≠ 2) (hq64 : q < 2 ^ 64) (a : ℕ) :
    (if euler a q = 1 then 1 else if euler a q = 0 then 0 else -1 : ℤ) =
      quadraticChar (ZMod q) a := by
  have h2 : 2 ≤ q := hq.out.two_le
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (hq.out.odd_of_ne_two hq2)
  have hlt : euler a q < q := powMod_lt (by omega) _ _
  have hcast : (euler a q : ZMod q) = ((quadraticChar (ZMod q) a : ℤ) : ZMod q) := by
    rw [quadraticChar_eq_pow_of_char_ne_two' (by rw [ZMod.ringChar_zmod_n]; exact hq2), ZMod.card,
      euler, powMod_cast _ _ _ (by omega), show (q - 1) / 2 = q / 2 by omega]
  have h1ne : (1 : ZMod q) ≠ -1 := by
    intro h
    have h0 : ((2 : ℕ) : ZMod q) = 0 := by push_cast; linear_combination h
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 q).mp h0)
    omega
  rcases quadraticChar_isQuadratic (ZMod q) (a : ZMod q) with h | h | h
  · rw [h] at hcast ⊢
    have : euler a q = 0 := (natCast_eq_zero_of_lt hlt).mp (by simpa using hcast)
    simp [this]
  · rw [h] at hcast ⊢
    have : euler a q = 1 := (natCast_inj_of_lt hlt (by omega)).mp (by simpa using hcast)
    simp [this]
  · rw [h] at hcast ⊢
    have hne1 : euler a q ≠ 1 := by
      intro he; rw [he] at hcast; exact h1ne (by simpa using hcast)
    have hne0 : euler a q ≠ 0 := by
      intro he; rw [he] at hcast; simp at hcast
    simp [hne1, hne0]

namespace Curve

variable (E : Curve) (q : ℕ)

lemma rhs_cast (x : ℕ) : (E.rhs q x : ZMod q) =
    (x : ZMod q) ^ 3 + E.a2 * (x : ZMod q) ^ 2 + E.a4 * x + E.a6 := by
  simp only [rhs, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]; ring

lemma order_eq_sum [Fact q.Prime] (hq2 : q ≠ 2) (hq64 : q < 2 ^ 64) :
    E.order q = q + 1 + ∑ x : ZMod q,
      (quadraticChar (ZMod q) (x ^ 3 + E.a2 * x ^ 2 + E.a4 * x + E.a6) : ℤ) := by
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hfun : (fun acc x => let e := euler (E.rhs q x) q
      if e = 1 then acc + 1 else if e = 0 then acc else acc - 1) =
      fun (acc : ℤ) (x : ℕ) => acc + (if euler (E.rhs q x) q = 1 then 1
        else if euler (E.rhs q x) q = 0 then 0 else -1 : ℤ) := by
    funext acc x; simp only; split_ifs <;> ring
  rw [order, hfun, foldl_add_eq, list_sum_range, ← sum_range_zmod]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [euler_eq_char hq2 hq64, rhs_cast]

/-- Points are the point at infinity or a nonsingular affine pair (`WithZero` is `Option`). -/
def pointEquivOption :
    (E.W q).Point ≃ Option {xy : ZMod q × ZMod q // (E.W q).Nonsingular xy.1 xy.2} :=
  (E.W q).nonsingularPointEquiv

instance [Fact q.Prime] : Finite (E.W q).Point :=
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  Finite.of_equiv _ (E.pointEquivOption q).symm

/-- `Curve.order` is the number of points. -/
theorem card_eq_order [Fact q.Prime] (hq2 : q ≠ 2) (hq64 : q < 2 ^ 64) (hΔ : (E.W q).Δ ≠ 0) :
    (Nat.card (E.W q).Point : ℤ) = E.order q := by
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  classical
  have hchar : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq2
  set g : ZMod q → ZMod q := fun x => x ^ 3 + E.a2 * x ^ 2 + E.a4 * x + E.a6 with hg
  -- points = affine solutions of y² = g(x), plus infinity
  have hpts : Nat.card (E.W q).Point =
      (univ.filter fun xy : ZMod q × ZMod q => xy.2 ^ 2 = g xy.1).card + 1 := by
    rw [Nat.card_congr (E.pointEquivOption q), Nat.card_eq_fintype_card, Fintype.card_option,
      Fintype.card_subtype]
    congr 2
    ext xy
    simp only [mem_filter, mem_univ, true_and, hg]
    rw [← equation_iff_nonsingular_of_Δ_ne_zero hΔ, equation_iff]
    simp [W]
  -- split by `x`, and count square roots
  have hsplit : ((univ.filter fun xy : ZMod q × ZMod q => xy.2 ^ 2 = g xy.1).card : ℤ) =
      ∑ x : ZMod q, ((quadraticChar (ZMod q) (g x) : ℤ) + 1) := by
    rw [card_filter, Fintype.sum_prod_type]
    push_cast
    refine sum_congr rfl fun x _ => ?_
    rw [← quadraticChar_card_sqrts hchar (g x), Set.toFinset_ofPred, card_filter]
    push_cast; rfl
  rw [hpts, Nat.cast_add, hsplit, order_eq_sum E q hq2 hq64, sum_add_distrib]
  simp [ZMod.card, hg]
  ring

end Curve

end Fermat433.Sieve
