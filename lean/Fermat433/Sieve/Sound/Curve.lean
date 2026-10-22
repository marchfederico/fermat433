/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Sieve.Sound.Arith

/-!
# Soundness of the checker, part 2: the group law

The checker's curves `y² = x³ + a₂x² + a₄x + a₆` are Mathlib Weierstrass curves `Curve.W` over
`ZMod q` with `a₁ = a₃ = 0`. A checker point `P : Pt` *represents* a Mathlib point `P'` (`Rep`) when
it is `inf` and `P' = 0`, or `pt x y` with `x, y < q` and `P' = (x, y)`. The main results:

* `Curve.add_rep`: `Curve.add` represents Mathlib's addition;
* `Curve.mul_rep`: `Curve.mul n` represents `n • ·`;
* `Curve.rep_of_onCurve`: a reduced pair passing `onCurve` represents a point, when the
  discriminant is nonzero;
* `Curve.Δ_ne_zero`: the checker's `disc ≠ 0` implies `Δ ≠ 0`.
-/

namespace Fermat433.Sieve

open WeierstrassCurve WeierstrassCurve.Affine

lemma natCast_inj_of_lt {q a b : ℕ} (ha : a < q) (hb : b < q) :
    (a : ZMod q) = b ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

lemma natCast_eq_zero_of_lt {q a : ℕ} (ha : a < q) : (a : ZMod q) = 0 ↔ a = 0 := by
  have hq : 0 < q := by omega
  simpa using natCast_inj_of_lt (b := 0) ha hq

lemma point_some_congr {F : Type*} [Field F] {W : Affine F} {x y x' y' : F} (hx : x = x')
    (hy : y = y') (h : W.Nonsingular x y) (h' : W.Nonsingular x' y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx hy; rfl

namespace Curve

variable (E : Curve) (q : ℕ)

/-- The Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over `ZMod q`. -/
def W : Affine (ZMod q) := ⟨0, E.a2, 0, E.a4, E.a6⟩

/-- `P` represents `P'`. -/
def Rep : Pt → (E.W q).Point → Prop
  | .inf, P' => P' = 0
  | .pt x y, P' => x < q ∧ y < q ∧ ∃ h : (E.W q).Nonsingular x y, P' = .some _ _ h

lemma W_Δ : (E.W q).Δ = 16 * (-4 * E.a2 ^ 3 * E.a6 + E.a2 ^ 2 * E.a4 ^ 2 + 18 * E.a2 * E.a4 * E.a6
    - 4 * E.a4 ^ 3 - 27 * E.a6 ^ 2 : ZMod q) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, W]
  ring

lemma disc_cast (hq : 0 < q) : (E.disc q : ZMod q) = (-4 * E.a2 ^ 3 * E.a6 + E.a2 ^ 2 * E.a4 ^ 2
    + 18 * E.a2 * E.a4 * E.a6 - 4 * E.a4 ^ 3 - 27 * E.a6 ^ 2 : ZMod q) := by
  simp only [disc, sub_cast hq, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

lemma Δ_ne_zero [hq : Fact q.Prime] (hq2 : q ≠ 2) (h : E.disc q ≠ 0) : (E.W q).Δ ≠ 0 := by
  have h0 : 0 < q := hq.out.pos
  have hlt : E.disc q < q := sub_lt h0 _ _
  rw [W_Δ, ← disc_cast E q h0]
  refine mul_ne_zero ?_ ((natCast_eq_zero_of_lt hlt).not.mpr h)
  have h16 : ((16 : ℕ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have h2 := (Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).mp
      (hq.out.dvd_of_dvd_pow (show q ∣ 2 ^ 4 by simpa using hd))
    exact hq2 h2
  simpa using h16

lemma equation_iff_onCurve (x y : ℕ) :
    (E.W q).Equation x y ↔ (y * y % q : ZMod q) = (E.rhs q x : ZMod q) := by
  rw [equation_iff]
  simp only [rhs, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, W]
  constructor <;> intro h <;> linear_combination h

/-- A reduced pair that passes `onCurve` represents a point. -/
lemma rep_of_onCurve [hq : Fact q.Prime] (hq2 : q ≠ 2) (h : E.disc q ≠ 0) {x y : ℕ}
    (hx : x < q) (hy : y < q) (hon : E.onCurve q (.pt x y) = true) :
    ∃ P', E.Rep q (.pt x y) P' := by
  have h0 : 0 < q := hq.out.pos
  have heq : (E.W q).Equation x y := by
    rw [equation_iff_onCurve E q]
    simp only [onCurve, beq_iff_eq] at hon
    rw [hon]
  have hns := (equation_iff_nonsingular_of_Δ_ne_zero (E.Δ_ne_zero q hq2 h)).mp heq
  exact ⟨.some _ _ hns, hx, hy, hns, rfl⟩

lemma rep_lt {P : Pt} {P' : (E.W q).Point} (h : E.Rep q P P') :
    match P with | .inf => True | .pt x y => x < q ∧ y < q := by
  cases P with
  | inf => trivial
  | pt x y => exact ⟨h.1, h.2.1⟩

/-- `Curve.add` is the group law. -/
theorem add_rep [hq : Fact q.Prime] (hq2 : q ≠ 2) (hq64 : q < 2 ^ 64) (ha2 : E.a2 < q)
    {P Q : Pt} {P' Q' : (E.W q).Point} (hP : E.Rep q P P') (hQ : E.Rep q Q Q') :
    E.Rep q (E.add q P Q) (P' + Q') := by
  have h0 : 0 < q := hq.out.pos
  cases P with
  | inf =>
    have : P' = 0 := hP
    subst this; simpa [add] using hQ
  | pt x1 y1 =>
    cases Q with
    | inf =>
      have : Q' = 0 := hQ
      subst this; simpa [add] using hP
    | pt x2 y2 =>
      obtain ⟨hx1, hy1, h1, rfl⟩ := hP
      obtain ⟨hx2, hy2, h2, rfl⟩ := hQ
      have hxeq : (x1 : ZMod q) = x2 ↔ x1 = x2 := natCast_inj_of_lt hx1 hx2
      have hyneg : (y1 : ZMod q) = (E.W q).negY x2 y2 ↔ (y1 + y2) % q = 0 := by
        rw [Affine.negY, ← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
        simp only [W, zero_mul, sub_zero, Nat.cast_add]
        constructor <;> intro h <;> linear_combination h
      by_cases hc : x1 = x2 ∧ (y1 + y2) % q = 0
      · have : E.add q (.pt x1 y1) (.pt x2 y2) = .inf := by simp [add, hc]
        rw [this]
        exact Point.add_of_Y_eq (hxeq.mpr hc.1) (hyneg.mpr hc.2)
      · have hc' : ¬((x1 : ZMod q) = x2 ∧ (y1 : ZMod q) = (E.W q).negY x2 y2) := by
          rwa [hxeq, hyneg]
        rw [Point.add_some hc']
        -- the slope
        set ℓ := (E.W q).slope x1 x2 y1 y2 with hℓ
        set lam : ℕ := if x1 = x2 then (3 * x1 % q * x1 + 2 * E.a2 % q * x1 + E.a4) % q *
            inv (2 * y1 % q) q % q else sub y2 y1 q * inv (sub x2 x1 q) q % q
          with hlam
        have hlamq : (lam : ZMod q) = ℓ := by
          by_cases hx : x1 = x2
          · have hy : (y1 : ZMod q) ≠ (E.W q).negY x2 y2 := fun h => hc' ⟨hxeq.mpr hx, h⟩
            rw [hℓ, slope_of_Y_ne (hxeq.mpr hx) hy]
            simp only [hlam, hx, ↓reduceIte]
            simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, inv_cast hq2 _ hq64,
              Affine.negY, W]
            push_cast
            rw [div_eq_mul_inv]; ring_nf
          · rw [hℓ, slope_of_X_ne (fun h => hx (hxeq.mp h))]
            simp only [hlam, hx, ↓reduceIte]
            simp only [ZMod.natCast_mod, Nat.cast_mul, inv_cast hq2 _ hq64, sub_cast h0]
            rw [div_eq_mul_inv, ← neg_sub (x1 : ZMod q), inv_neg]; ring
        have hlt : lam < q := by rw [hlam]; split_ifs <;> exact Nat.mod_lt _ h0
        set x3 := (lam * lam % q + 3 * q - E.a2 - x1 - x2) % q with hx3
        have hx3q : (x3 : ZMod q) = (E.W q).addX x1 x2 ℓ := by
          rw [hx3, ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_sub (by omega),
            Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_mod, Nat.cast_mul, hlamq,
            Nat.cast_mul, ZMod.natCast_self]
          simp only [Affine.addX, W]; ring
        have hres : E.add q (.pt x1 y1) (.pt x2 y2) =
            .pt x3 (sub (lam * sub x1 x3 q % q) y1 q) := by
          simp only [add, hc, ↓reduceIte, hlam, hx3]
        have hy3q : ((sub (lam * sub x1 x3 q % q) y1 q : ℕ) : ZMod q) =
            (E.W q).addY x1 x2 y1 ℓ := by
          simp only [sub_cast h0, ZMod.natCast_mod, Nat.cast_mul, hlamq, hx3q]
          simp only [Affine.addY, Affine.negY, Affine.negAddY, W]; ring
        have hns := nonsingular_add h1 h2 hc'
        rw [hres]
        refine ⟨Nat.mod_lt _ h0, sub_lt h0 _ _, by rw [hx3q, hy3q]; exact hns,
          point_some_congr hx3q.symm hy3q.symm _ _⟩

lemma mulAux_rep [Fact q.Prime] (hq2 : q ≠ 2) (hq64 : q < 2 ^ 64) (ha2 : E.a2 < q) :
    ∀ (fuel n : ℕ) {P R : Pt} {P' R' : (E.W q).Point}, n < 2 ^ fuel → E.Rep q P P' → E.Rep q R R' →
      E.Rep q (E.mulAux q fuel n P R) (R' + n • P') := by
  intro fuel
  induction fuel with
  | zero =>
    intro n P R P' R' hn _ hR
    obtain rfl : n = 0 := by simpa using hn
    simpa [mulAux] using hR
  | succ k ih =>
    intro n P R P' R' hn hP hR
    unfold mulAux
    by_cases h0 : n = 0
    · subst h0; simpa using hR
    · simp only [h0, ↓reduceIte]
      have hn2 : n / 2 < 2 ^ k := by rw [pow_succ] at hn; omega
      have hPP := E.add_rep q hq2 hq64 ha2 hP hP
      have hhalf : (n / 2) • (P' + P') = (n / 2 * 2) • P' := by
        rw [← two_nsmul, smul_smul]
      split_ifs with hodd
      · have key : R' + n • P' = (R' + P') + (n / 2) • (P' + P') := by
          rw [hhalf, add_assoc]
          congr 1
          conv_lhs => rw [show n = 1 + n / 2 * 2 by omega]
          rw [add_nsmul, one_nsmul]
        rw [key]; exact ih (n / 2) hn2 hPP (E.add_rep q hq2 hq64 ha2 hR hP)
      · have key : R' + n • P' = R' + (n / 2) • (P' + P') := by
          rw [hhalf]; congr 2; omega
        rw [key]; exact ih (n / 2) hn2 hPP hR

/-- `Curve.mul n` is multiplication by `n`. -/
theorem mul_rep [Fact q.Prime] (hq2 : q ≠ 2) (hq64 : q < 2 ^ 64) (ha2 : E.a2 < q)
    {n : ℕ} (hn : n < 2 ^ 64) {P : Pt} {P' : (E.W q).Point} (hP : E.Rep q P P') :
    E.Rep q (E.mul q n P) (n • P') := by
  have := E.mulAux_rep q hq2 hq64 ha2 64 n (R := .inf) (R' := 0) hn hP rfl
  rwa [zero_add] at this

/-- Distinct representatives represent distinct points, and equal ones equal points. -/
lemma rep_inj {P Q : Pt} {P' Q' : (E.W q).Point} (hP : E.Rep q P P') (hQ : E.Rep q Q Q') :
    P = Q ↔ P' = Q' := by
  cases P with
  | inf =>
    cases Q with
    | inf => exact ⟨fun _ => hP.trans hQ.symm, fun _ => rfl⟩
    | pt x y =>
      obtain ⟨-, -, h, rfl⟩ := hQ
      have : P' = 0 := hP
      subst this
      simp
  | pt x1 y1 =>
    obtain ⟨hx1, hy1, h1, rfl⟩ := hP
    cases Q with
    | inf =>
      have : Q' = 0 := hQ
      subst this
      simp
    | pt x2 y2 =>
      obtain ⟨hx2, hy2, h2, rfl⟩ := hQ
      simp only [Pt.pt.injEq, Point.some.injEq, natCast_inj_of_lt hx1 hx2,
        natCast_inj_of_lt hy1 hy2]

end Curve

end Fermat433.Sieve
