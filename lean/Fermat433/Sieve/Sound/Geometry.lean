/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Sieve.Sound.Poly
import Fermat433.Sieve.Sound.Curve

/-!
# Soundness of the checker, part 4b: the curve `X` and the maps `φ₁, φ₂`

Over `𝔽_q`, a point of `X : y² = f(x)` (`f` a sextic) is affine or at infinity (`XPt`). The Möbius
change of variable `X = (x − x₊)/(x − x₋)`, `Y = y(X − 1)³` sends it to the even model
`Y² = F(X) = AX⁶ + BX⁴ + CX² + D`, or to the point over `X = ∞` when `x = x₋`
(`toEv`, `toEv_valid`).
The quotient maps are `φ₁(X, Y) = (AX², AY)` and `φ₂(X, Y) = (D/X², DY/X³)` (`Im1`, `Im2`); their
values are points of `E₁, E₂` (`exists_im1`, `exists_im2`).

Everything is stated for `S = setting I q r` under `settingOk`, the structural facts the checker
verifies at run time.
-/

namespace Fermat433.Sieve

open WeierstrassCurve WeierstrassCurve.Affine Finset

/-- The sextic `f(x) = Σₖ fₖ xᵏ` over `ZMod q`. -/
def fZ (f : List ℤ) (q : ℕ) (x : ZMod q) : ZMod q := ∑ k ∈ range 7, (f.getD k 0 : ZMod q) * x ^ k

/-- A rational number `num/den` in `ZMod q`. -/
def ratZ {q : ℕ} (z : ℤ × ℕ) : ZMod q := (z.1 : ZMod q) * (z.2 : ZMod q)⁻¹

/-- A point of `X : y² = f(x)` over `𝔽_q`: affine, or at infinity with `y/x³ → s`. -/
inductive XPt (q : ℕ)
  | aff (x y : ZMod q)
  | infty (s : ZMod q)

def XPt.Valid {q : ℕ} (f : List ℤ) : XPt q → Prop
  | .aff x y => y ^ 2 = fZ f q x
  | .infty s => s ^ 2 = (f.getD 6 0 : ZMod q)

/-- A generator, a point of `X` with rational coordinates. -/
def XPt.ofRat {q : ℕ} (p : (ℤ × ℕ) × (ℤ × ℕ)) : XPt q := .aff (ratZ p.1) (ratZ p.2)

/-- A point of the even model, or the point over `X = ∞` (where `x = x₋`), which keeps `y`. -/
inductive EvPt (q : ℕ)
  | fin (X Y : ZMod q)
  | inf (y : ZMod q)

lemma f_cast {q : ℕ} (hq : 0 < q) {f : List ℤ} (hf : f.length = 7) (x : ℕ) :
    (evalPoly (f.map (ofInt · q)) x q : ZMod q) = fZ f q x := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, rfl⟩ := list7 hf
  rw [evalPoly_cast]
  simp [fZ, evZ, ofInt_cast _ hq, sum_range_succ]
  ring

lemma ratMod_cast {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hq64 : q < 2 ^ 64) (z : ℤ × ℕ) :
    (ratMod z q : ZMod q) = ratZ z := by
  have h0 : 0 < q := (Fact.out : q.Prime).pos
  rw [ratMod, ZMod.natCast_mod, Nat.cast_mul, ofInt_cast _ h0, inv_cast hq2 _ hq64,
    ZMod.natCast_mod, ratZ]

variable (I : Inputs) (q r : ℕ)

/-- Abbreviations for the setting's values in `ZMod q`. -/
structure Vals where
  xp : ZMod q
  xm : ZMod q
  A : ZMod q
  B : ZMod q
  C : ZMod q
  D : ZMod q

def vals : Vals q :=
  let S := setting I q r
  ⟨S.xp, S.xm, S.A, S.F.getD 4 0, S.F.getD 2 0, S.D⟩

lemma setting_F : (setting I q r).F =
    evenModel I.f (evalL I.xp r q) (evalL I.xm r q) q := by simp only [setting]
lemma setting_f : (setting I q r).f = I.f.map (ofInt · q) := by simp only [setting]
lemma setting_p1 : (setting I q r).p1 = (ratMod I.p1.1 q, ratMod I.p1.2 q) := by
  simp only [setting]
lemma setting_p2 : (setting I q r).p2 = (ratMod I.p2.1 q, ratMod I.p2.2 q) := by
  simp only [setting]
lemma setting_xp : (setting I q r).xp = evalL I.xp r q := by simp only [setting]
lemma setting_xm : (setting I q r).xm = evalL I.xm r q := by simp only [setting]
lemma setting_A : (setting I q r).A = (setting I q r).F.getD 6 0 := by simp only [setting]
lemma setting_D : (setting I q r).D = (setting I q r).F.getD 0 0 := by simp only [setting]
lemma setting_q : (setting I q r).q = q := by simp only [setting]

variable {I q r}

/-- The facts `settingOk` checks. -/
structure SettingFacts : Prop where
  flen : I.f.length = 7
  len : (setting I q r).F.length ≤ 7
  c1 : (setting I q r).F.getD 1 0 = 0
  c3 : (setting I q r).F.getD 3 0 = 0
  c5 : (setting I q r).F.getD 5 0 = 0
  A_eq : (setting I q r).A = evalPoly (I.f.map (ofInt · q)) (setting I q r).xm q
  D_eq : (setting I q r).D = evalPoly (I.f.map (ofInt · q)) (setting I q r).xp q
  xp_lt : (setting I q r).xp < q
  xm_lt : (setting I q r).xm < q
  A_lt : (setting I q r).A < q
  D_lt : (setting I q r).D < q
  a2_1 : (setting I q r).E1.a2 < q
  a2_2 : (setting I q r).E2.a2 < q

lemma settingFacts_of_ok (hf : I.f.length = 7)
    (h : settingOk (setting I q r) (setting I q r).f = true) :
    SettingFacts (I := I) (q := q) (r := r) := by
  rw [setting_f] at h
  simp only [settingOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  simp only [setting_q] at h7 h8 h9 h10 h11 h12
  exact ⟨hf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

variable (hS : SettingFacts (I := I) (q := q) (r := r)) (hq : 0 < q)
include hS

/-- `F` is the even sextic `AX⁶ + BX⁴ + CX² + D`. -/
lemma evZ_F_even (X : ZMod q) : evZ (setting I q r).F X =
    (vals I q r).A * X ^ 6 + (vals I q r).B * X ^ 4 + (vals I q r).C * X ^ 2 + (vals I q r).D := by
  rw [evZ_eq_sum7 X _ hS.len]
  simp only [sum_range_succ, sum_range_zero, hS.c1, hS.c3, hS.c5, vals, setting_A, setting_D]
  push_cast; ring

include hq

/-- `F(X) = Σₖ fₖ (x₋X − x₊)ᵏ (X − 1)⁶⁻ᵏ`. -/
lemma evZ_F_model (X : ZMod q) : evZ (setting I q r).F X = ∑ k ∈ range 7,
    (I.f.getD k 0 : ZMod q) * ((vals I q r).xm * X - (vals I q r).xp) ^ k * (X - 1) ^ (6 - k) := by
  have hxp := hS.xp_lt
  rw [setting_xp] at hxp
  rw [setting_F, evZ_evenModel hq hS.flen _ _ hxp]
  simp only [vals, setting_xp, setting_xm]

lemma A_eq_f : (vals I q r).A = fZ I.f q (vals I q r).xm := by
  simp only [vals]; rw [hS.A_eq, f_cast hq hS.flen]

lemma D_eq_f : (vals I q r).D = fZ I.f q (vals I q r).xp := by
  simp only [vals]; rw [hS.D_eq, f_cast hq hS.flen]

omit hS hq in
/-- The Möbius change of variable to the even model. -/
def toEv [Fact q.Prime] (V : Vals q) : XPt q → EvPt q
  | .aff x y => if x = V.xm then .inf y else
      .fin ((x - V.xp) / (x - V.xm)) (y * ((x - V.xp) / (x - V.xm) - 1) ^ 3)
  | .infty s => .fin 1 (s * (V.xm - V.xp) ^ 3)

omit hS hq in
def EvPt.Valid (V : Vals q) : EvPt q → Prop
  | .fin X Y => Y ^ 2 = V.A * X ^ 6 + V.B * X ^ 4 + V.C * X ^ 2 + V.D
  | .inf y => y ^ 2 = V.A

/-- Points of `X` go to points of the even model. -/
theorem toEv_valid [Fact q.Prime] (P : XPt q)
    (hP : P.Valid I.f) : (toEv (vals I q r) P).Valid (vals I q r) := by
  cases P with
  | aff x y =>
    simp only [XPt.Valid] at hP
    simp only [toEv]
    split_ifs with hx
    · simp only [EvPt.Valid]; rw [hP, hx, ← A_eq_f hS hq]
    · simp only [EvPt.Valid]
      have hxm : x - (vals I q r).xm ≠ 0 := sub_ne_zero.mpr hx
      set X := (x - (vals I q r).xp) / (x - (vals I q r).xm) with hX
      have hX1 : X - 1 = ((vals I q r).xm - (vals I q r).xp) / (x - (vals I q r).xm) := by
        rw [hX]; field_simp; ring
      have hlin : (vals I q r).xm * X - (vals I q r).xp = x * (X - 1) := by
        rw [hX1, hX]; field_simp; ring
      rw [← evZ_F_even hS, evZ_F_model hS hq, hlin, mul_pow, hP]
      simp only [fZ, sum_range_succ, sum_range_zero, mul_pow]
      ring
  | infty s =>
    simp only [XPt.Valid] at hP
    simp only [toEv, EvPt.Valid]
    rw [← evZ_F_even hS, evZ_F_model hS hq, mul_pow, hP]
    simp only [sum_range_succ, sum_range_zero, sub_self, mul_one]
    simp only [zero_add, pow_zero, mul_one, Nat.sub_self]
    ring

omit hS hq

/-! ### The quotient maps -/

lemma E1_W : (setting I q r).E1.W q = ⟨0, (vals I q r).B, 0, (vals I q r).A * (vals I q r).C,
    (vals I q r).A * (vals I q r).A * (vals I q r).D⟩ := by
  simp only [Curve.W, setting, vals, ZMod.natCast_mod, Nat.cast_mul]

lemma E2_W : (setting I q r).E2.W q = ⟨0, (vals I q r).C, 0, (vals I q r).B * (vals I q r).D,
    (vals I q r).A * (vals I q r).D * (vals I q r).D⟩ := by
  simp only [Curve.W, setting, vals, ZMod.natCast_mod, Nat.cast_mul]

variable [Fact q.Prime]

/-- `φ₁ : (X, Y) ↦ (AX², AY)`, and the point over `X = ∞` goes to `O`. -/
def Im1 : EvPt q → ((setting I q r).E1.W q).Point → Prop
  | .fin X Y, Q => ∃ h, Q = .some ((vals I q r).A * X ^ 2) ((vals I q r).A * Y) h
  | .inf _, Q => Q = 0

/-- `φ₂ : (X, Y) ↦ (D/X², DY/X³)`, `O` at `X = 0`, and `(0, Dy)` over `X = ∞`. -/
def Im2 : EvPt q → ((setting I q r).E2.W q).Point → Prop
  | .fin X Y, Q => if X = 0 then Q = 0 else
      ∃ h, Q = .some ((vals I q r).D / X ^ 2) ((vals I q r).D * Y / X ^ 3) h
  | .inf y, Q => ∃ h, Q = .some 0 ((vals I q r).D * y) h

/-- `φ₁` of a point of the even model is a point of `E₁`. -/
theorem exists_im1 (hΔ : ((setting I q r).E1.W q).Δ ≠ 0) (P : EvPt q)
    (hP : P.Valid (vals I q r)) : ∃ Q, Im1 (I := I) (r := r) P Q := by
  cases P with
  | inf y => exact ⟨0, rfl⟩
  | fin X Y =>
    simp only [EvPt.Valid] at hP
    have heq : ((setting I q r).E1.W q).Equation ((vals I q r).A * X ^ 2) ((vals I q r).A * Y) := by
      rw [equation_iff, E1_W]
      linear_combination (vals I q r).A ^ 2 * hP
    exact ⟨_, (equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp heq, rfl⟩

/-- `φ₂` of a point of the even model is a point of `E₂`. -/
theorem exists_im2 (hΔ : ((setting I q r).E2.W q).Δ ≠ 0) (P : EvPt q)
    (hP : P.Valid (vals I q r)) : ∃ Q, Im2 (I := I) (r := r) P Q := by
  cases P with
  | inf y =>
    simp only [EvPt.Valid] at hP
    have heq : ((setting I q r).E2.W q).Equation 0 ((vals I q r).D * y) := by
      rw [equation_iff, E2_W]
      linear_combination (vals I q r).D ^ 2 * hP
    exact ⟨_, (equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp heq, rfl⟩
  | fin X Y =>
    simp only [EvPt.Valid] at hP
    by_cases hX : X = 0
    · exact ⟨0, by simp [Im2, hX]⟩
    · have heq : ((setting I q r).E2.W q).Equation ((vals I q r).D / X ^ 2)
          ((vals I q r).D * Y / X ^ 3) := by
        rw [equation_iff, E2_W]
        field_simp
        linear_combination (vals I q r).D ^ 2 * hP
      exact ⟨_, by
        simp only [Im2, hX, ↓reduceIte]
        exact ⟨(equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp heq, rfl⟩⟩

end Fermat433.Sieve
