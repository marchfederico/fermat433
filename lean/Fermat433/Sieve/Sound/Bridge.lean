/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Sieve.Sound.Geometry
import Fermat433.Sieve.Sound.Count
import Fermat433.Sieve.Sound.Fibre

/-!
# Soundness of the checker, part 4c: the checker's maps and fibre test

* `phi_rep`: the checker's `phi S x y` represents `φ₁, φ₂` of the point `(x, y)` of `X`.
* `fibreOk_sound`: if `fibreOk` accepts a point `Q` of the fibre, no point of `X(𝔽_q)` with
  `φ₁ = Q` has `c₂·φ₂` equal to the target.
-/

namespace Fermat433.Sieve

open WeierstrassCurve WeierstrassCurve.Affine

lemma Curve.rep_pt (E : Curve) (q : ℕ) {x y : ℕ} (hx : x < q) (hy : y < q) {X Y : ZMod q}
    (h : (E.W q).Nonsingular X Y) (hX : (x : ZMod q) = X) (hY : (y : ZMod q) = Y) :
    E.Rep q (.pt x y) (.some X Y h) := by
  subst hX hY; exact ⟨hx, hy, h, rfl⟩

variable {I : Inputs} {q r : ℕ} [hqp : Fact q.Prime]

local notation "S" => setting I q r
local notation "V" => vals I q r

lemma vals_xp : (V).xp = ((S).xp : ZMod q) := rfl
lemma vals_xm : (V).xm = ((S).xm : ZMod q) := rfl
lemma vals_A : (V).A = ((S).A : ZMod q) := rfl
lemma vals_D : (V).D = ((S).D : ZMod q) := rfl
omit hqp in
lemma setting_q' : (S).q = q := setting_q I q r

lemma natCast_ne_of_lt {a b : ℕ} (ha : a < q) (hb : b < q) (h : a ≠ b) : (a : ZMod q) ≠ b :=
  fun h' => h ((natCast_inj_of_lt ha hb).mp h')

lemma phi_rep (hS : SettingFacts (I := I) (q := q) (r := r)) (hq2 : q ≠ 2) (hq64 : q < 2 ^ 64)
    {x y : ℕ} (hx : x < q) (_hy : y < q) {Q1 : ((S).E1.W q).Point} {Q2 : ((S).E2.W q).Point}
    (h1 : Im1 (I := I) (r := r) (toEv V (.aff x y)) Q1)
    (h2 : Im2 (I := I) (r := r) (toEv V (.aff x y)) Q2) :
    (S).E1.Rep q (phi S x y).1 Q1 ∧ (S).E2.Rep q (phi S x y).2 Q2 := by
  have h0 : 0 < q := hqp.out.pos
  have hxp := hS.xp_lt
  have hxm := hS.xm_lt
  have hA := hS.A_lt
  have hD := hS.D_lt
  simp only [phi, setting_q']
  simp only [toEv, vals_xm, vals_xp] at h1 h2
  by_cases hxe : x = (S).xm
  · -- `x = x₋`: the point over `X = ∞`
    subst hxe
    simp only [↓reduceIte] at h1 h2 ⊢
    refine ⟨h1, ?_⟩
    obtain ⟨h, rfl⟩ := h2
    exact Curve.rep_pt _ q h0 (Nat.mod_lt _ h0) h (by simp)
      (by rw [ZMod.natCast_mod, Nat.cast_mul, vals_D])
  · have hxe' : (x : ZMod q) ≠ (S).xm := natCast_ne_of_lt hx hxm hxe
    have hden : (x : ZMod q) - (S).xm ≠ 0 := sub_ne_zero.mpr hxe'
    simp only [hxe, hxe', ↓reduceIte] at h1 h2 ⊢
    by_cases hxp' : x = (S).xp
    · -- `x = x₊`: `X = 0`
      subst hxp'
      simp only [↓reduceIte, sub_self, zero_div] at h1 h2 ⊢
      obtain ⟨h, rfl⟩ := h1
      refine ⟨Curve.rep_pt _ q h0 (sub_lt h0 _ _) h (by simp) ?_,
        by simpa [Im2, Curve.Rep] using h2⟩
      rw [sub_cast h0, ZMod.natCast_mod, Nat.cast_mul, vals_A]; ring
    · have hxp'' : (x : ZMod q) ≠ (S).xp := natCast_ne_of_lt hx hxp hxp'
      simp only [hxp', ↓reduceIte]
      set X : ZMod q := ((x : ZMod q) - (S).xp) / ((x : ZMod q) - (S).xm) with hX
      have hX0 : X ≠ 0 := div_ne_zero (sub_ne_zero.mpr hxp'') hden
      set Xn := sub x (S).xp q * inv (sub x (S).xm q) q % q with hXn
      have hXn : (Xn : ZMod q) = X := by
        rw [hXn, ZMod.natCast_mod, Nat.cast_mul, sub_cast h0, inv_cast hq2 _ hq64, sub_cast h0,
          hX, div_eq_mul_inv]
      have hXnlt : Xn < q := Nat.mod_lt _ h0
      set Yn := y * powMod (sub Xn 1 q) 3 q % q with hYn
      have hYn : (Yn : ZMod q) = y * (X - 1) ^ 3 := by
        rw [hYn, ZMod.natCast_mod, Nat.cast_mul, powMod_cast _ _ _ (by norm_num), sub_cast h0,
          hXn, Nat.cast_one]
      obtain ⟨g1, rfl⟩ := h1
      simp only [Im2, hX0, ↓reduceIte] at h2
      obtain ⟨g2, rfl⟩ := h2
      refine ⟨Curve.rep_pt _ q (Nat.mod_lt _ h0) (Nat.mod_lt _ h0) g1 ?_ ?_,
        Curve.rep_pt _ q (Nat.mod_lt _ h0) (Nat.mod_lt _ h0) g2 ?_ ?_⟩
      · simp only [ZMod.natCast_mod, Nat.cast_mul, hXn, vals_A]; ring
      · rw [ZMod.natCast_mod, Nat.cast_mul, hYn, vals_A]
      · rw [ZMod.natCast_mod, Nat.cast_mul, inv_cast hq2 _ hq64, ZMod.natCast_mod, Nat.cast_mul,
          hXn, vals_D, div_eq_mul_inv, sq]
      · rw [ZMod.natCast_mod, Nat.cast_mul, inv_cast hq2 _ hq64, powMod_cast _ _ _ (by norm_num),
          ZMod.natCast_mod, Nat.cast_mul, hXn, hYn, vals_D, div_eq_mul_inv]

/-- A `hit` test that fails rules out the corresponding Mathlib point. -/
lemma not_hit {E : Curve} (ha2 : E.a2 < q) (hq2 : q ≠ 2) (hq64 : q < 2 ^ 64) {c : ℕ}
    (hc : c < 2 ^ 64) {P T : Pt} {P' T' : (E.W q).Point} (hP : E.Rep q P P') (hT : E.Rep q T T')
    (h : (!(E.mul q c P == T)) = true) : c • P' ≠ T' := by
  intro heq
  have hm := E.mul_rep q hq2 hq64 ha2 hc hP
  have := (E.rep_inj q hm hT).mpr heq
  simp [this] at h

/-- If the fibre test accepts `(Q, w)`, no point over `Q` reaches `T₂`. -/
theorem fibreOk_sound (hS : SettingFacts (I := I) (q := q) (r := r)) (hq2 : q ≠ 2)
    (hq64 : q < 2 ^ 64) (hA0 : (S).A ≠ 0) {c2 : ℕ} (hc2 : c2 < 2 ^ 64) {T2 : Pt}
    {T2' : ((S).E2.W q).Point} (hT : (S).E2.Rep q T2 T2') {Q : Pt} {w : ℕ} (hw : w ≤ q)
    (hok : fibreOk S (fq q) c2 T2 Q w = true) {Q1 : ((S).E1.W q).Point} (hQ : (S).E1.Rep q Q Q1)
    {P : EvPt q} (hP : P.Valid V) (h1 : Im1 (I := I) (r := r) P Q1)
    {Q2 : ((S).E2.W q).Point} (h2 : Im2 (I := I) (r := r) P Q2) : c2 • Q2 ≠ T2' := by
  have h0 : 0 < q := hqp.out.pos
  have hA := hS.A_lt
  have hD := hS.D_lt
  have ha2 := hS.a2_2
  have hAz : (V).A ≠ 0 := by
    have := natCast_ne_of_lt hA h0 hA0; rwa [Nat.cast_zero, ← vals_A] at this
  have hq' : (S).q = q := setting_q' (I := I) (r := r)
  cases P with
  | inf y =>
    simp only [EvPt.Valid] at hP
    have hQ1 : Q1 = 0 := h1
    obtain ⟨g, rfl⟩ := h2
    cases Q with
    | pt u v => obtain ⟨-, -, h, rfl⟩ := hQ; exact absurd hQ1 (Point.some_ne_zero h)
    | inf =>
      have hfx : (evalPoly (fq q) (S).xm q : ZMod q) = (V).A := by
        rw [fq, f_cast h0, A_eq_f hS h0, vals_xm]
      simp only [fibreOk, hq'] at hok
      split_ifs at hok with hwq
      · simp only [beq_iff_eq] at hok
        exact absurd ⟨y, by rw [← hfx] at hP; rw [hP.symm.trans (sq y)]⟩
          (not_isSquare_of_euler hq2 hq64 _ hok)
      · simp only [Bool.and_eq_true, beq_iff_eq] at hok
        obtain ⟨⟨hsq, hit1⟩, hit2⟩ := hok
        have hwlt : w < q := lt_of_le_of_ne hw hwq
        have hw2 : (w : ZMod q) ^ 2 = y ^ 2 := by
          rw [hP, ← hfx, ← hsq, ZMod.natCast_mod, Nat.cast_mul, sq]
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hw2.symm with hy | hy
        · refine not_hit ha2 hq2 hq64 hc2 (Curve.rep_pt _ q h0 (Nat.mod_lt _ h0) g (by simp) ?_)
            hT hit1
          rw [ZMod.natCast_mod, Nat.cast_mul, hy, vals_D]
        · refine not_hit ha2 hq2 hq64 hc2 (Curve.rep_pt _ q h0 (sub_lt h0 _ _) g (by simp) ?_)
            hT hit2
          rw [sub_cast h0, ZMod.natCast_mod, Nat.cast_mul, hy, vals_D]; push_cast; ring
  | fin X Y =>
    simp only [EvPt.Valid] at hP
    obtain ⟨g1, rfl⟩ := h1
    cases Q with
    | inf => exact absurd hQ (Point.some_ne_zero g1)
    | pt u v =>
      obtain ⟨hu, hv, h, heq⟩ := hQ
      simp only [Point.some.injEq] at heq
      obtain ⟨hAu, hAv⟩ := heq
      have hs : ((u * inv (S).A q % q : ℕ) : ZMod q) = X ^ 2 := by
        rw [ZMod.natCast_mod, Nat.cast_mul, inv_cast hq2 _ hq64, ← hAu, ← vals_A]
        field_simp
      have hY : ((v * inv (S).A q % q : ℕ) : ZMod q) = Y := by
        rw [ZMod.natCast_mod, Nat.cast_mul, inv_cast hq2 _ hq64, ← hAv, ← vals_A]
        field_simp
      -- the image of `(±X, Y)` under the checker's `img`
      have himg : ∀ Xn, Xn < q → (Xn : ZMod q) = X → (S).E2.Rep q
          (if Xn = 0 then Pt.inf else Pt.pt ((S).D * inv (Xn * Xn % q) q % q)
            ((S).D * (v * inv (S).A q % q) % q * inv (powMod Xn 3 q) q % q)) Q2 := by
        intro Xn hXn hXX
        by_cases hX0 : Xn = 0
        · have : X = 0 := by rw [← hXX, hX0, Nat.cast_zero]
          simp only [hX0, ↓reduceIte]
          simpa [Im2, this, Curve.Rep] using h2
        · have hXz : X ≠ 0 := by
            have := natCast_ne_of_lt hXn h0 hX0; rwa [Nat.cast_zero, hXX] at this
          simp only [Im2, hXz, ↓reduceIte] at h2
          obtain ⟨g2, rfl⟩ := h2
          simp only [hX0, ↓reduceIte]
          refine Curve.rep_pt _ q (Nat.mod_lt _ h0) (Nat.mod_lt _ h0) g2 ?_ ?_
          · rw [ZMod.natCast_mod, Nat.cast_mul, inv_cast hq2 _ hq64, ZMod.natCast_mod,
              Nat.cast_mul, hXX, vals_D, div_eq_mul_inv, sq]
          · rw [ZMod.natCast_mod, Nat.cast_mul, inv_cast hq2 _ hq64,
              powMod_cast _ _ _ (by norm_num), ZMod.natCast_mod, Nat.cast_mul, hXX, hY, vals_D,
              div_eq_mul_inv]
      dsimp only [fibreOk] at hok
      rw [hq'] at hok
      by_cases hwq : w = q
      · simp only [hwq, ↓reduceIte] at hok
        exact ((not_isSquare_of_euler hq2 hq64 _ (beq_iff_eq.mp hok)) ⟨X, by rw [hs, sq]⟩).elim
      · simp only [hwq, ↓reduceIte] at hok
        rw [Bool.and_eq_true, Bool.and_eq_true] at hok
        obtain ⟨⟨hsq, hit1⟩, hit2⟩ := hok
        have hsq := beq_iff_eq.mp hsq
        have hwlt : w < q := lt_of_le_of_ne hw hwq
        have hw2 : (w : ZMod q) ^ 2 = X ^ 2 := by
          rw [← hs, ← hsq, ZMod.natCast_mod, Nat.cast_mul, sq]
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hw2.symm with hX | hX
        · exact not_hit ha2 hq2 hq64 hc2 (himg w hwlt hX.symm) hT hit1
        · refine not_hit ha2 hq2 hq64 hc2 (himg ((q - w) % q) (Nat.mod_lt _ h0) ?_) hT hit2
          rw [ZMod.natCast_mod, Nat.cast_sub hw, ZMod.natCast_self, zero_sub, hX]

end Fermat433.Sieve
