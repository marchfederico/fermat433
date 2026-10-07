/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Lemmas

/-!
# Parts A and E: from a primitive solution to the six curves, and back

Throughout, `(x, y, z)` is a primitive solution, `z + yθ = −εᵏγ⁴` (Lemma A.1, an input), and
`δ = γ² = d₀ + d₁θ + d₂θ²`. Then `z + yθ = −εᵏδ²`, so `x² = N(δ)` and the `θ²`-coordinate of
`−εᵏδ²` vanishes: this is the conic `Q_k(δ) = 0` of Lemma A.3. The line through `(1 : 0 : 0)` and
`δ` has slope `X = d₁/d₂`, the `x`-coordinate of the point on the curve; `d₂ = 0` is the tangent
direction, handled directly.

* `descended`: `x² = N(δ)`, `δ` has no prime factor, `γ` is a unit at 2 (`a` odd), hence `d₀` odd.
* `not_k23`: `k = 2, 3` are impossible, since `C₂, C₃` have no points with `a` odd mod 2 (A.2).
* `case_k0`, `case_k1`: the twist set (A.3) and the recovery of `(x, y, z)` (E).
-/

open ZT

namespace Fermat433

variable {x y z : ℤ}

lemma _root_.Primitive.false_of_prime {p : ℤ} (h : Primitive x y z) (hp : Prime p)
    (hx : p ∣ x) (hy : p ∣ y) (hz : p ∣ z) : False :=
  hp.not_isUnit (h p hx hy hz)

/-- What Lemma A.1 gives, with `δ = γ²` in place of `γ`. -/
structure Descended (x y z : ℤ) (k : ℕ) (δ : ZT) : Prop where
  eq : (⟨z, y, 0⟩ : ZT) = -(ε ^ k * δ ^ 2)
  norm : x ^ 2 = N δ
  prim : ∀ p : ℤ, Prime p → DvdAll p δ → False
  odd : Odd δ.r0

lemma eq_sq_sq {k : ℕ} {γ : ZT} (hα : (⟨z, y, 0⟩ : ZT) = -(ε ^ k * γ ^ 4)) :
    (⟨z, y, 0⟩ : ZT) = -(ε ^ k * (γ ^ 2) ^ 2) := by
  rw [hα, ← pow_mul]

lemma sq_norm_eq (heq : x ^ 4 + 2 * y ^ 3 + z ^ 3 = 0) {k : ℕ} {γ : ZT}
    (hα : (⟨z, y, 0⟩ : ZT) = -(ε ^ k * γ ^ 4)) : x ^ 2 = N γ ^ 2 := by
  have h := congrArg N hα
  rw [N_neg, N_mul, N_pow, N_pow, N_ε, one_pow, one_mul,
    show N ⟨z, y, 0⟩ = z ^ 3 + 2 * y ^ 3 by simp [N]] at h
  have h4 : (x ^ 2) ^ 2 = (N γ ^ 2) ^ 2 := by linear_combination heq - h
  exact (pow_left_inj₀ (sq_nonneg _) (sq_nonneg _) two_ne_zero).mp h4

/-- Lemma A.2, first half: `γ` is a unit at 2, i.e. `a` is odd. If `a` were even then `γ = θγ'`,
`γ⁴ = θ⁴γ'⁴ = 2θγ'⁴` and `N(γ) = 2N(γ')`, so 2 would divide `x, y, z`. -/
lemma odd_r0 (heq : x ^ 4 + 2 * y ^ 3 + z ^ 3 = 0) (hp : Primitive x y z) {k : ℕ} {γ : ZT}
    (hα : (⟨z, y, 0⟩ : ZT) = -(ε ^ k * γ ^ 4)) : Odd γ.r0 := by
  have hx2 := sq_norm_eq heq hα
  by_contra hev
  obtain ⟨a', ha'⟩ := Int.not_odd_iff_even.mp hev
  set γ' : ZT := ⟨γ.r1, γ.r2, a'⟩
  have hγ : γ = θ * γ' := by ext <;> simp [θ, γ', ha']; ring
  have h2 : DvdAll 2 (-(ε ^ k * γ ^ 4)) := by
    rw [hγ, mul_pow, show θ ^ 4 = ⟨0, 2, 0⟩ by decide]
    exact ((DvdAll.mul_right ⟨dvd_zero 2, dvd_refl 2, dvd_zero 2⟩ _).mul_left _).neg
  rw [← hα] at h2
  have hNγ : N γ = 2 * N γ' := by rw [hγ, N_mul]; rfl
  exact hp.false_of_prime Int.prime_two
    (Int.prime_two.dvd_of_dvd_pow (n := 2) ⟨2 * N γ' ^ 2, by rw [hx2, hNγ]; ring⟩) h2.2.1 h2.1

lemma descended (heq : x ^ 4 + 2 * y ^ 3 + z ^ 3 = 0) (hp : Primitive x y z) {k : ℕ} {γ : ZT}
    (hα : (⟨z, y, 0⟩ : ZT) = -(ε ^ k * γ ^ 4)) : Descended x y z k (γ ^ 2) := by
  have hx2 := sq_norm_eq heq hα
  have hα' := eq_sq_sq hα
  have hodd := odd_r0 heq hp hα
  refine ⟨hα', by rw [hx2, N_pow], ?_, ?_⟩
  · intro p hpp hδ
    have h := ((hδ.mul_left (γ ^ 2)).mul_left (ε ^ k)).neg
    rw [← sq, ← hα'] at h
    have hpx : p ∣ x := hpp.dvd_of_dvd_pow (n := 2) (by rw [hx2, ← N_pow]; exact hδ.dvd_N)
    exact hp.false_of_prime hpp hpx h.2.1 h.1
  · obtain ⟨a', ha'⟩ := hodd
    exact ⟨2 * a' ^ 2 + 2 * a' + 2 * γ.r1 * γ.r2, by simp [sq_def, ha']; ring⟩

/-- Lemma A.2: for `k = 2, 3` the `θ²`-coordinate of `−εᵏγ⁴` is odd when `a` is odd. -/
lemma not_k23 {k : ℕ} (hk : k = 2 ∨ k = 3) {γ : ZT} (ha : Odd γ.r0)
    (hα : (⟨z, y, 0⟩ : ZT) = -(ε ^ k * γ ^ 4)) : False := by
  obtain ⟨a, b, c⟩ := γ
  obtain ⟨a', ha'⟩ := ha
  simp only at ha'
  subst ha'
  have h := congrArg ZT.r2 hα
  rcases hk with rfl | rfl <;>
  · simp only [pow_succ, pow_zero, one_mul, mul_r2, mul_r0, mul_r1, neg_r2, ε] at h
    have h2 := congrArg (Int.cast : ℤ → ZMod 2) h
    push_cast at h2
    generalize (a' : ZMod 2) = A at h2
    generalize (b : ZMod 2) = B at h2
    generalize (c : ZMod 2) = C at h2
    revert A B C h2
    decide

/-- A point `(d₁/d₂, W)` on `y² = μF(x)` from `F(d₁/d₂)d₂⁶ = λ³x²` and `λ = μq²`. -/
lemma twist_point {F : ℚ → ℚ} {d1 d2 x lam μ q : ℚ} (hd2 : d2 ≠ 0)
    (hF : F (d1 / d2) * d2 ^ 6 = lam ^ 3 * x ^ 2) (hlam : lam = μ * q ^ 2) :
    (μ ^ 2 * q ^ 3 * x / d2 ^ 3) ^ 2 = μ * F (d1 / d2) := by
  rw [eq_div_of_mul_eq (pow_ne_zero 6 hd2) hF, hlam]
  field_simp

lemma ratio_eq {d1 d2 : ℤ} (hd2 : d2 ≠ 0) {r s : ℤ} (hs : s ≠ 0)
    (h : (d1 : ℚ) / d2 = r / s) : s * d1 = r * d2 := by
  have hd2' : (d2 : ℚ) ≠ 0 := by exact_mod_cast hd2
  have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast hs
  rw [div_eq_div_iff hd2' hs'] at h
  exact_mod_cast (by linarith : (s : ℚ) * d1 = r * d2)

lemma sq_eq_one {x : ℤ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h | h
  · left; linarith
  · right; linarith

/-- `k = 0`: the conic is `d₁² + 2d₀d₂ = 0` and the curves are `A± : y² = ±(x⁶ − 40x³ − 32)`. -/
lemma case_k0 (H : Inputs) (hp : Primitive x y z) {δ : ZT} (D : Descended x y z 0 δ) :
    (x, y, z) ∈ solutions := by
  obtain ⟨d0, d1, d2⟩ := δ
  obtain ⟨heq, hN, hprim, hodd⟩ := D
  simp only [pow_zero, one_mul] at heq
  have hz : z = -d0 ^ 2 - 4 * d1 * d2 := by
    have := congrArg ZT.r0 heq; simp [sq_def] at this; linear_combination this
  have hy : y = -2 * d0 * d1 - 2 * d2 ^ 2 := by
    have := congrArg ZT.r1 heq; simp [sq_def] at this; linear_combination this
  have hQ : d1 ^ 2 + 2 * d0 * d2 = 0 := by
    have := congrArg ZT.r2 heq; simp [sq_def] at this; linear_combination this
  simp only [N] at hN
  simp only at hodd
  have prim : ∀ p : ℤ, Prime p → p ∣ d0 → p ∣ d1 → p ∣ d2 → False :=
    fun p hpp h0 h1 h2 => hprim p hpp ⟨h0, h1, h2⟩
  by_cases hd2 : d2 = 0
  · -- the tangent direction: `δ = ±1`, giving `(±1, 0, −1)`
    subst hd2
    have hd1 : d1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
    subst hd1
    rcases eq_one_or_neg_one (fun p hpp h0 => prim p hpp h0 (dvd_zero p) (dvd_zero p))
      with rfl | rfl
    · rcases sq_eq_one (by linarith : x ^ 2 = 1) with rfl | rfl <;> simp_all [solutions]
    · nlinarith [sq_nonneg x]
  -- the twist class: `d₀ · (−2d₂) = d₁²` with `d₀` odd and coprime to `d₂`
  have hcop : IsCoprime (-2 * d2) d0 := by
    apply isCoprime_of_prime_dvd
    · rintro ⟨-, rfl⟩; exact absurd hodd (by decide)
    · intro p hpp hp2 hp0
      rw [neg_mul, dvd_neg] at hp2
      rcases hpp.dvd_or_dvd hp2 with h | h
      · exact not_dvd_two_of_dvd_odd hpp hodd hp0 h
      · have hsq : d1 ^ 2 = d0 * (-2 * d2) := by linear_combination hQ
        exact prim p hpp hp0 (hpp.dvd_of_dvd_pow (n := 2) (hsq ▸ dvd_mul_of_dvd_left hp0 _)) h
  obtain ⟨m, hm⟩ := Int.sq_of_isCoprime hcop (c := d1) (by linear_combination -hQ)
  have hf : d1 ^ 6 - 40 * d1 ^ 3 * d2 ^ 3 - 32 * d2 ^ 6 = (-2 * d2) ^ 3 * x ^ 2 := by
    linear_combination (4 * d0 ^ 2 * d2 ^ 2 - 2 * d0 * d1 ^ 2 * d2 + d1 ^ 4 - 24 * d1 * d2 ^ 3) * hQ
      + 8 * d2 ^ 3 * hN
  have hd2Q : (d2 : ℚ) ≠ 0 := by exact_mod_cast hd2
  have hF : FA ((d1 : ℚ) / d2) * (d2 : ℚ) ^ 6 = (-2 * (d2 : ℚ)) ^ 3 * (x : ℚ) ^ 2 := by
    rw [show FA ((d1 : ℚ) / d2) * (d2 : ℚ) ^ 6 = d1 ^ 6 - 40 * d1 ^ 3 * d2 ^ 3 - 32 * d2 ^ 6 by
      unfold FA; field_simp]
    exact_mod_cast hf
  rcases hm with hm | hm
  · -- `A⁺`, so `X = −1`: `δ = d₀(1, 2, −2)` and `3` divides `x, y, z`
    have hW := twist_point (μ := 1) (q := m) hd2Q hF (by rw [one_mul]; exact_mod_cast hm)
    rw [one_mul] at hW
    have hd1 := ratio_eq (r := -1) (s := 1) hd2 one_ne_zero (by rw [H.A_plus _ _ hW]; norm_num)
    have hd2' : d2 = -2 * d0 := by
      have : d2 * (d2 + 2 * d0) = 0 := by linear_combination hQ - (d1 - d2) * hd1
      linarith [(mul_eq_zero.mp this).resolve_left hd2]
    have hd1' : d1 = 2 * d0 := by linarith
    subst hd1' hd2'
    exact (hp.false_of_prime Int.prime_three
      (Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨3 * d0 ^ 3, by rw [hN]; ring⟩)
      ⟨-4 * d0 ^ 2, by rw [hy]; ring⟩ ⟨5 * d0 ^ 2, by rw [hz]; ring⟩).elim
  · have hW := twist_point (μ := -1) (q := m) hd2Q hF (by
      rw [neg_one_mul]; exact_mod_cast hm)
    exact (H.A_minus _ _ (by rw [hW]; ring)).elim

/-- `k = 1`: the conic is `d₁² − 2d₀d₁ + 2d₀d₂ − 2d₂² = 0` and the curves are `B± : y² = ±C₃(x)`,
`C± : y² = ±2C₃(x)`. With `u = d₂ − d₁` the conic reads `d₁² = u(2d₀ − 4d₁ − 2u)`, and the twist
class of `2u` is that of `μ ∈ {±1, ±2}`. -/
lemma case_k1 (H : Inputs) (hp : Primitive x y z) {δ : ZT} (D : Descended x y z 1 δ) :
    (x, y, z) ∈ solutions := by
  obtain ⟨d0, d1, d2⟩ := δ
  obtain ⟨heq, hN, hprim, hodd⟩ := D
  simp only [pow_one] at heq
  have hz : z = d0 ^ 2 - 4 * d0 * d2 - 2 * d1 ^ 2 + 4 * d1 * d2 := by
    have := congrArg ZT.r0 heq; simp [sq_def, ε] at this; linear_combination this
  have hy : y = -d0 ^ 2 + 2 * d0 * d1 - 4 * d1 * d2 + 2 * d2 ^ 2 := by
    have := congrArg ZT.r1 heq; simp [sq_def, ε] at this; linear_combination this
  have hQ : -2 * d0 * d1 + 2 * d0 * d2 + d1 ^ 2 - 2 * d2 ^ 2 = 0 := by
    have := congrArg ZT.r2 heq; simp [sq_def, ε] at this; linear_combination -this
  simp only [N] at hN
  simp only at hodd
  have prim : ∀ p : ℤ, Prime p → p ∣ d0 → p ∣ d1 → p ∣ d2 → False :=
    fun p hpp h0 h1 h2 => hprim p hpp ⟨h0, h1, h2⟩
  by_cases hd2 : d2 = 0
  · -- the tangent direction: `d₁(d₁ − 2d₀) = 0`
    subst hd2
    have : d1 * (d1 - 2 * d0) = 0 := by linear_combination hQ
    rcases mul_eq_zero.mp this with hd1 | hd1
    · -- `δ = ±1`, giving `(±1, −1, 1)`
      subst hd1
      rcases eq_one_or_neg_one (fun p hpp h0 => prim p hpp h0 (dvd_zero p) (dvd_zero p))
        with rfl | rfl
      · rcases sq_eq_one (by linarith : x ^ 2 = 1) with rfl | rfl <;> simp_all [solutions]
      · nlinarith [sq_nonneg x]
    · -- `δ = ±(1 + 2θ)`, of norm `±17`, not a square
      have hd1' : d1 = 2 * d0 := by linarith
      subst hd1'
      rcases eq_one_or_neg_one (fun p hpp h0 =>
          prim p hpp h0 (dvd_mul_of_dvd_right h0 2) (dvd_zero p)) with rfl | rfl
      · exact (sq_ne_17 x (by linarith)).elim
      · nlinarith [sq_nonneg x]
  set u := d2 - d1 with hu
  have hu0 : u ≠ 0 := by
    intro h0
    have : d1 = d2 := by linarith
    subst this
    exact hd2 (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination -hQ))
  have hsq : d1 ^ 2 = u * (2 * d0 - 4 * d1 - 2 * u) := by rw [hu]; linear_combination -hQ
  obtain ⟨m, hm⟩ := sq_class hsq
    (fun p hpp hpu hpv => by
      have h1 : p ∣ d1 := hpp.dvd_of_dvd_pow (n := 2) (hsq ▸ dvd_mul_of_dvd_left hpu _)
      have h2 : p ∣ d2 := by rw [show d2 = d1 + u by rw [hu]; ring]; exact dvd_add h1 hpu
      have h0 : p ∣ 2 * d0 := by
        rw [show 2 * d0 = (2 * d0 - 4 * d1 - 2 * u) + 4 * d1 + 2 * u by ring]
        exact dvd_add (dvd_add hpv (dvd_mul_of_dvd_right h1 4)) (dvd_mul_of_dvd_right hpu 2)
      rcases hpp.dvd_or_dvd h0 with h | h
      · exact h
      · exact (prim p hpp h h1 h2).elim)
    (fun h2u h2v h4v => by
      have h1 : (2 : ℤ) ∣ d1 :=
        Int.prime_two.dvd_of_dvd_pow (n := 2) (hsq ▸ dvd_mul_of_dvd_left h2u _)
      exact prim 2 Int.prime_two (by omega) h1 (by omega))
  have hf : -17 * d1 ^ 6 + 72 * d1 ^ 5 * d2 - 90 * d1 ^ 4 * d2 ^ 2 - 40 * d1 ^ 3 * d2 ^ 3
      + 180 * d1 ^ 2 * d2 ^ 4 - 144 * d1 * d2 ^ 5 + 40 * d2 ^ 6 = (2 * u) ^ 3 * x ^ 2 := by
    rw [hu]
    linear_combination (-4 * d0 ^ 2 * d1 ^ 2 + 8 * d0 ^ 2 * d1 * d2 - 4 * d0 ^ 2 * d2 ^ 2
      - 2 * d0 * d1 ^ 3 + 2 * d0 * d1 ^ 2 * d2 + 4 * d0 * d1 * d2 ^ 2 - 4 * d0 * d2 ^ 3 - d1 ^ 4
      + 24 * d1 ^ 3 * d2 - 44 * d1 ^ 2 * d2 ^ 2 + 24 * d1 * d2 ^ 3 - 4 * d2 ^ 4) * hQ
      - 8 * (d2 - d1) ^ 3 * hN
  have hd2Q : (d2 : ℚ) ≠ 0 := by exact_mod_cast hd2
  have hF : (fun X => -C3 X) ((d1 : ℚ) / d2) * (d2 : ℚ) ^ 6 = (2 * (u : ℚ)) ^ 3 * (x : ℚ) ^ 2 := by
    rw [show (fun X => -C3 X) ((d1 : ℚ) / d2) * (d2 : ℚ) ^ 6 = -17 * d1 ^ 6 + 72 * d1 ^ 5 * d2
      - 90 * d1 ^ 4 * d2 ^ 2 - 40 * d1 ^ 3 * d2 ^ 3 + 180 * d1 ^ 2 * d2 ^ 4 - 144 * d1 * d2 ^ 5
      + 40 * d2 ^ 6 by unfold C3; field_simp; ring]
    exact_mod_cast hf
  -- the four twists; `B⁺` and `C⁻` have no points
  have hX : (d1 : ℚ) / d2 = 1 ∨ (d1 : ℚ) / d2 = -1 ∨ (d1 : ℚ) / d2 = 6 / 5 ∨ (d1 : ℚ) / d2 = 2 := by
    rcases hm with hm | hm | hm | hm
    · have hW := twist_point (F := fun X => -C3 X) (lam := 2 * (u : ℚ)) (μ := 2) (q := m)
        hd2Q hF (by rw [hm]; push_cast; ring)
      exact (H.C_minus _ _ (by rw [hW]; ring)).elim
    · have hW := twist_point (F := fun X => -C3 X) (lam := 2 * (u : ℚ)) (μ := -2) (q := m)
        hd2Q hF (by rw [hm]; push_cast; ring)
      rcases H.C_plus _ _ (by rw [hW]; ring) with h | h <;> simp [h]
    · have hW := twist_point (F := fun X => -C3 X) (lam := 2 * (u : ℚ)) (μ := 1) (q := 2 * m)
        hd2Q hF (by rw [hm]; push_cast; ring)
      rcases H.B_minus _ _ (by rw [hW]; ring) with h | h <;> simp [h]
    · have hW := twist_point (F := fun X => -C3 X) (lam := 2 * (u : ℚ)) (μ := -1) (q := 2 * m)
        hd2Q hF (by rw [hm]; push_cast; ring)
      exact (H.B_plus _ _ (by rw [hW]; ring)).elim
  rcases hX with hX | hX | hX | hX
  · -- `X = 1` would need `u = 0`
    have := ratio_eq (r := 1) (s := 1) hd2 one_ne_zero (by rw [hX]; norm_num)
    exact (hu0 (by rw [hu]; linarith)).elim
  · -- `X = −1`: `δ = d₀(1, −4, 4)`, and 3 divides `x, y, z`
    have hd1 := ratio_eq (r := -1) (s := 1) hd2 one_ne_zero (by rw [hX]; norm_num)
    obtain rfl : d1 = -d2 := by linarith
    obtain rfl : d2 = 4 * d0 := by
      have : d2 * (4 * d0 - d2) = 0 := by linear_combination hQ
      linarith [(mul_eq_zero.mp this).resolve_left hd2]
    exact (hp.false_of_prime Int.prime_three
      (Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨75 * d0 ^ 3, by rw [hN]; ring⟩)
      ⟨29 * d0 ^ 2, by rw [hy]; ring⟩ ⟨-37 * d0 ^ 2, by rw [hz]; ring⟩).elim
  · -- `X = 6/5`: `δ = ±(−7 + 6θ + 5θ²)`, giving `(±43, −203, 237)`
    have hd1 := ratio_eq (r := 6) (s := 5) hd2 (by norm_num) (by rw [hX]; norm_num)
    obtain ⟨e, he⟩ : ∃ e, d2 = 5 * e := ⟨d2 / 5, by omega⟩
    have hd1' : d1 = 6 * e := by omega
    have he0 : e ≠ 0 := by rintro rfl; exact hd2 (by simp [he])
    subst hd1' he
    obtain rfl : d0 = -7 * e := by
      have : (2 * e) * (d0 + 7 * e) = 0 := by linear_combination -hQ
      linarith [(mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero he0)]
    rcases eq_one_or_neg_one (fun p hpp h => prim p hpp (dvd_mul_of_dvd_right h _)
        (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right h _)) with rfl | rfl
    · have : (x - 43) * (x + 43) = 0 := by linear_combination hN
      rcases mul_eq_zero.mp this with h | h
      · obtain rfl : x = 43 := by linarith
        simp_all [solutions]
      · obtain rfl : x = -43 := by linarith
        simp_all [solutions]
    · nlinarith [sq_nonneg x]
  · -- `X = 2`: `δ = d₂(1, 2, 1)`, and 3 divides `x, y, z`
    have hd1 := ratio_eq (r := 2) (s := 1) hd2 one_ne_zero (by rw [hX]; norm_num)
    obtain rfl : d1 = 2 * d2 := by linarith
    obtain rfl : d0 = d2 := by
      have : (2 * d2) * (d2 - d0) = 0 := by linear_combination hQ
      linarith [(mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hd2)]
    exact (hp.false_of_prime Int.prime_three
      (Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨3 * d0 ^ 3, by rw [hN]; ring⟩)
      ⟨-d0 ^ 2, by rw [hy]; ring⟩ ⟨-d0 ^ 2, by rw [hz]; ring⟩).elim

end Fermat433
