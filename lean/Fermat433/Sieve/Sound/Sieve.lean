/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Sieve.Sound.Bridge

/-!
# Soundness of the checker, part 4d: the sieve at one prime

`sievePrime_sound`: if `sievePrime I C alive = some alive'`, then for every candidate `a` it
removed, no point `P` of `X(𝔽_q)` satisfies
`c₁·φ₁(P) = a₁·c₁·φ₁(P₁) + a₂·c₁·φ₁(P₂)` and `c₂·φ₂(P) = a₁·c₂·φ₂(P₁) + a₂·c₂·φ₂(P₂)`,
where `P₁, P₂` are the generators and `cᵢ = #Eᵢ(𝔽_q)/ℓ`. Everything in the statement is a
Mathlib object: points of Weierstrass curves over `ZMod q` and their group law.
-/

namespace Fermat433.Sieve

open WeierstrassCurve WeierstrassCurve.Affine

lemma distinct_nodup : ∀ l : List Pt, distinct l = true → l.Nodup
  | [] => fun _ => List.nodup_nil
  | P :: Ps => fun h => by
    simp only [distinct, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, distinct_nodup Ps h2⟩
    have : Ps.contains P = true := by simpa using hm
    rw [this] at h1; exact Bool.noConfusion h1

open Classical in
/-- A Mathlib point represented by a checker point (junk `0` if there is none). -/
noncomputable def repOf (E : Curve) (q : ℕ) [Fact q.Prime] (P : Pt) : (E.W q).Point :=
  if h : ∃ P', E.Rep q P P' then h.choose else 0

open Classical in
lemma repOf_spec (E : Curve) (q : ℕ) [Fact q.Prime] {P : Pt} (h : ∃ P', E.Rep q P P') :
    E.Rep q P (repOf E q P) := by
  simp only [repOf, h, ↓reduceDIte]; exact h.choose_spec

/-- The checker's trial division is correct. -/
lemma isPrime_sound {q : ℕ} (h : isPrime q = true) : q.Prime := by
  simp only [isPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨h2, hall⟩ := h
  by_contra hnp
  have hq0 : 0 < q := by omega
  have hm2 : 2 ≤ q.minFac := (Nat.minFac_prime (by omega)).two_le
  have hsq := Nat.minFac_sq_le_self hq0 hnp
  have hlt : q.minFac < q := by nlinarith
  rcases hall q.minFac hlt with (h1 | h1) | h1
  · omega
  · nlinarith
  · exact h1 (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd q))

variable {I : Inputs}

/-- The unpacked `primeOk`. -/
structure PrimeFacts (I : Inputs) (q r : ℕ) : Prop where
  ellp : I.ell.Prime
  ellq : I.ell < q
  q16 : 15 < q
  q32 : q < 2 ^ 32
  facts : SettingFacts (I := I) (q := q) (r := r)
  A0 : (setting I q r).A ≠ 0
  disc1 : (setting I q r).E1.disc q ≠ 0
  disc2 : (setting I q r).E2.disc q ≠ 0

lemma primeFacts_of {q r : ℕ} {R : List Removal} (h : primeOk I ⟨q, r, R⟩ = true) :
    PrimeFacts I q r := by
  simp only [primeOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, hl⟩, -⟩, hlq⟩, h16⟩, h32⟩, -⟩, -⟩, -⟩, -⟩, hok⟩, -⟩, hA⟩, -⟩, hd1⟩,
    hd2⟩ := h
  exact ⟨isPrime_sound hl, hlq, h16, h32, settingFacts_of_ok hf hok, hA, hd1, hd2⟩

/-- The cofactor: if `ℓ ∥ N = #E`, then `#E = c·ℓ` with `ℓ ∤ c`, `c = (N/ℓ).toNat`. -/
lemma cofactor {N : ℤ} {n ell : ℕ} (hell : 0 < ell) (hn : (n : ℤ) = N) (ha : N % ell = 0)
    (hb : N % ((ell : ℤ) * ell) ≠ 0) : n = (N / ell).toNat * ell ∧ ¬ ell ∣ (N / ell).toNat := by
  obtain ⟨k, rfl⟩ := Int.dvd_of_emod_eq_zero ha
  have hell' : (0 : ℤ) < ell := by exact_mod_cast hell
  have hk : 0 ≤ k := by
    have : (0 : ℤ) ≤ ell * k := hn ▸ Int.natCast_nonneg n
    exact nonneg_of_mul_nonneg_right (by linarith) hell'
  rw [Int.mul_ediv_cancel_left _ hell'.ne']
  refine ⟨by have := Int.toNat_of_nonneg hk; zify; rw [this, hn]; ring, ?_⟩
  rintro ⟨m, hm⟩
  apply hb
  have : k = ell * m := by have := Int.toNat_of_nonneg hk; rw [← this, hm]; push_cast; ring
  rw [this, ← mul_assoc]
  exact Int.mul_emod_right _ _

/-- A candidate dropped by `sieveList` had a valid removal witness. -/
lemma sieveList_removed (S : Setting) (c1 c2 : ℕ) (a : ℕ × ℕ) :
    ∀ (alive : List (ℕ × ℕ)) (Rs : List Removal), a ∈ alive → a ∉ sieveList S c1 c2 alive Rs →
      ∃ R ∈ Rs, R.a = a ∧ removedBy S c1 c2 R = true
  | [], _, ha, _ => absurd ha List.not_mem_nil
  | b :: bs, [], ha, hna => absurd ha (by simpa [sieveList] using hna)
  | b :: bs, R :: Rs, ha, hna => by
    simp only [sieveList] at hna
    by_cases hRb : (R.a == b) = true
    · simp only [hRb, ↓reduceIte] at hna
      by_cases hv : removedBy S c1 c2 R = true
      · simp only [hv, ↓reduceIte] at hna
        by_cases hab : a = b
        · exact ⟨R, List.mem_cons_self .., (beq_iff_eq.mp hRb).trans hab.symm, hv⟩
        · obtain ⟨R', hR', h⟩ := sieveList_removed S c1 c2 a bs Rs
            ((List.mem_cons.mp ha).resolve_left hab) hna
          exact ⟨R', List.mem_cons_of_mem _ hR', h⟩
      · simp only [Bool.not_eq_true] at hv
        simp only [hv, Bool.false_eq_true, ↓reduceIte, List.mem_cons, not_or] at hna
        obtain ⟨R', hR', h⟩ := sieveList_removed S c1 c2 a bs Rs
          ((List.mem_cons.mp ha).resolve_left hna.1) hna.2
        exact ⟨R', List.mem_cons_of_mem _ hR', h⟩
    · simp only [Bool.not_eq_true] at hRb
      simp only [hRb, Bool.false_eq_true, ↓reduceIte, List.mem_cons, not_or] at hna
      exact sieveList_removed S c1 c2 a bs (R :: Rs) ((List.mem_cons.mp ha).resolve_left hna.1)
        hna.2

/-- The quotient curves over `ZMod q`. -/
abbrev W1 (I : Inputs) (q r : ℕ) : Affine (ZMod q) := (setting I q r).E1.W q
abbrev W2 (I : Inputs) (q r : ℕ) : Affine (ZMod q) := (setting I q r).E2.W q

/-- **Soundness of the sieve at one prime.** If `sievePrime` returns `alive'`, then for each
candidate `a` it removed, no point `P` of `X(𝔽_q)` has
`c₁·φ₁(P) = a₁·c₁·φ₁(P₁) + a₂·c₁·φ₁(P₂)` and `c₂·φ₂(P) = a₁·c₂·φ₂(P₁) + a₂·c₂·φ₂(P₂)`,
with `P₁, P₂` the generators and `cᵢ = #Eᵢ(𝔽_q)/ℓ`. -/
theorem sievePrime_sound {q r : ℕ} [Fact q.Prime] {R : List Removal}
    {alive alive' : List (ℕ × ℕ)} (h : sievePrime I ⟨q, r, R⟩ alive = some alive')
    (a : ℕ × ℕ) (ha : a ∈ alive) (hna : a ∉ alive')
    {G11 G12 : (W1 I q r).Point} {G21 G22 : (W2 I q r).Point}
    (hG11 : Im1 (I := I) (r := r) (toEv (vals I q r) (.ofRat I.p1)) G11)
    (hG12 : Im1 (I := I) (r := r) (toEv (vals I q r) (.ofRat I.p2)) G12)
    (hG21 : Im2 (I := I) (r := r) (toEv (vals I q r) (.ofRat I.p1)) G21)
    (hG22 : Im2 (I := I) (r := r) (toEv (vals I q r) (.ofRat I.p2)) G22)
    (P : XPt q) (hP : P.Valid I.f) {Q1 : (W1 I q r).Point} {Q2 : (W2 I q r).Point}
    (h1 : Im1 (I := I) (r := r) (toEv (vals I q r) P) Q1)
    (h2 : Im2 (I := I) (r := r) (toEv (vals I q r) P) Q2) :
    ¬ ((Nat.card (W1 I q r).Point / I.ell) • Q1 =
          a.1 • (Nat.card (W1 I q r).Point / I.ell) • G11 +
            a.2 • (Nat.card (W1 I q r).Point / I.ell) • G12 ∧
        (Nat.card (W2 I q r).Point / I.ell) • Q2 =
          a.1 • (Nat.card (W2 I q r).Point / I.ell) • G21 +
            a.2 • (Nat.card (W2 I q r).Point / I.ell) • G22) := by
  have h0 : 0 < q := (Fact.out : q.Prime).pos
  have hq' : (setting I q r).q = q := setting_q I q r
  -- unpack the run
  unfold sievePrime at h
  dsimp only at h
  split_ifs at h with hp ho
  have hfil := Option.some.inj h
  have hF := primeFacts_of hp
  have hq16 := hF.q16
  have hq2 : q ≠ 2 := by omega
  have hq64 : q < 2 ^ 64 := by have := hF.q32; omega
  set S := setting I q r with hS
  set N1 := S.E1.order q with hN1
  set N2 := S.E2.order q with hN2
  simp only [ordersOk, Bool.and_eq_true, decide_eq_true_eq] at ho
  obtain ⟨⟨⟨⟨⟨hN1a, hN1b⟩, hN2a⟩, hN2b⟩, hc1q⟩, hc2q⟩ := ho
  -- the cofactors
  have hΔ1 := S.E1.Δ_ne_zero q hq2 hF.disc1
  have hΔ2 := S.E2.Δ_ne_zero q hq2 hF.disc2
  have hcard1 : (Nat.card (W1 I q r).Point : ℤ) = N1 := S.E1.card_eq_order q hq2 hq64 hΔ1
  have hcard2 : (Nat.card (W2 I q r).Point : ℤ) = N2 := S.E2.card_eq_order q hq2 hq64 hΔ2
  have hl0 : 0 < I.ell := hF.ellp.pos
  obtain ⟨hk1, hnd1⟩ := cofactor hl0 hcard1 hN1a hN1b
  obtain ⟨hk2, -⟩ := cofactor hl0 hcard2 hN2a hN2b
  set c1 := (N1 / I.ell).toNat with hc1
  set c2 := (N2 / I.ell).toNat with hc2
  have hc1' : Nat.card (W1 I q r).Point / I.ell = c1 := by rw [hk1, Nat.mul_div_cancel _ hl0]
  have hc2' : Nat.card (W2 I q r).Point / I.ell = c2 := by rw [hk2, Nat.mul_div_cancel _ hl0]
  rw [hc1', hc2']
  have hc1_64 : c1 < 2 ^ 64 := by omega
  have hc2_64 : c2 < 2 ^ 64 := by omega
  have ha21 := hF.facts.a2_1
  have ha22 := hF.facts.a2_2
  -- the removal witness for `a`
  rw [← hfil] at hna
  obtain ⟨Rm, -, rfl, hrem⟩ := sieveList_removed S c1 c2 a alive R ha hna
  unfold removedBy at hrem
  dsimp only at hrem
  simp only [hq', Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hrem
  obtain ⟨⟨⟨⟨ha1, ha2⟩, hlen⟩, hdist⟩, hall⟩ := hrem
  have hSell : S.ell = I.ell := by rw [hS]; simp only [setting]
  have hellq := hF.ellq
  rw [hSell] at ha1 ha2
  -- the generators and the targets
  have e1 : XPt.ofRat (q := q) I.p1 = .aff (S.p1.1 : ZMod q) (S.p1.2 : ZMod q) := by
    rw [hS, setting_p1, XPt.ofRat, ratMod_cast hq2 hq64, ratMod_cast hq2 hq64]
  have e2 : XPt.ofRat (q := q) I.p2 = .aff (S.p2.1 : ZMod q) (S.p2.2 : ZMod q) := by
    rw [hS, setting_p2, XPt.ofRat, ratMod_cast hq2 hq64, ratMod_cast hq2 hq64]
  rw [e1] at hG11 hG21
  rw [e2] at hG12 hG22
  have hlt : ∀ z : ℤ × ℕ, ratMod z q < q := fun z => Nat.mod_lt _ h0
  have hp1 : S.p1.1 < q ∧ S.p1.2 < q := by rw [hS, setting_p1]; exact ⟨hlt _, hlt _⟩
  have hp2 : S.p2.1 < q ∧ S.p2.2 < q := by rw [hS, setting_p2]; exact ⟨hlt _, hlt _⟩
  obtain ⟨r11, r21⟩ := phi_rep hF.facts hq2 hq64 hp1.1 hp1.2 hG11 hG21
  obtain ⟨r12, r22⟩ := phi_rep hF.facts hq2 hq64 hp2.1 hp2.2 hG12 hG22
  have hT1 : S.E1.Rep q (target S c1 c2 Rm.a).1
      (Rm.a.1 • c1 • G11 + Rm.a.2 • c1 • G12) := by
    simp only [target, imgAt, hq']
    exact S.E1.add_rep q hq2 hq64 ha21
      (S.E1.mul_rep q hq2 hq64 ha21 (by omega) (S.E1.mul_rep q hq2 hq64 ha21 hc1_64 r11))
      (S.E1.mul_rep q hq2 hq64 ha21 (by omega) (S.E1.mul_rep q hq2 hq64 ha21 hc1_64 r12))
  have hT2 : S.E2.Rep q (target S c1 c2 Rm.a).2
      (Rm.a.1 • c2 • G21 + Rm.a.2 • c2 • G22) := by
    simp only [target, imgAt, hq']
    exact S.E2.add_rep q hq2 hq64 ha22
      (S.E2.mul_rep q hq2 hq64 ha22 (by omega) (S.E2.mul_rep q hq2 hq64 ha22 hc2_64 r21))
      (S.E2.mul_rep q hq2 hq64 ha22 (by omega) (S.E2.mul_rep q hq2 hq64 ha22 hc2_64 r22))
  -- the fibre, as Mathlib points
  have hex : ∀ p ∈ Rm.fibre, ∃ Q', S.E1.Rep q p.1 Q' := by
    intro ⟨Q, w⟩ hm
    obtain ⟨⟨⟨⟨hred, -⟩, hon⟩, -⟩, -⟩ := hall _ hm
    cases Q with
    | inf => exact ⟨0, rfl⟩
    | pt x y =>
      simp only [Pt.reduced, Bool.and_eq_true, decide_eq_true_eq] at hred
      exact S.E1.rep_of_onCurve q hq2 hF.disc1 hred.1 hred.2 hon
  set L := Rm.fibre.map fun p => repOf S.E1 q p.1 with hL
  have hLnd : L.Nodup := by
    rw [hL, show (fun p : Pt × ℕ => repOf S.E1 q p.1) = repOf S.E1 q ∘ Prod.fst from rfl,
      ← List.map_map]
    refine List.Nodup.map_on ?_ (distinct_nodup _ hdist)
    intro x hx y hy hxy
    obtain ⟨px, hpx, rfl⟩ := List.mem_map.mp hx
    obtain ⟨py, hpy, rfl⟩ := List.mem_map.mp hy
    exact (S.E1.rep_inj q (repOf_spec _ _ (hex _ hpx)) (repOf_spec _ _ (hex _ hpy))).mpr hxy
  have hLlen : L.length = c1 := by rw [hL, List.length_map, hlen]
  have hLfib : ∀ Q ∈ L, c1 • Q = Rm.a.1 • c1 • G11 + Rm.a.2 • c1 • G12 := by
    intro Q hQ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hQ
    obtain ⟨⟨⟨⟨-, -⟩, -⟩, hmul⟩, -⟩ := hall _ hp
    exact (S.E1.rep_inj q (S.E1.mul_rep q hq2 hq64 ha21 hc1_64 (repOf_spec _ _ (hex _ hp)))
      hT1).mp hmul
  -- conclude
  rintro ⟨hc1eq, hc2eq⟩
  obtain ⟨p, hp, hpQ⟩ := List.mem_map.mp (mem_of_fibre hF.ellp hk1 hnd1 L hLnd hLlen hLfib hc1eq)
  obtain ⟨⟨⟨⟨-, hw⟩, -⟩, -⟩, hok⟩ := hall _ hp
  have hQ : S.E1.Rep q p.1 Q1 := hpQ ▸ repOf_spec _ _ (hex _ hp)
  exact fibreOk_sound hF.facts hq2 hq64 hF.A0 hc2_64 hT2 hw hok hQ
    (toEv_valid hF.facts h0 P hP) h1 h2 hc2eq

end Fermat433.Sieve
