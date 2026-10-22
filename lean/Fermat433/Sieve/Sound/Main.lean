/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Sieve.Sound.Sieve
import Fermat433.Sieve.Theorem

/-!
# The sieve for `B⁻`, as a statement about elliptic curves

`sieve_B_minus_sound` combines the kernel computation `sieve_B_minus` with the soundness of the
checker. For each of the 520 candidates the sieve removes, there is a prime `q` (997 or 12973) of
`L` at which no point of `X(𝔽_q)` has the images in the 499-parts of `E₁(𝔽_q)` and `E₂(𝔽_q)` that
the candidate's vector `a = (a₁, a₂)` predicts.
-/

namespace Fermat433.Sieve

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

/-- A candidate missing from the output of `run` was removed at one of the primes. -/
lemma run_removed (I : Inputs) : ∀ (certs : List PrimeCert) (alive L : List (ℕ × ℕ)),
    certs.foldlM (fun alive C => sievePrime I C alive) alive = some L →
    ∀ a ∈ alive, a ∉ L → ∃ C ∈ certs, ∃ al al', sievePrime I C al = some al' ∧ a ∈ al ∧ a ∉ al'
  | [], alive, L, h, a, ha, hna => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact absurd (h ▸ ha) hna
  | C :: certs, alive, L, h, a, ha, hna => by
    simp only [List.foldlM_cons, Option.bind_eq_bind] at h
    cases hC : sievePrime I C alive with
    | none => simp [hC] at h
    | some al' =>
      rw [hC, Option.bind_some] at h
      by_cases hal : a ∈ al'
      · obtain ⟨C', hC', rest⟩ := run_removed I certs al' L h a hal hna
        exact ⟨C', List.mem_cons_of_mem _ hC', rest⟩
      · exact ⟨C, List.mem_cons_self .., alive, al', hC, ha, hal⟩

/-- **The sieve for `B⁻`.** Every candidate other than the four known points is removed at a prime
`q ∈ {997, 12973}` of `L`: no point `P` of `X(𝔽_q)` satisfies both
`c₁·φ₁(P) = a₁·c₁·φ₁(P₁) + a₂·c₁·φ₁(P₂)` on `E₁` and `c₂·φ₂(P) = a₁·c₂·φ₂(P₁) + a₂·c₂·φ₂(P₂)` on
`E₂`, where `P₁ = (1, 1)`, `P₂ = (−1, 15)` and `cᵢ = #Eᵢ(𝔽_q)/499`. -/
theorem sieve_B_minus_sound (a : ℕ × ℕ) (ha : a ∈ inputs.cands)
    (hs : a ∉ [(1, 0), (498, 0), (0, 1), (0, 498)]) :
    ∃ C ∈ certs, ∃ hq : C.q.Prime,
      haveI : Fact C.q.Prime := ⟨hq⟩
      ∀ (G11 G12 : (W1 inputs C.q C.r).Point) (G21 G22 : (W2 inputs C.q C.r).Point),
        Im1 (I := inputs) (r := C.r) (toEv (vals inputs C.q C.r) (.aff 1 1)) G11 →
        Im1 (I := inputs) (r := C.r) (toEv (vals inputs C.q C.r) (.aff (-1) 15)) G12 →
        Im2 (I := inputs) (r := C.r) (toEv (vals inputs C.q C.r) (.aff 1 1)) G21 →
        Im2 (I := inputs) (r := C.r) (toEv (vals inputs C.q C.r) (.aff (-1) 15)) G22 →
        ∀ P : XPt C.q, P.Valid →
        ∀ (Q1 : (W1 inputs C.q C.r).Point) (Q2 : (W2 inputs C.q C.r).Point),
          Im1 (I := inputs) (r := C.r) (toEv (vals inputs C.q C.r) P) Q1 →
          Im2 (I := inputs) (r := C.r) (toEv (vals inputs C.q C.r) P) Q2 →
          ¬ ((Nat.card (W1 inputs C.q C.r).Point / 499) • Q1 =
                a.1 • (Nat.card (W1 inputs C.q C.r).Point / 499) • G11 +
                  a.2 • (Nat.card (W1 inputs C.q C.r).Point / 499) • G12 ∧
              (Nat.card (W2 inputs C.q C.r).Point / 499) • Q2 =
                a.1 • (Nat.card (W2 inputs C.q C.r).Point / 499) • G21 +
                  a.2 • (Nat.card (W2 inputs C.q C.r).Point / 499) • G22) := by
  obtain ⟨C, hC, al, al', hrun, hal, hal'⟩ :=
    run_removed inputs certs inputs.cands _ sieve_B_minus a ha hs
  refine ⟨C, hC, ?_⟩
  obtain ⟨q, r, R⟩ := C
  have hp : primeOk inputs ⟨q, r, R⟩ = true := by
    unfold sievePrime at hrun; split_ifs at hrun with h; · exact h
  have hq : q.Prime := by
    simp only [primeOk, Bool.and_eq_true] at hp
    exact isPrime_sound hp.1.1.1.1.1.1.1.1.1.1.1.1.1
  refine ⟨hq, ?_⟩
  have : Fact q.Prime := ⟨hq⟩
  intro G11 G12 G21 G22 hG11 hG12 hG21 hG22 P hP Q1 Q2 h1 h2
  exact sievePrime_sound hrun a hal hal' hG11 hG12 hG21 hG22 P hP h1 h2

end Fermat433.Sieve
