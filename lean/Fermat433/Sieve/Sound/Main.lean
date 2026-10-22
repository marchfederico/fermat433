/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Sieve.Sound.Sieve
import Fermat433.Sieve.Theorem
import Fermat433.Sieve.TheoremP1459

/-!
# The sieves for `B⁻` and `C⁺`, at `p = 499` and `p = 1459`, as statements about elliptic curves

`sieve_B_minus_sound` and `sieve_C_plus_sound` combine the kernel computations `sieve_B_minus`,
`sieve_C_plus` with the soundness of the checker (`run_sound`). For each candidate the sieve
removes (520 on `B⁻`, 500 on `C⁺`), there is a prime `q` (997 or 12973) of `L` at which no point of
`X(𝔽_q)` has the images in the ℓ-parts of `E₁(𝔽_q)` and `E₂(𝔽_q)` that the candidate's vector
`a = (a₁, a₂)` predicts (`SieveRemoves`).
-/

namespace Fermat433.Sieve

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

/-- The conclusion of the sieve for a candidate `a` at a prime `C` (stated for any curve given by
`I`): no point `P` of `X(𝔽_q)` satisfies both
`c₁·φ₁(P) = a₁·c₁·φ₁(P₁) + a₂·c₁·φ₁(P₂)` on `E₁` and `c₂·φ₂(P) = a₁·c₂·φ₂(P₁) + a₂·c₂·φ₂(P₂)`
on `E₂`, where `P₁, P₂` are the generators and `cᵢ = #Eᵢ(𝔽_q)/ℓ`. -/
def SieveRemoves (I : Inputs) (C : PrimeCert) (a : ℕ × ℕ) : Prop :=
  ∃ hq : C.q.Prime,
    haveI : Fact C.q.Prime := ⟨hq⟩
    ∀ (G11 G12 : (W1 I C.q C.r).Point) (G21 G22 : (W2 I C.q C.r).Point),
      Im1 (I := I) (r := C.r) (toEv (vals I C.q C.r) (.ofRat I.p1)) G11 →
      Im1 (I := I) (r := C.r) (toEv (vals I C.q C.r) (.ofRat I.p2)) G12 →
      Im2 (I := I) (r := C.r) (toEv (vals I C.q C.r) (.ofRat I.p1)) G21 →
      Im2 (I := I) (r := C.r) (toEv (vals I C.q C.r) (.ofRat I.p2)) G22 →
      ∀ P : XPt C.q, P.Valid I.f →
      ∀ (Q1 : (W1 I C.q C.r).Point) (Q2 : (W2 I C.q C.r).Point),
        Im1 (I := I) (r := C.r) (toEv (vals I C.q C.r) P) Q1 →
        Im2 (I := I) (r := C.r) (toEv (vals I C.q C.r) P) Q2 →
        ¬ ((Nat.card (W1 I C.q C.r).Point / I.ell) • Q1 =
              a.1 • (Nat.card (W1 I C.q C.r).Point / I.ell) • G11 +
                a.2 • (Nat.card (W1 I C.q C.r).Point / I.ell) • G12 ∧
            (Nat.card (W2 I C.q C.r).Point / I.ell) • Q2 =
              a.1 • (Nat.card (W2 I C.q C.r).Point / I.ell) • G21 +
                a.2 • (Nat.card (W2 I C.q C.r).Point / I.ell) • G22)

/-- **Soundness of the checker.** If `run` returns `L`, every candidate not in `L` is removed, in
the sense of `SieveRemoves`, at one of the primes. -/
theorem run_sound {I : Inputs} {certs : List PrimeCert} {L : List (ℕ × ℕ)}
    (h : run I certs = some L) (a : ℕ × ℕ) (ha : a ∈ I.cands) (hs : a ∉ L) :
    ∃ C ∈ certs, SieveRemoves I C a := by
  obtain ⟨C, hC, al, al', hrun, hal, hal'⟩ := run_removed I certs I.cands _ h a ha hs
  refine ⟨C, hC, ?_⟩
  obtain ⟨q, r, R⟩ := C
  have hp : primeOk I ⟨q, r, R⟩ = true := by
    unfold sievePrime at hrun; split_ifs at hrun with h; · exact h
  have hq : q.Prime := by
    simp only [primeOk, Bool.and_eq_true] at hp
    exact isPrime_sound hp.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  refine ⟨hq, ?_⟩
  have : Fact q.Prime := ⟨hq⟩
  intro G11 G12 G21 G22 hG11 hG12 hG21 hG22 P hP Q1 Q2 h1 h2
  exact sievePrime_sound hrun a hal hal' hG11 hG12 hG21 hG22 P hP h1 h2

/-- **The sieve for `B⁻ : y² = −C₃(x)`.** Of the 524 quadratic Chabauty candidates, every one
except the four known points `(1, ±1)`, `(−1, ±15)` is removed at `q = 997` or `q = 12973`. -/
theorem sieve_B_minus_sound (a : ℕ × ℕ) (ha : a ∈ Bminus.inputs.cands)
    (hs : a ∉ [(1, 0), (498, 0), (0, 1), (0, 498)]) :
    ∃ C ∈ Bminus.certs, SieveRemoves Bminus.inputs C a :=
  run_sound sieve_B_minus a ha hs

/-- **The sieve for `C⁺ : y² = 2C₃(x)`.** Of the 504 quadratic Chabauty candidates, every one
except the four known points `(6/5, ±172/125)`, `(2, ±12)` is removed at `q = 997` or
`q = 12973`. -/
theorem sieve_C_plus_sound (a : ℕ × ℕ) (ha : a ∈ Cplus.inputs.cands)
    (hs : a ∉ [(0, 1), (0, 498), (1, 0), (498, 0)]) :
    ∃ C ∈ Cplus.certs, SieveRemoves Cplus.inputs C a :=
  run_sound sieve_C_plus a ha hs

/-- **The sieve for `B⁻` in the rerun at `p = 1459`.** Of the 1546 candidates, every one except the
four known points is removed at `q = 2917` or `q = 26261`, in the 1459-parts. -/
theorem sieve_B_minus_p1459_sound (a : ℕ × ℕ) (ha : a ∈ Bminus_p1459.inputs.cands)
    (hs : a ∉ [(1, 0), (1458, 0), (0, 1), (0, 1458)]) :
    ∃ C ∈ Bminus_p1459.certs, SieveRemoves Bminus_p1459.inputs C a :=
  run_sound sieve_B_minus_p1459 a ha hs

/-- **The sieve for `C⁺` in the rerun at `p = 1459`.** Of the 1426 candidates (with the disks
`x ≡ 103` recomputed), every one except the four known points is removed at `q = 2917`. -/
theorem sieve_C_plus_p1459_sound (a : ℕ × ℕ) (ha : a ∈ Cplus_p1459.inputs.cands)
    (hs : a ∉ [(0, 1), (0, 1458), (1458, 0), (1, 0)]) :
    ∃ C ∈ Cplus_p1459.certs, SieveRemoves Cplus_p1459.inputs C a :=
  run_sound sieve_C_plus_p1459 a ha hs

end Fermat433.Sieve
