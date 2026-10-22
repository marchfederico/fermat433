/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Sieve.Sound.Arith

/-!
# Soundness of the checker, part 4a: polynomials as lists

The checker stores polynomials over `𝔽_q` as coefficient lists (lowest degree first). `evZ l X`
evaluates such a list in `ZMod q`; the list operations `padd`, `pscale`, `pmul`, `ppow` are shown to
add, scale, multiply and raise to powers, and `evalPoly` to evaluate. The upshot is
`evZ_evenModel`: the checker's `F` is `Σₖ fₖ (x₋X − x₊)ᵏ (X − 1)⁶⁻ᵏ`.
-/

namespace Fermat433.Sieve

open Finset

variable {q : ℕ}

/-- Evaluate a coefficient list at `X : ZMod q`. -/
def evZ (l : List ℕ) (X : ZMod q) : ZMod q := l.foldr (fun c acc => acc * X + c) 0

@[simp] lemma evZ_nil (X : ZMod q) : evZ [] X = 0 := rfl

@[simp] lemma evZ_cons (c : ℕ) (l : List ℕ) (X : ZMod q) : evZ (c :: l) X = evZ l X * X + c := rfl

lemma evalPoly_cast (l : List ℕ) (x : ℕ) : (evalPoly l x q : ZMod q) = evZ l (x : ZMod q) := by
  induction l with
  | nil => simp [evalPoly]
  | cons c l ih =>
    simp only [evalPoly, List.foldr_cons] at ih ⊢
    rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ih, evZ_cons]

lemma evZ_padd (X : ZMod q) : ∀ a b : List ℕ, evZ (padd a b q) X = evZ a X + evZ b X
  | [], b => by simp [padd]
  | x :: a, [] => by simp [padd]
  | x :: a, y :: b => by
    simp only [padd, evZ_cons, evZ_padd X a b, ZMod.natCast_mod, Nat.cast_add]; ring

lemma evZ_pscale (c : ℕ) (X : ZMod q) : ∀ a : List ℕ, evZ (pscale c a q) X = c * evZ a X
  | [] => by simp [pscale]
  | x :: a => by
    have := evZ_pscale c X a
    simp only [pscale, List.map_cons, evZ_cons] at this ⊢
    rw [this, ZMod.natCast_mod, Nat.cast_mul]; ring

lemma evZ_pmul (X : ZMod q) : ∀ a b : List ℕ, evZ (pmul a b q) X = evZ a X * evZ b X
  | [], b => by simp [pmul]
  | x :: a, b => by
    rw [pmul, evZ_padd, evZ_pscale, evZ_cons, evZ_pmul X a b, evZ_cons]; push_cast; ring

lemma evZ_foldl_pmul (X : ZMod q) (a : List ℕ) :
    ∀ (n : ℕ) (init : List ℕ),
      evZ ((List.replicate n a).foldl (pmul · · q) init) X = evZ init X * evZ a X ^ n
  | 0, init => by simp
  | n + 1, init => by
    rw [List.replicate_succ, List.foldl_cons, evZ_foldl_pmul X a n, evZ_pmul, pow_succ]; ring

lemma evZ_ppow (a : List ℕ) (n : ℕ) (X : ZMod q) : evZ (ppow a n q) X = evZ a X ^ n := by
  rw [ppow, evZ_foldl_pmul]; simp

/-- A list evaluates to the sum of its coefficients times powers. -/
lemma evZ_eq_sum (X : ZMod q) : ∀ l : List ℕ,
    evZ l X = ∑ i ∈ range l.length, (l.getD i 0 : ZMod q) * X ^ i
  | [] => by simp
  | c :: l => by
    rw [evZ_cons, evZ_eq_sum X l, List.length_cons, sum_range_succ', sum_mul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    congr 1; refine sum_congr rfl fun i _ => ?_; ring

lemma evZ_eq_sum7 (X : ZMod q) (l : List ℕ) (hl : l.length ≤ 7) :
    evZ l X = ∑ i ∈ range 7, (l.getD i 0 : ZMod q) * X ^ i := by
  rw [evZ_eq_sum, sum_subset (range_subset_range.mpr hl)]
  intro i hi7 hil
  rw [List.getD_eq_default _ _ (by simpa using hil)]; simp

/-- A list of length 7, written out. -/
lemma list7 {α : Type*} {l : List α} (h : l.length = 7) :
    ∃ c0 c1 c2 c3 c4 c5 c6, l = [c0, c1, c2, c3, c4, c5, c6] := by
  match l, h with
  | [c0, c1, c2, c3, c4, c5, c6], _ => exact ⟨_, _, _, _, _, _, _, rfl⟩

/-- The checker's `F` evaluates to `Σₖ fₖ (x₋X − x₊)ᵏ (X − 1)⁶⁻ᵏ`. -/
lemma evZ_evenModel (hq : 0 < q) {f : List ℤ} (hf : f.length = 7) (xp xm : ℕ) (hxp : xp < q)
    (X : ZMod q) : evZ (evenModel f xp xm q) X = ∑ k ∈ range 7,
      (f.getD k 0 : ZMod q) * ((xm : ZMod q) * X - xp) ^ k * (X - 1) ^ (6 - k) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, rfl⟩ := list7 hf
  have hneg : (((q - xp) % q : ℕ) : ZMod q) = -xp := by
    rw [ZMod.natCast_mod, Nat.cast_sub hxp.le, ZMod.natCast_self, zero_sub]
  have hm1 : (((q - 1 : ℕ)) : ZMod q) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hlin : evZ [(q - xp) % q, xm] X = (xm : ZMod q) * X - xp := by
    simp only [evZ_cons, evZ_nil, hneg]; ring
  have hlin1 : evZ [q - 1, 1] X = X - 1 := by simp only [evZ_cons, evZ_nil, hm1]; push_cast; ring
  simp only [evenModel, List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil,
    evZ_padd, evZ_pmul, evZ_pscale, evZ_ppow, hlin, hlin1, evZ_nil, ofInt_cast _ hq]
  simp [sum_range_succ]

end Fermat433.Sieve
