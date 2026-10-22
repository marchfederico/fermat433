/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Sieve.Data

/-!
# The sieve for `B⁻`, checked by the kernel

Of the 524 candidates left by quadratic Chabauty on `B⁻ : y² = −C₃(x)` at `p = 499`, the primes of
`L` above 997 and 12973 remove all but the four with `a(z) ≡ (±1, 0), (0, ±1) (mod 499)`, which are
the known points `(1, ±1)` and `(−1, ±15)`. `decide +kernel` evaluates the checker in Lean's kernel,
so the proof does not depend on the compiler (`#print axioms` reports only `propext`).

See `Fermat433.Sieve.Check` for exactly what is checked, and what is not.
-/

namespace Fermat433.Sieve

set_option maxRecDepth 200000 in
theorem sieve_B_minus : run inputs certs = some [(1, 0), (498, 0), (0, 1), (0, 498)] := by
  decide +kernel

/-! The checker must reject bad witnesses. Each test spoils the first removal at `q = 12973`
(candidate `(77, 227)`), which must then survive; a wrong prime of `L` must fail outright. -/

private instance : Inhabited Removal := ⟨⟨(0, 0), []⟩⟩

private def spoil (f : List (Pt × Nat) → List (Pt × Nat)) : List PrimeCert :=
  let R := cert12973.removals.head!
  [cert997, { cert12973 with removals := { R with fibre := f R.fibre } :: cert12973.removals.tail }]

private def kept := some [(1, 0), (498, 0), (77, 227), (0, 1), (0, 498)]

-- a fibre point missing
#guard run inputs (spoil List.tail) == kept
-- a fibre point repeated
#guard run inputs (spoil fun l => l.take 1 ++ l.drop 2 ++ l.take 1) == kept
-- a wrong square root
#guard run inputs (spoil fun l => l.take 1 |>.map (fun (Q, w) => (Q, (w + 1) % 12973)) |>.append (l.drop 1)) == kept
-- a fibre point not on the curve
#guard run inputs (spoil fun l => (l.take 1 |>.map fun (_, w) => (Pt.pt 1 1, w)) ++ l.drop 1) == kept
-- a fibre point repeated in unreduced form `(x + q, y)`
#guard run inputs (spoil fun l => match l with
  | (Pt.pt x y, w) :: rest => (Pt.pt x y, w) :: (rest.take (rest.length - 1)) ++
      [(Pt.pt (x + 12973) y, w)]
  | l => l) == kept
-- a wrong prime of L
#guard run inputs [cert997, { cert12973 with r := 776 }] == none

end Fermat433.Sieve
