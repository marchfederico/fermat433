# Sieve certificate

An independent re-check of the Mordell–Weil sieve (PROOF.md §C.3, Proposition 6.2 of the paper) for
the curve B⁻: y² = −C₃(x). The original sieve is `step4_sieve.gp`, run in PARI/GP. Here the same
conclusion is reached from a small set of exact inputs, by code that shares nothing with PARI.

## What the sieve claims

The quadratic Chabauty step leaves 524 candidates on B⁻(ℚ₄₉₉), each with a coefficient vector
a(z) ∈ ℤ₄₉₉². The sieve removes every one except the four known points, using two primes of L:
- the prime above q = 997 given by t ↦ 35 removes 518 candidates;
- the prime above q = 12973 given by t ↦ 775 removes 2 more.

The other 22 primes in `logs/step4_sieve.log` remove nothing, so the certificate uses only these two.

## The files

| file | what it does |
|---|---|
| `emit.gp` | Exports the exact inputs from PARI: the field L, the fixed points x± of the involution as elements of L, the two primes, and the 524 candidate vectors mod 499. It runs in under a second. |
| `inputs.txt` | Those inputs, as text. |
| `check.py` | An independent checker in plain Python, with no PARI and no libraries. It runs in under a second. |
| `emit_lean.py` | Writes `lean/Fermat433/Sieve/Data.lean`: the inputs plus a removal witness for each removed candidate (see below). |
| `../lean/Fermat433/Sieve/Check.lean` | The Lean checker. |
| `../lean/Fermat433/Sieve/Theorem.lean` | The theorem `sieve_B_minus`, proved by evaluating the checker in Lean's kernel, plus tests that spoiled witnesses are rejected. |

Both checkers start from `inputs.txt` and recompute everything else themselves:
- they reduce L at the prime and build the quotients E₁, E₂;
- they count E₁(𝔽_q) and E₂(𝔽_q) by brute force, and check that the 499-parts are cyclic of order 499;
- they compute the images of the generators and each candidate's target (T₁, T₂).

Neither uses PARI's generators, discrete logarithms or allowed sets. The sieve's verdict does not
depend on those choices, so this is a genuine second computation, not a replay. The two checkers
also differ from each other in how they decide that a candidate is removed:

- **`check.py` works forwards**, like PARI. It enumerates all of X(𝔽_q), maps every point to the
  499-parts, and removes a candidate whose target is not among the images.
- **The Lean checker works backwards**, from a witness. Multiplication by c₁ = #E₁(𝔽_q)/499 maps
  E₁(𝔽_q) onto its 499-part, and every fibre has exactly c₁ points. A list of c₁ distinct points Q
  with c₁·Q = T₁ is therefore the whole fibre over T₁. Each Q comes from at most two points of X:
  in the even model Y² = AX⁶ + BX⁴ + CX² + D they are (±√(u/A), v/A). The candidate is removed if
  none of those points is sent to T₂ on E₂.

  The certificate supplies each fibre and the square roots, and the checker verifies all of them.
  That is about 50 points per removed candidate at q = 12973, instead of all 12,974 points of
  X(𝔽_q). It is why the kernel check takes about 35 seconds rather than not finishing.

## Result

All three implementations agree exactly:

| | PARI (`step4_sieve.gp`) | Python (`check.py`) | Lean (`sieve_B_minus`) |
|---|---|---|---|
| q = 997: removed, left | 518, 6 | 518, 6 | 518, 6 |
| q = 12973: removed, left | 2, 4 | 2, 4 | 2, 4 |
| survivors, a mod 499 | (1,0), (−1,0), (0,1), (0,−1) | same | same |

The Lean result is a theorem, checked by the kernel in about 35 seconds:

```lean
theorem sieve_B_minus : run inputs certs = some [(1, 0), (498, 0), (0, 1), (0, 498)]
```

It depends only on the axiom `propext`; in particular it does not use `native_decide`, so Lean's
compiler is not trusted. CI rebuilds it and checks the axioms on every change. `Theorem.lean` also
spoils witnesses in five ways (a missing fibre point, a repeated one, a wrong square root, a point
off the curve, a wrong prime of L) and checks that each is rejected.

The survivors are the four known points P₁, ιP₁, P₂, ιP₂. That they survive is also a consistency
check on the exported conventions: if x₊ and x₋ were swapped, or the generators mismatched, the
known points would be removed too.

## What this does and does not establish

**Established:** given the 524 candidate vectors, the finite arithmetic of the sieve is right. The
reductions, group orders, cyclicity of the 499-parts, the enumeration of X(𝔽_q) and the sieving
condition were all recomputed without PARI.

**Not established here:**
- that the candidate vectors are the zeros of the quadratic Chabauty function (Proposition 6.1);
- that the sieving condition is the right one (Proposition 6.2);
- the C⁺ half and the p = 1459 rerun, which have the same structure and are a straightforward
  extension.

**The soundness proof.** `sieve_B_minus` says that a program returns the four survivors.
`sieve_B_minus_sound` (in `lean/Fermat433/Sieve/Sound/Main.lean`) turns that into mathematics.
For each of the 520 removed candidates a = (a₁, a₂), there is a prime q ∈ {997, 12973} at which
no point P of X(𝔽_q) satisfies both

  c₁·φ₁(P) = a₁·c₁·φ₁(P₁) + a₂·c₁·φ₁(P₂) on E₁  and  c₂·φ₂(P) = a₁·c₂·φ₂(P₁) + a₂·c₂·φ₂(P₂) on E₂,

where P₁ = (1, 1), P₂ = (−1, 15) and cᵢ = #Eᵢ(𝔽_q)/499. The curves Eᵢ, their points and group law
are Mathlib's (`WeierstrassCurve.Affine.Point` over `ZMod q`). The maps φᵢ are given by their
formulas: the change of variable X = (x − x₊)/(x − x₋), Y = y(X − 1)³ to the even model, then
(AX², AY) and (D/X², DY/X³). X(𝔽_q) includes the points at infinity and the special points
x = x±. The theorem depends only on Lean's three standard axioms.

The proof is in four layers in `lean/Fermat433/Sieve/Sound/`:

| layer | statement | status |
|---|---|---|
| 1. arithmetic (`Arith.lean`) | `powMod`, `inv`, `sub`, `ofInt` compute exponentiation, inverses, subtraction and casts in `ZMod q`; `euler` returning `q − 1` means "not a square" | proved |
| 2. group law (`Curve.lean`) | `Curve.add` and `Curve.mul` are Mathlib's addition and `n • ·`; points passing `onCurve` are points; `disc ≠ 0` gives `Δ ≠ 0` | proved |
| 3. counting (`Count.lean`, `Fibre.lean`) | `Curve.order` is the number of points (`card_eq_order`); in a group of order `499c` with `499 ∤ c`, `c` distinct points of a fibre of `c • ·` are the whole fibre (`mem_of_fibre`) | proved |
| 4. the sieve (`Poly.lean`, `Geometry.lean`, `Bridge.lean`, `Sieve.lean`, `Main.lean`) | the list polynomials compute `F`; points of `X` land on the even model and on `E₁`, `E₂`; the checker's `phi` and fibre test are correct; `sievePrime` returning `some` implies the statement above | proved |

Writing layer 4 exposed one real gap in the checker, now closed. Fibre points were not required to
be reduced mod q, so a certificate could have listed (x, y) and (x + q, y) as two "distinct" points.
The checker now rejects this, and `Theorem.lean` tests that it does. A few other facts the proof
needs (F has at most seven coefficients, A = f(x₋), D = f(x₊), values reduced mod q, q > 15) are
also checked at run time rather than derived.

**What is still not proved in Lean:**
- that the 524 candidate vectors are the zeros of the quadratic Chabauty function (§6,
  Proposition 6.1);
- that the sieve condition above is the right one, i.e. that a rational point's coefficient vector
  must satisfy it (Proposition 6.2): this links φᵢ over 𝔽_q to the maps over L and to J(ℚ);
- the C⁺ half and the p = 1459 rerun, which have the same structure.

## Reproducing

From the repository root:

    gp -q sieve_cert/emit.gp          # rewrites inputs.txt (needs PARI/GP 2.17)
    python3 sieve_cert/check.py
    python3 sieve_cert/emit_lean.py   # rewrites lean/Fermat433/Sieve/Data.lean (about 5 seconds)
    cd lean && lake build             # includes the kernel check of sieve_B_minus
