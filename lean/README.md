# Lean formalization

A Lean 4 / Mathlib proof of the theorem of PROOF.md, **conditional on the inputs Mathlib cannot yet
supply**. The main theorem is

```lean
theorem fermat433 (H : Inputs) (x y z : ℤ) (hp : Primitive x y z) :
    x ^ 4 + 2 * y ^ 3 + z ^ 3 = 0 ↔ (x, y, z) ∈ solutions
```

where `solutions` lists (±1, 0, −1), (±1, −1, 1), (±43, −203, 237), and `Inputs` (in
`Fermat433/Statement.lean`) is a structure of seven hypotheses. Every hypothesis is stated explicitly
and none is an `axiom`, so `#print axioms fermat433` reports only Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). There is no `sorry` and no `native_decide`.

## What is assumed (`Inputs`)

| field | statement | established in |
|---|---|---|
| `descent` | a primitive solution has z + yθ = −εᵏγ⁴, γ ∈ ℤ[∛2], 0 ≤ k < 4 | Lemma A.1 (h_K = 1, units ⟨−1, ε⟩) |
| `A_minus`, `B_plus`, `C_minus` | y² = −(x⁶ − 40x³ − 32), y² = C₃(x), y² = −2C₃(x) have no rational points | Prop. B.1 |
| `A_plus` | an affine rational point of y² = x⁶ − 40x³ − 32 has x = −1 | Prop. B.2 |
| `B_minus` | an affine rational point of y² = −C₃(x) has x ∈ {1, −1} | Part C, Prop. D.1 |
| `C_plus` | an affine rational point of y² = 2C₃(x) has x ∈ {6/5, 2} | Part C, Prop. D.2 |

Only the x-coordinates of affine points are used; the points at infinity correspond to the tangent
direction of the conic and are handled inside the proof.

## What is proved

Everything between Lemma A.1 and the six curves, and everything from the curves back to the
solutions:

- `ZTheta.lean`: ℤ[∛2] in coordinates, its multiplication and norm, N(uv) = N(u)N(v).
- `Reduction.lean`:
  - `sq_norm_eq`, `descended`: x² = N(γ²); γ² has no prime factor, because one would divide x, y and z.
  - `odd_r0`: γ is a unit at 2, i.e. a is odd (Lemma A.2): otherwise γ = θγ′ and 2 divides x, y, z.
  - `not_k23`: k = 2, 3 are impossible, since the θ²-coordinate of −εᵏγ⁴ is odd. The check runs by
    `decide` over (ℤ/2)³.
  - `case_k0`, `case_k1`: the conics Q_k(δ) = 0 and the twist set of Lemma A.3. These show that X = d₁/d₂
    is a rational point on exactly one of A±, B±, C±. The curves' rational points then recover
    (x, y, z) as in Part E; (−1, ±15) and (2, ±12) on B⁻ and C⁺, and (−1, ±3) on A⁺, give triples
    divisible by 3.
- `Lemmas.lean`: the square-class lemma behind the twist set (d² = uv with gcd(u, v) | 2 forces
  u ∈ {±m², ±2m²}), and small facts about primes.
- `Main.lean`: the theorem, plus checks that the six triples are solutions and are primitive.

## The sieve certificate

`Fermat433/Sieve/` checks the Mordell–Weil sieves for B⁻ and C⁺ (Proposition 6.2 of the paper),
at p = 499 and in the rerun at p = 1459, without PARI, in two steps:

- `sieve_B_minus`, `sieve_C_plus`, `sieve_B_minus_p1459`, `sieve_C_plus_p1459`: the checker,
  evaluated in Lean's kernel (`decide +kernel`, axioms: `propext` only), returns exactly the four
  known points in each case.
- The corresponding `…_sound` theorems (in `Sieve/Sound/`, all from `run_sound`): the checker is
  sound, so every other candidate is ruled out at one of the sieving primes by a statement about
  Mathlib elliptic curves over `ZMod q` (`SieveRemoves`).

It is not connected to `fermat433`: the candidate lists and the sieve condition itself
(Propositions 6.1–6.2) remain outside Lean. See `../sieve_cert/README.md`.

## Building

Install [elan](https://github.com/leanprover/elan), then from this directory:

    lake exe cache get     # download the prebuilt Mathlib (~6.6 GB unpacked)
    lake build             # about two minutes after the cache is in place (~8 GB of memory)
    lake env lean scripts/axioms.lean

The toolchain and the Mathlib version are pinned in `lean-toolchain` and `lake-manifest.json`.

## What it would take to remove a hypothesis

`descent` is the most approachable. Mathlib has Minkowski-bound criteria for 𝓞_K to be a PID
(`NumberField.isPrincipalIdealRing_of_isPrincipal_of_norm_le` and its variants). Proving
𝓞_K = ℤ[∛2], the unit group ⟨−1, ε⟩ (which needs a certified bound on the regulator) and the
coprimality of the conjugates would still be substantial work. The other six need Jacobians of
genus-2 curves, 2-descent and Chabauty-type arguments, none of which exists in Mathlib today.
