/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/

/-!
# A checker for the Mordell–Weil sieve certificate (Proposition 6.2)

The sieve of §6 removes every zero of the quadratic Chabauty function on `X = B⁻ : y² = −C₃(x)`
(and on `X = C⁺ : y² = 2C₃(x)`) except the four known points. Each zero `z` comes with a vector
`a(z) = (a₁, a₂) ∈ ℤ_ℓ²` (ℓ = p = 499, or 1459 in the rerun) such that, at a prime `𝔮` of `L` of
degree one where `ℓ ∥ #E_i(𝔽_q)`, the ℓ-parts satisfy `c_i·φ_i(z̄) = a₁·c_i·φ_i(P̄₁) + a₂·c_i·φ_i(P̄₂)`
on both quotients `E₁, E₂`, where `c_i = #E_i(𝔽_q)/ℓ` and `P₁, P₂` are the generators (`(1, 1)`, `(−1, 15)` on `B⁻`;
`(6/5, 172/125)`, `(2, 12)` on `C⁺`). A zero is removed when no point of `X(𝔽_q)` has that image.

`run` recomputes this from the exact inputs: it reduces `L` at `𝔮`, builds `E₁, E₂`, counts their
points and checks that their ℓ-parts are cyclic of order ℓ. To remove a candidate it does not
enumerate `X(𝔽_q)`; it works backwards from the target `(T₁, T₂)`. Multiplication by `c₁` maps
`E₁(𝔽_q)` onto its ℓ-part with every fibre of size exactly `c₁`, so a list of `c₁` distinct points
`Q` with `c₁·Q = T₁` is the whole fibre. Each `Q` comes from at most two points of `X`, the two
square roots `±X` of `u/A` in the even model `Y² = AX⁶ + BX⁴ + CX² + D`. The candidate is removed
when none of them is sent to `T₂` by `c₂·φ₂`. The certificate supplies the fibre and the square
roots; the checker verifies every one, and a false witness makes it fail.

What is *not* proved here: that the sieve condition above is the right one (that is Proposition 6.2
of the paper), and that the candidate vectors are the zeros of the quadratic Chabauty function (§6,
Proposition 6.1). This file only checks the finite arithmetic. `run` is ordinary code; the theorem
in `Fermat433.Sieve.Theorem` evaluates it in the kernel.
-/

namespace Fermat433.Sieve

/-- The exact inputs: the sextic `f` of `X : y² = f(x)` (lowest degree first), the generators
`P₁, P₂` with rational coordinates `(num, den)`, the defining polynomial of `L`, the fixed points
`x±` of the involution as polynomials in the generator of `L` with rational coefficients, and the
candidate vectors `a(z) mod ℓ`, where `ℓ` is the prime of the quadratic Chabauty computation. -/
structure Inputs where
  ell : Nat
  f : List Int
  p1 : (Int × Nat) × (Int × Nat)
  p2 : (Int × Nat) × (Int × Nat)
  pl : List Int
  xp : List (Int × Nat)
  xm : List (Int × Nat)
  cands : List (Nat × Nat)

/-! ### Arithmetic modulo `q` on representatives `0 ≤ a < q` -/

def powModAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, q => 1 % q
  | fuel + 1, b, e, q =>
    if e = 0 then 1 % q else
      let h := powModAux fuel (b * b % q) (e / 2) q
      if e % 2 = 1 then h * b % q else h

def powMod (b e q : Nat) : Nat := powModAux 64 (b % q) e q

def inv (a q : Nat) : Nat := powMod a (q - 2) q

def ofInt (z : Int) (q : Nat) : Nat := (z % (q : Int)).toNat

def sub (a b q : Nat) : Nat := (a + q - b % q) % q

/-- Euler's criterion: `1` for a nonzero square, `q − 1` for a non-square, `0` for `0`. -/
def euler (a q : Nat) : Nat := (a % q) ^ ((q - 1) / 2) % q

def isPrime (q : Nat) : Bool :=
  2 ≤ q && (List.range q).all fun d => d < 2 || q < d * d || q % d != 0

/-- Evaluate a polynomial (lowest degree first) at `x`. -/
def evalPoly (cs : List Nat) (x q : Nat) : Nat := cs.foldr (fun c acc => (acc * x + c) % q) 0

/-- Evaluate an element of `L` (rational coefficients) at `t = r`. -/
def evalL (cs : List (Int × Nat)) (r q : Nat) : Nat :=
  evalPoly (cs.map fun (n, d) => ofInt n q * inv (d % q) q % q) r q

def denomsOk (cs : List (Int × Nat)) (q : Nat) : Bool := cs.all fun (_, d) => d % q != 0

/-! ### Polynomials over `𝔽_q` (lowest degree first) -/

def padd (a b : List Nat) (q : Nat) : List Nat :=
  match a, b with
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => (x + y) % q :: padd a b q

def pscale (c : Nat) (a : List Nat) (q : Nat) : List Nat := a.map fun x => c * x % q

def pmul (a b : List Nat) (q : Nat) : List Nat :=
  match a with
  | [] => []
  | x :: a => padd (pscale x b q) (0 :: pmul a b q) q

def ppow (a : List Nat) (n q : Nat) : List Nat := (List.replicate n a).foldl (pmul · · q) [1]

def trim (a : List Nat) : List Nat := (a.reverse.dropWhile (· == 0)).reverse

def pderiv (a : List Nat) (q : Nat) : List Nat :=
  (a.zipIdx.drop 1).map fun (c, i) => c * i % q

/-- Remainder of `a` by a nonzero trimmed `b`. -/
def pmodAux : Nat → List Nat → List Nat → Nat → List Nat
  | 0, a, _, _ => a
  | fuel + 1, a, b, q =>
    let a := trim a
    if a.length < b.length then a else
      let s := a.length - b.length
      let c := a.getLast! * inv b.getLast! q % q
      let sub := (List.replicate s 0) ++ pscale ((q - c) % q) b q
      pmodAux fuel (padd a sub q) b q

def pgcdAux : Nat → List Nat → List Nat → Nat → List Nat
  | 0, a, _, _ => a
  | fuel + 1, a, b, q =>
    let b := trim b
    if b.isEmpty then trim a else pgcdAux fuel b (pmodAux (a.length + 1) a b q) q

/-- `f` is squarefree of degree 6 modulo `q`. -/
def squarefree (f : List Nat) (q : Nat) : Bool :=
  (trim f).length == 7 && (pgcdAux 16 f (pderiv f q) q).length == 1

/-! ### Elliptic curves `y² = x³ + a₂x² + a₄x + a₆` over `𝔽_q` -/

inductive Pt
  | inf
  | pt (x y : Nat)
  deriving DecidableEq

/-- The curve `y² = x³ + a₂x² + a₄x + a₆`; the modulus `q` is passed to each operation. -/
structure Curve where
  a2 : Nat
  a4 : Nat
  a6 : Nat

namespace Curve

def rhs (E : Curve) (q x : Nat) : Nat := (x * x % q * x + E.a2 * x % q * x + E.a4 * x + E.a6) % q

def onCurve (E : Curve) (q : Nat) : Pt → Bool
  | .inf => true
  | .pt x y => y * y % q == E.rhs q x

/-- The discriminant of the cubic, up to a unit: `−4a₂³a₆ + a₂²a₄² + 18a₂a₄a₆ − 4a₄³ − 27a₆²`. -/
def disc (E : Curve) (q : Nat) : Nat :=
  let (a, b, c) := (E.a2, E.a4, E.a6)
  let pos := (a * a % q * b % q * b + 18 * a % q * b % q * c) % q
  let neg := (4 * a % q * a % q * a % q * c + 4 * b % q * b % q * b + 27 * c % q * c) % q
  sub pos neg q

def add (E : Curve) (q : Nat) : Pt → Pt → Pt
  | .inf, Q => Q
  | P, .inf => P
  | .pt x1 y1, .pt x2 y2 =>
    if x1 = x2 ∧ (y1 + y2) % q = 0 then .inf else
      let lam :=
        if x1 = x2 then (3 * x1 % q * x1 + 2 * E.a2 % q * x1 + E.a4) % q * inv (2 * y1 % q) q % q
        else sub y2 y1 q * inv (sub x2 x1 q) q % q
      let x3 := (lam * lam % q + 3 * q - E.a2 - x1 - x2) % q
      .pt x3 (sub (lam * sub x1 x3 q % q) y1 q)

def mulAux (E : Curve) (q : Nat) : Nat → Nat → Pt → Pt → Pt
  | 0, _, _, R => R
  | fuel + 1, n, P, R =>
    if n = 0 then R else
      mulAux E q fuel (n / 2) (E.add q P P) (if n % 2 = 1 then E.add q R P else R)

def mul (E : Curve) (q n : Nat) (P : Pt) : Pt := E.mulAux q 64 n P .inf

/-- `#E(𝔽_q) = q + 1 + Σₓ (rhs(x) / q)`. -/
def order (E : Curve) (q : Nat) : Int :=
  (List.range q).foldl (fun acc x =>
    let e := euler (E.rhs q x) q
    if e = 1 then acc + 1 else if e = 0 then acc else acc - 1) ((q : Int) + 1)

end Curve

/-- The witness that a candidate is removed at a prime: the candidate `a`, and the fibre
`{Q : c₁·Q = T₁}` with, for each `Q = (u, v)`, a square root of `u/A` (for `Q = O`, of `f(x₋)`), or
`q` if there is none. -/
structure Removal where
  a : Nat × Nat
  fibre : List (Pt × Nat)

/-- A prime `𝔮 = (q, t − r)` of `L` and the candidates removed there. -/
structure PrimeCert where
  q : Nat
  r : Nat
  removals : List Removal

/-! ### One prime -/

/-- `F(X) = (X − 1)⁶ f((x₋X − x₊)/(X − 1)) = Σₖ fₖ (x₋X − x₊)ᵏ (X − 1)⁶⁻ᵏ`, lowest degree first. -/
def evenModel (f : List Int) (xp xm q : Nat) : List Nat :=
  (f.zipIdx).foldl (fun acc (c, k) =>
    padd acc (pmul (pscale (ofInt c q) (ppow [(q - xp) % q, xm] k q) q)
      (ppow [q - 1, 1] (6 - k) q) q) q) []

/-- The setting at `𝔮`: `x±`, the even sextic `A X⁶ + B X⁴ + C X² + D`, and the two quotients
`E₁ : y² = x³ + Bx² + ACx + A²D`, `E₂ : y² = x³ + Cx² + BDx + AD²`, as in `step3_setup.gp`. -/
structure Setting where
  q : Nat
  ell : Nat
  f : List Nat
  p1 : Nat × Nat
  p2 : Nat × Nat
  xp : Nat
  xm : Nat
  F : List Nat
  A : Nat
  D : Nat
  E1 : Curve
  E2 : Curve

/-- A rational number `num/den` modulo `q`. -/
def ratMod (z : Int × Nat) (q : Nat) : Nat := ofInt z.1 q * inv (z.2 % q) q % q

def setting (I : Inputs) (q r : Nat) : Setting :=
  let xp := evalL I.xp r q
  let xm := evalL I.xm r q
  let F := evenModel I.f xp xm q
  let co := fun i => F.getD i 0
  let (A, B, C, D) := (co 6, co 4, co 2, co 0)
  { q, xp, xm, F, A, D,
    ell := I.ell,
    f := I.f.map (ofInt · q),
    p1 := (ratMod I.p1.1 q, ratMod I.p1.2 q),
    p2 := (ratMod I.p2.1 q, ratMod I.p2.2 q),
    E1 := ⟨B, A * C % q, A * A % q * D % q⟩,
    E2 := ⟨C, B * D % q, A * D % q * D % q⟩ }

/-- Structural facts about the setting that the soundness proof uses: `F` is an even sextic,
`A = f(x₋)`, `D = f(x₊)`, and every value is reduced modulo `q`. -/
def settingOk (S : Setting) (f : List Nat) : Bool :=
  S.F.length ≤ 7 && S.F.getD 1 0 == 0 && S.F.getD 3 0 == 0 && S.F.getD 5 0 == 0 &&
    S.A == evalPoly f S.xm S.q && S.D == evalPoly f S.xp S.q &&
    S.xp < S.q && S.xm < S.q && S.A < S.q && S.D < S.q && S.E1.a2 < S.q && S.E2.a2 < S.q

/-- `(φ₁, φ₂)` of an affine point of `X`. -/
def phi (S : Setting) (x y : Nat) : Pt × Pt :=
  let q := S.q
  if x = S.xm then (.inf, .pt 0 (S.D * y % q))
  else if x = S.xp then (.pt 0 (sub 0 (S.A * y % q) q), .inf)
  else
    let X := sub x S.xp q * inv (sub x S.xm q) q % q
    let Y := y * powMod (sub X 1 q) 3 q % q
    (.pt (S.A * X % q * X % q) (S.A * Y % q),
     .pt (S.D * inv (X * X % q) q % q) (S.D * Y % q * inv (powMod X 3 q) q % q))

/-- No point of `X(𝔽_q)` over `Q ∈ E₁(𝔽_q)` is sent to `T₂` by `c₂·φ₂`, given a square-root
witness `w`. Over `Q = (u, v)` the points of `X` are `(X, Y) = (±√(u/A), v/A)` in the even model;
over `Q = O` they are the points with `x = x₋`, where `φ₂ = (0, D·y)`. -/
def fibreOk (S : Setting) (f : List Nat) (c2 : Nat) (T2 : Pt) (Q : Pt) (w : Nat) : Bool :=
  let q := S.q
  let hit : Pt → Bool := fun P => S.E2.mul q c2 P == T2
  match Q with
  | .inf =>
    let fx := evalPoly f S.xm q
    if w = q then euler fx q == q - 1
    else w * w % q == fx && !hit (.pt 0 (S.D * w % q)) && !hit (.pt 0 (sub 0 (S.D * w % q) q))
  | .pt u v =>
    let s := u * inv S.A q % q
    let Y := v * inv S.A q % q
    let img : Nat → Pt := fun X =>
      if X = 0 then .inf
      else .pt (S.D * inv (X * X % q) q % q) (S.D * Y % q * inv (powMod X 3 q) q % q)
    if w = q then euler s q == q - 1
    else w * w % q == s && !hit (img w) && !hit (img ((q - w) % q))

/-- A checker point with coordinates reduced modulo `q`. -/
def Pt.reduced (q : Nat) : Pt → Bool
  | .inf => true
  | .pt x y => x < q && y < q

/-- The points of a list are pairwise distinct. -/
def distinct : List Pt → Bool
  | [] => true
  | P :: Ps => !Ps.contains P && distinct Ps

/-- The checks at a prime that do not depend on the candidates: `𝔮 = (q, t − r)` is a prime of `L`
of degree one, `X`, `E₁`, `E₂` have good reduction there, and the setting is well formed. -/
def primeOk (I : Inputs) (C : PrimeCert) : Bool :=
  let q := C.q
  let S := setting I q C.r
  I.f.length = 7 && isPrime I.ell && isPrime q && I.ell < q && 15 < q && q < 2 ^ 32 &&
    evalPoly (I.pl.map (ofInt · q)) C.r q = 0 && denomsOk I.xp q && denomsOk I.xm q &&
    squarefree S.f q && settingOk S S.f &&
    S.xp ≠ S.xm && S.A ≠ 0 && S.D ≠ 0 && S.E1.disc q ≠ 0 && S.E2.disc q ≠ 0

/-- The ℓ-parts are cyclic of order `ℓ`, and the cofactors are small. -/
def ordersOk (ell q : Nat) (N1 N2 : Int) : Bool :=
  N1 % ell = 0 && N1 % (ell * ell) ≠ 0 && N2 % ell = 0 && N2 % (ell * ell) ≠ 0 &&
    (N1 / ell).toNat < q && (N2 / ell).toNat < q

/-- The images `cᵢ·φᵢ(P)` of a point of `X`, and the target of a candidate. -/
def imgAt (S : Setting) (c1 c2 : Nat) (P : Pt × Pt) : Pt × Pt :=
  (S.E1.mul S.q c1 P.1, S.E2.mul S.q c2 P.2)

def target (S : Setting) (c1 c2 : Nat) (a : Nat × Nat) : Pt × Pt :=
  let q := S.q
  let G1 := imgAt S c1 c2 (phi S S.p1.1 S.p1.2)
  let G2 := imgAt S c1 c2 (phi S S.p2.1 S.p2.2)
  (S.E1.add q (S.E1.mul q a.1 G1.1) (S.E1.mul q a.2 G2.1),
    S.E2.add q (S.E2.mul q a.1 G1.2) (S.E2.mul q a.2 G2.2))

/-- The removal witness `R` is valid: its fibre is `c₁` distinct reduced points `Q` of `E₁` with
`c₁·Q = T₁`, and no point of `X` over any of them reaches `T₂`. -/
def removedBy (S : Setting) (c1 c2 : Nat) (R : Removal) : Bool :=
  let q := S.q
  let T := target S c1 c2 R.a
  R.a.1 < S.ell && R.a.2 < S.ell && R.fibre.length == c1 && distinct (R.fibre.map Prod.fst) &&
    R.fibre.all fun (Q, w) => Q.reduced q && w ≤ q && S.E1.onCurve q Q &&
      S.E1.mul q c1 Q == T.1 && fibreOk S S.f c2 T.2 Q w

/-- Walk the candidates and the removal witnesses together (the witnesses come in candidate
order): a candidate is dropped when the next witness is for it and is valid. A witness that is for
the candidate but fails is used up, so it only keeps its own candidate. -/
def sieveList (S : Setting) (c1 c2 : Nat) : List (Nat × Nat) → List Removal → List (Nat × Nat)
  | [], _ => []
  | a :: as, [] => a :: as
  | a :: as, R :: Rs =>
    if R.a == a then
      if removedBy S c1 c2 R then sieveList S c1 c2 as Rs else a :: sieveList S c1 c2 as Rs
    else a :: sieveList S c1 c2 as (R :: Rs)

/-- Sieve the candidates still alive at one prime; `none` if any check fails. -/
def sievePrime (I : Inputs) (C : PrimeCert) (alive : List (Nat × Nat)) :
    Option (List (Nat × Nat)) :=
  if primeOk I C then
    let S := setting I C.q C.r
    let N1 := S.E1.order C.q
    let N2 := S.E2.order C.q
    if ordersOk I.ell C.q N1 N2 then
      some (sieveList S (N1 / I.ell).toNat (N2 / I.ell).toNat alive C.removals)
    else none
  else none

/-- Run the sieve over all primes in order. -/
def run (I : Inputs) (certs : List PrimeCert) : Option (List (Nat × Nat)) :=
  certs.foldlM (fun alive C => sievePrime I C alive) I.cands

end Fermat433.Sieve
