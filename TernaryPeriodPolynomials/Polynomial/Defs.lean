module

public import TernaryPeriodPolynomials.Polynomial.Restriction
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix

@[expose] public section


/-!
# Shared polynomial definitions for the paper

Paper:
("Ternary polynomial relations and periods of cusp forms"). The coordinate names
`x, y, z` are `X 0, X 1, X 2`; binary coordinates `X, Y` are `X 0, X 1`.
All definitions are literal formulas over an arbitrary commutative ring; they import
only the paper's polynomial definitions (`TernaryPoly.Paper.Definitions`).
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument

/-- The three-term norm `N = I + A + A²`, with `(Af)(x,y,z) = f(-y, x-y, z)` and
`(A²f)(x,y,z) = f(y-x, -x, z)` (Section 2, equation `eq:polynomial-operators`). -/
def threeTermNorm {R : Type*} [CommRing R] (f : MvPolynomial (Fin 3) R) :
    MvPolynomial (Fin 3) R :=
  f + bind₁ ![-X 1, X 0 - X 1, X 2] f + bind₁ ![X 1 - X 0, -X 0, X 2] f

/-- A polynomial is *alternating* if every permutation of the variables multiplies it by its
sign. -/
def IsAlternating {R : Type*} [CommRing R] (f : MvPolynomial (Fin 3) R) : Prop :=
  ∀ σ : Equiv.Perm (Fin 3), rename σ f = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • f

/-- Every monomial of `f` has odd total degree. -/
def HasOddMonomials {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 3) R) : Prop :=
  ∀ d ∈ f.support, Odd (d 0 + d 1 + d 2)

/-- The universal divisor `D = (x+y+z)(x+y)(y+z)(z+x)` (equation `eq:universal-divisor`). -/
def universalDivisor (R : Type*) [CommRing R] : MvPolynomial (Fin 3) R :=
  (X 0 + X 1 + X 2) * (X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0)

/-- The symmetric degree-ten binary period `q_s = XY(X²-Y²)²(X²-4Y²)(4X²-Y²)` of the
introduction's example. -/
def symmetricTenPeriod (R : Type*) [CommRing R] : MvPolynomial (Fin 2) R :=
  X 0 * X 1 * (X 0 ^ 2 - X 1 ^ 2) ^ 2 * (X 0 ^ 2 - 4 * X 1 ^ 2) * (4 * X 0 ^ 2 - X 1 ^ 2)

/-- The alternating degree-ten binary period `q_a = X²Y²(X²-Y²)³`. -/
def alternatingTenPeriod (R : Type*) [CommRing R] : MvPolynomial (Fin 2) R :=
  X 0 ^ 2 * X 1 ^ 2 * (X 0 ^ 2 - X 1 ^ 2) ^ 3

/-- `f_s = Φ(q_s)`, the cyclic sum `q_s(x,y) + q_s(y,z) + q_s(z,x)`. -/
def symmetricTenSolution (R : Type*) [CommRing R] : MvPolynomial (Fin 3) R :=
  TernaryPoly.Paper.cyclicLift (symmetricTenPeriod R)

/-- `f_a = Φ(q_a)`. -/
def alternatingTenSolution (R : Type*) [CommRing R] : MvPolynomial (Fin 3) R :=
  TernaryPoly.Paper.cyclicLift (alternatingTenPeriod R)

/-- `Π_p = ∏_{0 ≠ λ ∈ 𝔽_p³} (λ₁x + λ₂y + λ₃z)` over a field of characteristic `p`
(Section 7.4). -/
def nonzeroLinearFormProduct (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] :
    MvPolynomial (Fin 3) K :=
  ∏ v ∈ (Finset.univ.filter fun v : Fin 3 → ZMod p => v ≠ 0),
    ∑ i : Fin 3, C (ZMod.castHom (dvd_refl p) K (v i)) * X i

end TernaryPeriodPolynomials.Argument
