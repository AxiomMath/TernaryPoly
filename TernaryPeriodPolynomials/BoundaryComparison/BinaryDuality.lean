module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FarePeriod

@[expose] public section


/-!
# Binary duality for `GL₂(ℤ)`: the dual Farey tree, `H₁(GL₂(ℤ), Sym^d)` and the period space

Formalized by Claude Sonnet 5.5.

**Statement.**  Let `Γ = GL₂(ℤ)` and let `Sym^d` be the space of binary forms of degree `d` with the integral action
`integralAction d 0` (no determinant twist).  Mathlib's `H₁(Γ, Sym^d) = groupHomology (Dplain d) 1` is `ℚ`-linearly isomorphic
to `periodSpace d`, the space of homogeneous polynomials satisfying the four literal binary period equations
(symmetric, separately odd, `q(x,y) - q(x-y,y) + q(x,x-y) = 0`), by reading off the coefficient at the standard oriented
edge of the dual Farey tree (`periodEquivHomology`, `edge2_range`).

**By-products** (all over `ℚ`, for an arbitrary `ℚ`-representation `M` of `GL₂(ℤ)`).

* `ofMulAction_projective'`: a permutation representation `ℚ[X]` with finite stabilizers is projective.
* `isZero_groupHomology_two_le'`: `Hₙ(GL₂(ℤ), M) = 0` for `n ≥ 2` (the dual Farey tree is a projective resolution of length one).
* `edge2_injective'`, `edge2_isEdgeCoeff'`, `edge2_surjective_of'`: `H₁(Γ, M)` is the space of vectors fixed by the stabilizer of
  the standard edge, odd under the edge swap, and annihilated by the norm over the triangle stabilizer.
* `isEdgeCoeff_iff'`: these conditions are `w b = b`, `(-1) b = b`, `sOne b = -b`, `b + ρ b + ρ² b = 0`.

**Scope.**  Untwisted coefficients.  The determinant twist of the plane coefficient and the comparison with the
Hom-model `kappa` are not part of this file.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.BinaryDuality

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPoly.SinglePoleCoordinate TernaryPoly.OrdinaryResiduePeriod

theorem ofMulAction_projective' {Γ X : Type} [Group Γ] [MulAction Γ X] (k : Type) [Field k] [CharZero k]
    (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) :
    CategoryTheory.Projective (Rep.ofMulAction k Γ X) :=
  TernaryPeriodPolynomials.Argument.BinaryDuality.ofMulAction_projective hfin

theorem isZero_groupHomology_two_le' (M : Rep ℚ IntegralGL) (n : ℕ) :
    CategoryTheory.Limits.IsZero (groupHomology M (n + 2)) :=
  isZero_groupHomology_two_le M n

theorem edge2_injective' (M : Rep ℚ IntegralGL) : Function.Injective (edge2 M) :=
  edge2_injective M

theorem edge2_isEdgeCoeff' (M : Rep ℚ IntegralGL) (x : groupHomology M 1) : IsEdgeCoeff M (edge2 M x) :=
  edge2_isEdgeCoeff M x

theorem edge2_surjective_of' (M : Rep ℚ IntegralGL) {b : M} (hb : IsEdgeCoeff M b) : ∃ x, edge2 M x = b :=
  edge2_surjective_of (M := M) hb

theorem isEdgeCoeff_iff' (M : Rep ℚ IntegralGL) (b : M) : IsEdgeCoeff M b ↔
    M.ρ wSwap b = b ∧ M.ρ mI b = b ∧ M.ρ sOne b = -b ∧ b + M.ρ rho b + M.ρ rho2 b = 0 :=
  isEdgeCoeff_iff M b

/-- **Periods versus homology.**  The standard-edge coefficients of `H₁(GL₂(ℤ), Sym^d)` are the period space. -/
theorem edge2_range (d : ℕ) : LinearMap.range (edge2 (Dplain d)) = periodSpace d :=
  range_edge2_Dplain d

/-- `H₁(GL₂(ℤ), Sym^d) ≃ periodSpace d`, by the coefficient at the standard edge of the dual Farey tree. -/
def periodEquivHomology' (d : ℕ) : groupHomology (Dplain d) 1 ≃ₗ[ℚ] periodSpace d :=
  periodEquivHomology d

theorem periodEquivHomology'_apply (d : ℕ) (x : groupHomology (Dplain d) 1) :
    ((periodEquivHomology' d x : periodSpace d) : BinaryV d) = edge2 (Dplain d) x :=
  rfl

end TernaryPeriodPolynomials.Argument.Statements.BinaryDuality
