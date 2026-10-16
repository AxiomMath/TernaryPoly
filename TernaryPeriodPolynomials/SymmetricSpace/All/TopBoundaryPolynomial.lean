module

public import TernaryPeriodPolynomials.SymmetricSpace.All.TopBoundary
public import TernaryPeriodPolynomials.Polynomial.GLAction

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceAllTopBoundary
open CompactInteriorRelativeBoundary
open CategoryTheory IntegralGL3Congruence PolynomialGLAction
open SingularLocalSupport SymmetricSpaceBordifiedCohomology SymmetricSpaceBoundaryDuality

/-- The literal homogeneous polynomial representation restricted to the actual principal-six
arithmetic group, retaining the specified determinant twist. -/
abbrev polynomialCoefficients (n : ℕ) (e : ℤ) : Rep.{0} ℚ principalSix :=
  Rep.res principalSix.subtype (Rep.of (integralAction n e))

/-- The precise remaining positive-degree analytic vanishing obligation. This definition
states a proposition; it does not assert or assume that the proposition has been proved. -/
def PositivePolynomialInnerVanishing : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (e : ℤ), compactForget interiorCover (polynomialCoefficients n e) 2 = 0

/-- The positive-degree vanishing obligation is exactly all-top-boundary for the same
literal polynomial coefficient systems. This equivalence does not discharge that obligation. -/
theorem positivePolynomialInnerVanishing_iff_all_top_boundary :
    PositivePolynomialInnerVanishing ↔
      ∀ (n : ℕ), 0 < n → ∀ (e : ℤ),
        Function.Surjective (boundaryToGroup (polynomialCoefficients n e) 3).hom := by
  unfold PositivePolynomialInnerVanishing
  simp only [boundaryToGroup_surjective_iff_compactForget_zero]

/-- A proof of the explicitly isolated analytic obligation would give actual boundary
surjectivity in every positive polynomial degree, without changing coefficients. -/
theorem polynomial_boundary_surjective_of_inner_vanishing
    (h : PositivePolynomialInnerVanishing) (n : ℕ) (hn : 0 < n) (e : ℤ) :
    Function.Surjective (boundaryToGroup (polynomialCoefficients n e) 3).hom :=
  (boundaryToGroup_surjective_iff_compactForget_zero (polynomialCoefficients n e)).mpr (h n hn e)

end TernaryPoly.SymmetricSpaceAllTopBoundary
