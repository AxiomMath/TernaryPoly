module

public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Basic
public import TernaryPeriodPolynomials.DifferentialForm.Compact.Adjoint
public import TernaryPeriodPolynomials.SymmetricSpace.All.TopBoundaryPolynomial
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.PropC1Assembly
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeFour

@[expose] public section


/-! Target: Proposition C.1 (`ar:prop:coercivity`) of the paper. -/

open TernaryPoly TernaryPoly.PolynomialFormHilbert TernaryPoly.SmoothCoveringDeRham
open TernaryPoly.PolynomialCoefficientMetric TernaryPoly.SymmetricSpaceAllTopBoundary
open TernaryPoly.CompactInteriorRelativeBoundary TernaryPoly.SymmetricSpaceBordifiedCohomology

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Proposition C.1.** For every `n > 0` there is `c_n > 0` such that every compactly supported
smooth form `ω` of every degree on the arithmetic quotient, with coefficients in the degree-`n`
polynomial representation `Sym^n((ℝ³)*)` and its flat-bundle metric, satisfies
`‖Dω‖² + ‖D*ω‖² ≥ c_n ‖ω‖²` (`ar:eq:coercivity`); consequently
`H²_c(X_Γ, E) → H²(X_Γ, E)` is zero for every determinant twist `E = E_{n,e}`.

The formalization fixes the project's neat cover (the principal congruence subgroup of level six
inside the level group) on which the forms live; the constant does not depend on the degree. -/
theorem coercivity_compact_support (n : ℕ) (hn : 0 < n) :
    (∃ c : ℝ, 0 < c ∧
      (∀ a : Core n 0, c * ‖inclusion n 0 a‖ ^ 2 ≤
        ‖inclusion n 1 (compactDifferential (deckRepresentation n) isOpen_univ 0 a)‖ ^ 2) ∧
      ∀ (k : ℕ) (a : Core n (k + 1)), c * ‖inclusion n (k + 1) a‖ ^ 2 ≤
        ‖inclusion n k (PolynomialFormCoordinates.compactAdjoint n k a)‖ ^ 2 +
          ‖inclusion n (k + 2)
            (compactDifferential (deckRepresentation n) isOpen_univ (k + 1) a)‖ ^ 2) ∧
    ∀ e : ℤ, compactForget interiorCover (polynomialCoefficients n e) 2 = 0 :=
  TernaryPeriodPolynomials.Argument.Coercivity.prop_C_1_of_degree_four n hn
    (TernaryPeriodPolynomials.Argument.Coercivity.norm_differential_energy_coercive_degree_four hn)

end TernaryPeriodPolynomials
