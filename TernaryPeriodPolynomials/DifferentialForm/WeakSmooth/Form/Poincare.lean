module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.LowDifferential
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Poincare
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CoordinateBoxes

@[expose] public section


/-! Actual weak one-form Poincare for genuine polynomial coefficient-valued alternating forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialFormCoordinates PolynomialFormMetric PolynomialCoefficientMetric SymmetricSpaceCharts
open SmoothLocalDeRham

/-- Scalar compact-test Poincare implies exactness of actual polynomial-valued one-form currents. -/
theorem formWeakOneExact_of_scalar (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : ScalarWeakOneExact Ω) (W : FormWeak n 1 Ω) (hW : formWeakExterior n 1 Ω W = 0) :
    ∃ T : FormWeak n 0 Ω, formWeakExterior n 0 Ω T = W := by
  let e : Coefficients n ≃ₗ[ℝ] (Index n 0 → ℝ) :=
    zeroEquiv.toLinearEquiv.trans (coordinates n 0).toLinearEquiv
  obtain ⟨T, hT⟩ := valuedWeakOneExact_of_scalar Ω hΩ e (formWeakOneValue n Ω W)
    ((formWeakExterior_one_eq_zero_iff n Ω W).mp hW)
  refine ⟨zeroFormWeak n Ω T, formWeakOneValue_injective n Ω ?_⟩
  exact (formWeakExterior_zero n Ω T).trans hT

/-- On every actual affine coordinate box, every closed actual polynomial-valued weak one-form
has an actual polynomial-valued scalar-current primitive. -/
theorem coordinateTestBox_formWeakOneExact (n : ℕ)
    (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates)
    (W : FormWeak n 1 (coordinateTestBox e a))
    (hW : formWeakExterior n 1 (coordinateTestBox e a) W = 0) :
    ∃ T : FormWeak n 0 (coordinateTestBox e a),
      formWeakExterior n 0 (coordinateTestBox e a) T = W :=
  formWeakOneExact_of_scalar n (coordinateTestBox e a)
    (coordinateTestBox_weakOneExact e a) W hW

end TernaryPoly.PolynomialFormWeakSmooth
