module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.ScalarTransport
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Metric
public import TernaryPeriodPolynomials.DifferentialForm.Chart.StrongConvergence
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingPartitionSupport
public import TernaryPeriodPolynomials.Analysis.Compact.ChartDetermination

@[expose] public section


/-! Literal agreement between the actual double chart cutoff and quotient scalar multiplication. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set PolynomialFormHilbert PolynomialCoefficientMetric PolynomialFormConnection
  SmoothLocalDeRham SmoothCoveringDeRham SmoothDeRhamGluing
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold
open scoped ContDiff Manifold

theorem doubleChartCutoff_coordinateScalar (n k : ℕ) (S : Space) (ψ : OrbitSpace → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ ψ)
    (hsψ : tsupport ψ ⊆ (quotientChart S).source)
    (η : Coordinates → ℝ) (hχ : ContDiff ℝ ∞ (coordinateScalar S ψ))
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ (quotientChart S).target)
    (he : η * coordinateScalar S ψ = coordinateScalar S ψ) (a : Core n k) :
    doubleChartCutoff n k S (coordinateScalar S ψ) η hχ hη hcη hsη a.val =
      coreScalarMultiply n k ψ hψ a := by
  apply Subtype.ext
  apply eq_of_globalChartRepresentative_eq (deckRepresentation n) S
  · exact quotientSupport_chartCutoff n k S (η * coordinateScalar S ψ) (hη.mul hχ)
      hcη.mul_right (tsupport_mul_subset_left.trans hsη) a.val
  · rw [coreScalarMultiply_val]
    exact (quotientSupport_scalarMultiply_subset_tsupport ψ hψ.contMDiffOn a.val).trans hsψ
  · apply Form.ext
    intro x hx
    have hl := globalChartRepresentative_apply (deckRepresentation n) S
      (doubleChartCutoff n k S (coordinateScalar S ψ) η hχ hη hcη hsη a.val).val hx
    have hr := globalChartRepresentative_apply (deckRepresentation n) S
      (coreScalarMultiply n k ψ hψ a).val hx
    have hs : (η * coordinateScalar S ψ) x = ψ (coordinateProjection x) :=
      (congrFun he x).trans ((coordinateScalar_apply S ψ hx).trans
        (congrArg ψ (quotientChart_projection_coordinates S hx)))
    exact hl.trans ((chartCutoff_apply n k S (η * coordinateScalar S ψ) (hη.mul hχ)
      hcη.mul_right (tsupport_mul_subset_left.trans hsη) a.val hx).trans
        ((congrArg (fun t : ℝ => t • a.val.val.val x) hs).trans
          ((coreScalarMultiply_apply n k ψ hψ a x).symm.trans hr.symm)))

end TernaryPoly.PolynomialFormCoordinates
