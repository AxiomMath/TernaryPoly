module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.MetricCoefficient

@[expose] public section


/-! The genuine weighted-Gram coordinate map from intrinsic compact tests to actual scalar tests. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham
open scoped Distributions

/-- Each genuine weighted-Gram coefficient of an actual compact test is an actual compact smooth
scalar test, linearly in the original intrinsic test. -/
def intrinsicMetricCoefficientTest (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (i : Index n k) : supportedCompactCore n k (chartOpen S Ω) →ₗ[ℝ] 𝓓(Ω, ℝ) where
  toFun w := ⟨intrinsicMetricCoefficient n k S Ω w i, intrinsicMetricCoefficient_smooth n k S Ω w i,
    intrinsicMetricCoefficient_compact n k S Ω w i, intrinsicMetricCoefficient_tsupport n k S Ω w i⟩
  map_add' w z := by
    apply TestFunction.ext
    intro x
    change (weightedGram n k x).mulVec
      (coordinates n k ((globalChartRepresentative (deckRepresentation n) S k (w.val.val + z.val.val)).val x)) i =
        (weightedGram n k x).mulVec
          (coordinates n k ((globalChartRepresentative (deckRepresentation n) S k w.val.val).val x)) i +
        (weightedGram n k x).mulVec
          (coordinates n k ((globalChartRepresentative (deckRepresentation n) S k z.val.val).val x)) i
    simp only [map_add, AddMemClass.coe_add, Pi.add_apply, Matrix.mulVec_add]
  map_smul' c w := by
    apply TestFunction.ext
    intro x
    change (weightedGram n k x).mulVec
      (coordinates n k ((globalChartRepresentative (deckRepresentation n) S k (c • w.val.val)).val x)) i =
        c * (weightedGram n k x).mulVec
          (coordinates n k ((globalChartRepresentative (deckRepresentation n) S k w.val.val).val x)) i
    simp only [map_smul, SetLike.val_smul, Pi.smul_apply, Matrix.mulVec_smul, smul_eq_mul]

@[simp] theorem intrinsicMetricCoefficientTest_apply (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (i : Index n k)
    (w : supportedCompactCore n k (chartOpen S Ω)) (x : Coordinates) :
    intrinsicMetricCoefficientTest n k S Ω i w x = intrinsicMetricCoefficient n k S Ω w i x := rfl

end TernaryPoly.PolynomialFormWeakSmooth
