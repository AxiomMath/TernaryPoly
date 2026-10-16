module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.RealExterior

@[expose] public section


/-! Naturality of the actual inverse-Gram symmetric contraction. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

theorem symmetricContraction_real (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (a c : FormValue n (k + 1))
    (ha : a.compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) (k + 1) c) :
    (symmetricContraction n k (coordinateAction g x) a).compContinuousLinearMap
      (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) k (symmetricContraction n k x c) := by
  have hval (z : Fin (k + 1) → Coordinates) :
      a (fun r => fderiv ℝ (coordinateAction g) x (z r)) = realCoefficientMap n g (c z) :=
    congrArg (fun F : FormValue n (k + 1) => F z) ha
  apply ContinuousAlternatingMap.ext
  intro v
  change symmetricContraction n k (coordinateAction g x) a
      (fun r => fderiv ℝ (coordinateAction g) x (v r)) =
    realCoefficientMap n g (symmetricContraction n k x c v)
  rw [symmetricContraction_frame n k _ a (inverseGram x) _ (inverseGram_real g x hx)]
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply]
  rw [symmetricContraction_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  congr 1
  change symmetricPart n (coordinateAction g x) (fderiv ℝ (coordinateAction g) x (Pi.single i 1))
    (a (vecCons (fderiv ℝ (coordinateAction g) x (Pi.single j 1))
      (fun r => fderiv ℝ (coordinateAction g) x (v r)))) = _
  have hv : vecCons (fderiv ℝ (coordinateAction g) x (Pi.single j 1))
      (fun r => fderiv ℝ (coordinateAction g) x (v r)) =
      fun r => fderiv ℝ (coordinateAction g) x (vecCons (Pi.single j 1) v r) := by
    funext r
    refine Fin.cases ?_ (fun i => ?_) r <;> rfl
  rw [hv, hval, symmetricPart_real n g hg x hx]

end TernaryPoly.PolynomialFormGeometricEnergy
