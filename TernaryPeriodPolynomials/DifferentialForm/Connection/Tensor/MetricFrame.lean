module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.MetricCurves

@[expose] public section


/-! First variation of genuine tensor frames along affine coefficient and tangent maps. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric SymmetricSpaceCharts SmoothCoveringDeRham
open PolynomialFormGeometricEnergy ContinuousAlternatingMap
open scoped Matrix.Norms.Elementwise

theorem hasDerivAt_form_affine_pullback (n k : ℕ) (a : FormValue n k) (A : Coordinates →L[ℝ] Coordinates) :
    HasDerivAt (fun t : ℝ => a.compContinuousLinearMap (affineOperator A t))
      (a.fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ Coordinates) A) 0 := by
  have h := (ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap
    (a, ContinuousLinearMap.id ℝ Coordinates)).hasFDerivAt.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_const (0 : ℝ) a).prodMk (hasDerivAt_affineOperator A)) (by simp)
  convert! h using 1
  change _ = (compContinuousLinearMapCLM (ContinuousLinearMap.id ℝ Coordinates)) (0 : FormValue n k) + _
  rw [PolynomialFormCoordinates.clm_map_zero, zero_add]
  rfl

theorem hasDerivAt_coefficientFormMap_affine (n k : ℕ) (A : Coefficients n →L[ℝ] Coefficients n) :
    HasDerivAt (fun t : ℝ => coefficientFormMap (E := Coordinates) (affineOperator A t) k)
      (coefficientFormMap A k) 0 := by
  convert! hasDerivAt_affineOperator (coefficientFormMap (E := Coordinates) A k) using 1

/-- Actual coefficient composition and tangent pullback for the comparison frame. -/
def tensorFrameCurve (n k : ℕ) (x u : Coordinates) (a : FormValue n k) (t : ℝ) : FormValue n k :=
  coefficientFormMap (affineOperator (connectionMatrix n x u) t) k
    (a.compContinuousLinearMap (affineOperator (-tangentEndomorphism x u) t))

@[simp] theorem tensorFrameCurve_zero (n k : ℕ) (x u : Coordinates) (a : FormValue n k) :
    tensorFrameCurve n k x u a 0 = a := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [tensorFrameCurve, affineOperator_zero]
  rfl

theorem hasDerivAt_tensorFrameCurve (n k : ℕ) (x u : Coordinates) (a : FormValue n k) :
    HasDerivAt (tensorFrameCurve n k x u a)
      (coefficientFormMap (connectionMatrix n x u) k a - tangentFormAction n k x u a) 0 := by
  have h := (hasDerivAt_coefficientFormMap_affine n k (connectionMatrix n x u)).clm_apply
    (hasDerivAt_form_affine_pullback n k a (-tangentEndomorphism x u))
  convert! h using 1
  simp only [affineOperator_zero, map_neg, sub_eq_add_neg]
  congr 1

theorem toMatrix_affine_tangent (x u : Coordinates) (t : ℝ) :
    LinearMap.toMatrix' (affineOperator (-tangentEndomorphism x u) t).toLinearMap =
      (1 : Matrix (Fin 5) (Fin 5) ℝ) + t • (-tangentConnectionMatrix x u) := by
  change LinearMap.toMatrix' ((LinearMap.id : Coordinates →ₗ[ℝ] Coordinates) +
    t • (-(tangentEndomorphism x u).toLinearMap)) = _
  simp only [map_add, map_smul, map_neg, LinearMap.toMatrix'_id, tangentConnectionMatrix]

theorem metricDataPairing_tensorFrameCurve (n k : ℕ) (x u : Coordinates) (a b : FormValue n k) (t : ℝ) :
    metricDataPairing n k (metricCoefficientCurve n x u t) (metricInverseCurve x u t) a b =
      formPairing n k x (tensorFrameCurve n k x u a t) (tensorFrameCurve n k x u b t) := by
  rw [← metricDataPairing_actual]
  unfold tensorFrameCurve
  rw [← metricDataPairing_coefficient, metricDataPairing_pullback, toMatrix_affine_tangent]
  rfl

end TernaryPoly.PolynomialFormConnection
