module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtRealizeA
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtOrbit

@[expose] public section


/-!
# Analyticity of the Hilbert Eichler period and smoothness of the normal form, for every integer
# rotation weight

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins of `endpointForm_analyticAt`, `endpointPeriod_analyticAt`, `endpointPeriod_contDiffOn`,
`hilbertNormal` and `hilbertNormal_smooth` of `AnalyticClasses.EichlerBridgeAnalytic` for an
integer rotation weight `wt` in place of `2 * halfWeight`.  The weight-free ingredients
(`affineOrbit_analyticAt`, `analyticAt_intervalIntegral_unit`, `straightPath_mem`,
`basePoint_contDiffOn`, `basePoint_im_pos`) are reused unchanged.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Set
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

namespace TernaryPeriodPolynomials.EvenLevelThree

theorem endpointForm_analyticAtWt (cusp : CuspidalRepresentation) (degree : ℕ) (wt : ℤ)
    (vector : cusp.smooth) {point : ℂ} (positive : 0 < point.im) :
    AnalyticAt ℝ (binaryEndpointHolomorphicFormWt cusp degree wt vector.val) point := by
  apply analyticAt_pi_iff.mpr
  intro position
  have scalar : AnalyticAt ℝ (fun argument : ℂ => (binaryWeightBasis (degree + 1)).coord position
      (binaryPointPower (degree + 1) argument)) point :=
    (binaryPointPower_functional_analytic (degree + 1)
      ((binaryWeightBasis (degree + 1)).coord position) point).restrictScalars
  have weight : AnalyticAt ℝ (fun argument : ℂ => wtFactor wt argument.im) point :=
    analyticAt_wtFactor_im wt positive
  exact scalar.smul (weight.smul (affineOrbit_analyticAt cusp vector positive))

/-- **The Hilbert Eichler period is real analytic in its endpoint**, for every integer weight. -/
theorem endpointPeriod_analyticAtWt (cusp : CuspidalRepresentation) (degree : ℕ)
    (wt : ℤ) (vector : cusp.smooth) {point : ℂ} (positive : 0 < point.im) :
    AnalyticAt ℝ (binaryEndpointPeriodWt cusp degree wt vector.val) point := by
  let path : ℂ × ℝ → ℂ := fun parameter => Complex.I + parameter.2 • (parameter.1 - Complex.I)
  let integrand : ℂ × ℝ → (Fin (degree + 2) → cusp.H) := fun parameter =>
    (parameter.1 - Complex.I) • binaryEndpointHolomorphicFormWt cusp degree wt vector.val
      (path parameter)
  have path_analytic (parameter : ℂ × ℝ) : AnalyticAt ℝ path parameter :=
    analyticAt_const.add (analyticAt_snd.smul (analyticAt_fst.sub analyticAt_const))
  have integrand_analytic (center : ℝ) (member : center ∈ Icc (0 : ℝ) 1) :
      AnalyticAt ℝ integrand (point, center) := by
    have form_analytic : AnalyticAt ℝ
        (fun parameter => binaryEndpointHolomorphicFormWt cusp degree wt vector.val
          (path parameter)) (point, center) :=
      AnalyticAt.comp (f := path) (x := (point, center)) (endpointForm_analyticAtWt cusp degree
        wt vector (straightPath_mem point positive member)) (path_analytic (point, center))
    exact (analyticAt_fst.sub analyticAt_const).smul form_analytic
  exact analyticAt_intervalIntegral_unit integrand point
    UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.isOpen_upperHalfPlaneSet positive
    (fun parameter member => by
      have path_continuous : Continuous (fun sample : ℝ => path (parameter, sample)) := by
        fun_prop
      exact (continuousOn_const (c := parameter - Complex.I)).smul
        ((binaryEndpointHolomorphicForm_continuousOnWt cusp degree wt vector.val).comp
          path_continuous.continuousOn (fun _ inside => straightPath_mem parameter member inside)))
    integrand_analytic

theorem endpointPeriod_contDiffOnWt (cusp : CuspidalRepresentation) (degree : ℕ)
    (wt : ℤ) (vector : cusp.smooth) :
    ContDiffOn ℝ ⊤ (binaryEndpointPeriodWt cusp degree wt vector.val)
      UpperHalfPlane.upperHalfPlaneSet := fun _ positive =>
  (endpointPeriod_analyticAtWt cusp degree wt vector positive).contDiffAt.contDiffWithinAt

/-- **The Hilbert normal form** `½ (Per(A·i) + J Per(-conj(A·i)))`, for an integer weight. -/
def hilbertNormalWt (cusp : CuspidalRepresentation) (degree : ℕ) (wt : ℤ)
    (vector : cusp.H) (A : BinaryRealGL) : Fin (degree + 2) → cusp.H :=
  (2 : ℂ)⁻¹ • (binaryEndpointPeriodWt cusp degree wt vector (basePoint A) +
    binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
      (binaryEndpointPeriodWt cusp degree wt vector
        (binaryComplexReflection (basePoint A))))

/-- **The Hilbert normal form is smooth**, for every integer weight. -/
theorem hilbertNormal_smoothWt (cusp : CuspidalRepresentation) (degree : ℕ) (wt : ℤ)
    (vector : cusp.smooth) :
    Smooth (fun point : Fin 1 → BinaryRealGL =>
      hilbertNormalWt cusp degree wt vector.val (point 0)) := by
  have period := endpointPeriod_contDiffOnWt cusp degree wt vector
  have base : ContDiffOn ℝ ⊤ (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      basePoint (invertibleMatrix (point 0))) {point | ∀ position, (point position).det ≠ 0} :=
    basePoint_contDiffOn.comp (contDiff_apply ℝ (Matrix (Fin 2) (Fin 2) ℝ) (0 : Fin 1)).contDiffOn
      (fun _ member => member 0)
  have reflected : ContDiffOn ℝ ⊤ (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      binaryComplexReflection (basePoint (invertibleMatrix (point 0))))
      {point | ∀ position, (point position).det ≠ 0} :=
    binaryComplexReflection.contDiff.comp_contDiffOn base
  have first := period.comp base (fun point _ => basePoint_im_pos (invertibleMatrix (point 0)))
  have second := period.comp reflected (fun point _ => by
    change 0 < (binaryComplexReflection (basePoint (invertibleMatrix (point 0)))).im
    rw [binaryComplexReflection_im]
    exact basePoint_im_pos _)
  have third := ((binaryHilbertOperator cusp (binaryWeightBasis (degree + 1))
    UpperHalfPlane.J).restrictScalars ℝ).contDiff.comp_contDiffOn second
  exact (first.add third).const_smul (2 : ℂ)⁻¹

end TernaryPeriodPolynomials.EvenLevelThree
