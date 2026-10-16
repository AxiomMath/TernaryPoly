module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.BoundedSmoothRealization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedAnalyticFamilies TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open scoped Classical Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleScalarRegularity

def diagonal {degree : ℕ} (data : InducingData degree) : SmoothTupleOperator.Space data →ₗ[ℂ] SmoothTupleOperator.Space data :=
  LinearMap.pi (fun key =>
    (FiniteProfileResidues.character data (UniversalFiniteProfiles.representative data key))⁻¹ • LinearMap.proj key)

def linear {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) :
    SmoothTupleOperator.Space data →ₗ[ℂ] data.cusp.smooth :=
  FiniteProfileResidues.character data point • (SmoothTupleOperator.averagedRow data parameter halfPlane point).comp (diagonal data)

theorem linear_val {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (value : SmoothTupleOperator.Space data) :
    (linear data parameter halfPlane point value).val =
      TupleCuspRegularity.operator data parameter halfPlane point (fun key => (value key).val) := by
  simp only [linear, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul, SmoothTupleOperator.averagedRow_val]
  rfl

theorem linear_fixed {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (value : SmoothTupleOperator.Space data) :
    (linear data parameter halfPlane point value).val ∈ fixedSubspace data.cusp finiteCongruence := by
  simp only [linear, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul,
    SmoothTupleOperator.averagedRow_val, TupleFiniteAverage.averagedRow_eq]
  exact (fixedSubspace data.cusp finiteCongruence).smul_mem _
    ((fixedSubspace data.cusp finiteCongruence).smul_mem _ (TupleFiniteAverage.sectionAverage_fixed data parameter halfPlane point _))

def fixedLinear {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) :
    SmoothTupleOperator.Space data →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence :=
  (linear data parameter halfPlane point).codRestrict (fixedSmooth data.cusp finiteCongruence)
    (linear_fixed data parameter halfPlane point)

def entry {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (key : UniversalFiniteProfiles.Key data) :
    data.cusp.smooth →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence :=
  (fixedLinear data parameter halfPlane point).comp (LinearMap.single ℂ (fun _ => data.cusp.smooth) key)

theorem entry_val {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (key : UniversalFiniteProfiles.Key data)
    (vector : data.cusp.smooth) :
    (entry data parameter halfPlane point key vector).val.val =
      ((TupleCuspRegularity.operator data parameter halfPlane point).comp
        (ContinuousLinearMap.single ℂ (fun _ => data.cusp.H) key)) vector.val := by
  change (linear data parameter halfPlane point (Pi.single key vector)).val = _
  rw [linear_val]
  apply congrArg (TupleCuspRegularity.operator data parameter halfPlane point)
  funext other
  by_cases equality : other = key
  · subst other
    simp
  · simp [Pi.single_eq_of_ne equality]

theorem vector_sum {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    TupleCuspLift.vector induced halfPlane point realPoint =
      ∑ key, (entry data parameter halfPlane point key
        (planeCuspVector induced (inclusion (UniversalFiniteProfiles.representative data key) * atInfinity realPoint))).val := by
  have sumEquality : (∑ key, (entry data parameter halfPlane point key
      (planeCuspVector induced (inclusion (UniversalFiniteProfiles.representative data key) * atInfinity realPoint))).val) =
      linear data parameter halfPlane point (fun key =>
        planeCuspVector induced (inclusion (UniversalFiniteProfiles.representative data key) * atInfinity realPoint)) := by
    change (∑ key, linear data parameter halfPlane point (Pi.single key
      (planeCuspVector induced (inclusion (UniversalFiniteProfiles.representative data key) * atInfinity realPoint)))) = _
    rw [← map_sum, Finset.univ_sum_single]
  rw [sumEquality]
  apply Subtype.ext
  rw [TupleCuspRegularity.vector_val, linear_val]

theorem section_sum {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    FiniteSectionProjection.sectionFunction induced (inclusion point * atInfinity realPoint) =
      ∑ key, data.cusp.realize (entry data parameter halfPlane point key
        (matrixCuspVector induced (UniversalFiniteProfiles.representative data key) realPoint.val)).val 1 := by
  have realized := TupleCuspLift.realize_vector induced halfPlane point realPoint 1
  simp only [map_one, Helpers.normPower_one, one_mul] at realized
  have leviOne : planeLevi (1 : BinaryAdelicGL) 1 = 1 := (planeLeviHom Adeles).map_one
  rw [leviOne, one_mul, vector_sum, map_sum, Finset.sum_apply] at realized
  rw [← realized]
  apply Finset.sum_congr rfl
  intro key _
  rw [matrixCuspVector, OrbitSmooth.invertibleMatrix_units]
  rfl

theorem section_analyticAt {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    AnalyticAt ℝ (fun matrix : PlaneMatrix =>
      FiniteSectionProjection.sectionFunction induced (inclusion point * atInfinity (invertibleMatrix matrix))) realPoint.val := by
  have analytic := Finset.analyticAt_fun_sum Finset.univ (fun key _ =>
    BoundedSmoothRealization.matrixCuspVector_analyticAt induced (entry data parameter halfPlane point key)
      ((TupleCuspRegularity.operator data parameter halfPlane point).comp
        (ContinuousLinearMap.single ℂ (fun _ => data.cusp.H) key))
      (entry_val data parameter halfPlane point key) (UniversalFiniteProfiles.representative data key) realPoint 1)
  apply analytic.congr
  have nearby : ∀ᶠ matrix : PlaneMatrix in nhds realPoint.val, matrix.det ≠ 0 := by
    change {matrix : PlaneMatrix | matrix.det ≠ 0} ∈ nhds realPoint.val
    exact (isOpen_ne.preimage continuous_id.matrix_det).mem_nhds (GeneralLinearGroup.det_ne_zero realPoint)
  filter_upwards [nearby] with matrix invertible
  rw [section_sum induced halfPlane point (invertibleMatrix matrix), OrbitSmooth.invertibleMatrix_val matrix invertible]

theorem vector_realize_analyticAt {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (evaluation : BinaryAdelicGL) :
    AnalyticAt ℝ (fun matrix : PlaneMatrix =>
      data.cusp.realize (TupleCuspLift.vector induced halfPlane point (invertibleMatrix matrix)) evaluation) realPoint.val := by
  have analytic := Finset.analyticAt_fun_sum Finset.univ (fun key _ =>
    BoundedSmoothRealization.matrixCuspVector_analyticAt induced (entry data parameter halfPlane point key)
      ((TupleCuspRegularity.operator data parameter halfPlane point).comp
        (ContinuousLinearMap.single ℂ (fun _ => data.cusp.H) key))
      (entry_val data parameter halfPlane point key) (UniversalFiniteProfiles.representative data key) realPoint evaluation)
  apply analytic.congr
  apply Filter.Eventually.of_forall
  intro matrix
  dsimp only
  rw [vector_sum, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro key _
  rfl

theorem vector_realize_smooth {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (evaluation : BinaryAdelicGL) :
    Smooth (fun matrices : Fin 1 → RealGL3 =>
      data.cusp.realize (TupleCuspLift.vector induced halfPlane point (realPoint * matrices 0)) evaluation) :=
  BoundedSmoothRealization.smooth_of_analytic
    (fun realPoint => data.cusp.realize (TupleCuspLift.vector induced halfPlane point realPoint) evaluation)
    (fun realPoint => vector_realize_analyticAt induced halfPlane point realPoint evaluation) realPoint

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleScalarRegularity
