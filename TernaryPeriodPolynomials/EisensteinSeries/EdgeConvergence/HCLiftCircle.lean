module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftMajorant
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftContinuity
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.EndpointLiftTaylor
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.EndpointLift
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.OrbitSmooth

@[expose] public section


/-!
# The Cauchy lift of the local vectors is real analytic in the real variables

Original work by Claude Sonnet 5.5.

For a function `lam` continuous on a circle `|s - s₀| = r` inside the half plane `Re s > -n/2 - 1`,
the vector `W(x) = (2πi)⁻¹ ∮ (s - s₀)⁻¹ lam(s) L(s, x) ds` (`liftVector`), where `L(s, x)` is the local
Hilbert standard integral of the (twisted) flat family at the argument `κ · x_last`, is a smooth
function of the tuple `x` of real matrices (`liftVector_smooth`). The proof: the power series of
`x ↦ L(s, x)` at a real tuple, on a common ball, with coefficients bounded uniformly in `s` and
continuous in `s` (`exists_circleSeries`, from `HCLift.exists_uniformMajorant` and
`HCLift.continuous_orbit_coefficients`), and `EndpointLift.circleAverage_hasFPowerSeriesOnBall`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix MeasureTheory
  Filter Topology Metric
open scoped Matrix.Norms.Elementwise NNReal
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open CompactTaylorBounds FamilyCuspTaylor

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCLift

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedAddCommGroup
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  ContinuousMultilinearMap.normedAddCommGroup'

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedSpace ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  ContinuousMultilinearMap.normedSpace'

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [SMulCommClass ℝ ℂ E] (order : ℕ) :
    NormedSpace ℂ
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  ContinuousMultilinearMap.normedSpace

local instance {arity order : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [SMulCommClass ℝ ℂ E] :
    IsBoundedSMul ℂ
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  IsBoundedSMul.of_norm_smul_le fun r x => (norm_smul r x).le

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    ContinuousENorm
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  SeminormedAddGroup.toContinuousENorm

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  PseudoEMetricSpace.pseudoMetrizableSpace

section Circle

variable {degree arity : ℕ} (data : InducingData degree)
  (holomorphic : PlaneEisensteinHolomorphic data)
  (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
  (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices))
  (weight : (Fin arity → RealGL3) → ℝ)

/-- The local Hilbert vector of the twisted family, as a function of the parameter, at the
tuple of matrices `point`. -/
def circleValue (compact : AdelicGL) (parameter : ℂ)
    (point : SmoothJets.MatrixTuples 3 arity.succ) : data.cusp.H :=
  AdelicFamilyTaylor.matrixOrbit
    (localFamilyValue data parameter (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter)) compact point

/-- The Cauchy lift of the local Hilbert vectors of the twisted family at the arguments
`compact · x_last`, as a function of the tuple `x` of real matrices. -/
def liftVector (circleRadius : ℝ) (lam : ℂ → ℂ) (compact : AdelicGL)
    (x : Fin (arity + 1) → RealGL3) : data.cusp.H :=
  EndpointLift.endpointLift cohomologicalPoint circleRadius lam (fun parameter =>
    localFamilyValue data parameter (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter)
      (fun index => x index.castSucc) (compact * atInfinity (x (Fin.last arity))))

/-- The Taylor series, at a real tuple, of the local vectors on the circle: a common ball, series
continuous in the parameter, and a geometric bound uniform in the parameter. -/
theorem exists_circleSeries (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (circleRadius : ℝ) (circlePositive : 0 < circleRadius)
    (halfPlane : closedBall cohomologicalPoint circleRadius ⊆ EdgeInputs.localHalfPlane degree)
    (compact : AdelicGL) (compactMembership : inMaximalCompact compact)
    (real : Fin (arity + 1) → RealGL3) :
    ∃ radius : ℝ≥0, 0 < radius ∧
      ∃ series : ℂ → FormalMultilinearSeries ℝ (SmoothJets.MatrixTuples 3 arity.succ) data.cusp.H,
      ∃ constant : ℝ,
        (∀ parameter ∈ sphere cohomologicalPoint circleRadius,
          HasFPowerSeriesOnBall (circleValue data holomorphic family induced weight compact parameter)
            (series parameter) (fun index => (real index).val) radius) ∧
        (∀ order, ContinuousOn (fun parameter => series parameter order)
          (sphere cohomologicalPoint circleRadius)) ∧
        (∀ parameter ∈ sphere cohomologicalPoint circleRadius, ∀ order,
          ‖series parameter order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order) := by
  have lowerMembership : cohomologicalPoint - (circleRadius : ℂ) ∈
      closedBall cohomologicalPoint circleRadius := by
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg circlePositive.le]
  have lowerHalf : -(degree : ℝ) / 2 - 1 < (cohomologicalPoint - (circleRadius : ℂ)).re :=
    halfPlane lowerMembership
  rw [Complex.sub_re, Complex.ofReal_re] at lowerHalf
  have ordered : cohomologicalPoint.re - circleRadius ≤ cohomologicalPoint.re + circleRadius := by
    linarith
  have strip : ∀ parameter ∈ sphere cohomologicalPoint circleRadius,
      cohomologicalPoint.re - circleRadius ≤ parameter.re ∧
        parameter.re ≤ cohomologicalPoint.re + circleRadius := by
    intro parameter membership
    have distance : ‖parameter - cohomologicalPoint‖ = circleRadius :=
      mem_sphere_iff_norm.mp membership
    have bound := Complex.abs_re_le_norm (parameter - cohomologicalPoint)
    rw [Complex.sub_re, distance] at bound
    constructor
    · linarith [(abs_le.mp bound).1]
    · linarith [(abs_le.mp bound).2]
  obtain ⟨majorant⟩ := exists_uniformMajorant data holomorphic family induced weight lift
    weightSmooth real (cohomologicalPoint.re - circleRadius) (cohomologicalPoint.re + circleRadius)
    lowerHalf ordered (isCompact_sphere cohomologicalPoint circleRadius) strip compact
    compactMembership
  have lifts : ∀ parameter : ℂ, HasSmoothCuspLift data .plane parameter
      (twistedAt data holomorphic family induced weight parameter) :=
    fun parameter => twistedAt_hasSmoothCuspLift data holomorphic family induced weight lift
      weightSmooth parameter
  let series : ℂ → FormalMultilinearSeries ℝ (SmoothJets.MatrixTuples 3 arity.succ) data.cusp.H :=
    fun parameter order => ∫ coordinates, localFamilySeries data parameter
      (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter) real compact
      coordinates order ∂localRadicalMeasure
  refine ⟨majorant.radius, majorant.radius_pos, series,
    ∫ coordinates, majorant.bound coordinates ∂localRadicalMeasure, ?_, ?_, ?_⟩
  · intro parameter membership
    exact (majorant.toMajorant parameter membership).value_expansion (lifts parameter)
  · intro order
    refine continuousOn_of_dominated (bound := fun coordinates =>
      majorant.bound coordinates * (majorant.radius : ℝ)⁻¹ ^ order) ?_ ?_ ?_ ?_
    · intro parameter _
      exact (localFamilySeries_continuous data parameter
        (twistedAt data holomorphic family induced weight parameter)
        (twistedAt_induced data holomorphic family induced weight parameter)
        (lifts parameter) real compact order).aestronglyMeasurable
    · intro parameter membership
      exact Eventually.of_forall (fun coordinates =>
        majorant.dominates parameter membership coordinates order)
    · exact majorant.integrable.mul_const _
    · refine Eventually.of_forall (fun coordinates => ?_)
      exact (continuous_orbit_coefficients data holomorphic family induced weight lift
        weightSmooth (weyl⁻¹ * localRadical coordinates * compact) real order).continuousOn
  · intro parameter membership order
    have bounds := ((majorant.toMajorant parameter membership).coefficient_bounds
      (lifts parameter) order).2
    exact (norm_integral_le_integral_norm _).trans bounds

/-- The local Hilbert vector of the twisted family is continuous in the parameter on the circle. -/
theorem continuousOn_circleValue (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (circleRadius : ℝ) (circlePositive : 0 < circleRadius)
    (halfPlane : closedBall cohomologicalPoint circleRadius ⊆ EdgeInputs.localHalfPlane degree)
    (compact : AdelicGL) (compactMembership : inMaximalCompact compact)
    (point : SmoothJets.MatrixTuples 3 arity.succ) (invertible : ∀ index, (point index).det ≠ 0) :
    ContinuousOn (fun parameter => circleValue data holomorphic family induced weight compact
      parameter point) (sphere cohomologicalPoint circleRadius) := by
  obtain ⟨radius, positive, series, constant, expansion, continuous, bounded⟩ :=
    exists_circleSeries data holomorphic family induced weight lift weightSmooth circleRadius
      circlePositive halfPlane compact compactMembership (fun index => invertibleMatrix (point index))
  have centerEquality : (fun index => (invertibleMatrix (point index)).val) = point :=
    funext fun index => PlaneEisensteinContinuation.OrbitSmooth.invertibleMatrix_val _
      (invertible index)
  have evaluation : Continuous (fun value :
      ContinuousMultilinearMap ℝ (fun _ : Fin 0 => SmoothJets.MatrixTuples 3 arity.succ) data.cusp.H =>
      value (fun i => i.elim0)) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => SmoothJets.MatrixTuples 3 arity.succ)
      data.cusp.H (fun i => i.elim0)).continuous
  have coefficientContinuous := evaluation.comp_continuousOn (continuous 0)
  refine coefficientContinuous.congr (fun parameter membership => ?_)
  have value := (expansion parameter membership).coeff_zero (fun i => i.elim0)
  rw [centerEquality] at value
  exact value.symm

/-- **Real analyticity of the Cauchy lift.** -/
theorem liftVector_smooth (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (circleRadius : ℝ) (circlePositive : 0 < circleRadius)
    (halfPlane : closedBall cohomologicalPoint circleRadius ⊆ EdgeInputs.localHalfPlane degree)
    (lam : ℂ → ℂ) (lamContinuous : ContinuousOn lam (sphere cohomologicalPoint circleRadius))
    (compact : AdelicGL) (compactMembership : inMaximalCompact compact) :
    Smooth (liftVector data holomorphic family induced weight circleRadius lam compact) := by
  obtain ⟨lamBound, lamBounded⟩ :=
    (isCompact_sphere cohomologicalPoint circleRadius).exists_bound_of_continuousOn lamContinuous
  apply (SmoothAnalyticity.smooth_iff_analyticOn _).mpr
  intro matrices membership
  obtain ⟨radius, positive, series, constant, expansion, continuous, bounded⟩ :=
    exists_circleSeries data holomorphic family induced weight lift weightSmooth circleRadius
      circlePositive halfPlane compact compactMembership
      (fun index => invertibleMatrix (matrices index))
  have circle := EndpointLift.circleAverage_hasFPowerSeriesOnBall
    (X := SmoothJets.MatrixTuples 3 arity.succ) (F := data.cusp.H)
    (c := cohomologicalPoint) (r := circleRadius) circlePositive
    (fun parameter point => lam parameter •
      circleValue data holomorphic family induced weight compact parameter point)
    (fun parameter => lam parameter • series parameter)
    (fun index => (invertibleMatrix (matrices index)).val) radius positive
    (max lamBound 0 * constant)
    (fun parameter membership => (expansion parameter membership).const_smul (c := lam parameter))
    (fun order => (IsBoundedSMul.continuousSMul (α := ℂ)).continuous_smul.comp_continuousOn
      (lamContinuous.prodMk (continuous order)))
    (by
      intro parameter membership order
      calc ‖(lam parameter • series parameter) order‖
          = ‖lam parameter‖ * ‖series parameter order‖ := by
            exact norm_smul (lam parameter) (series parameter order)
        _ ≤ max lamBound 0 * (constant * (radius : ℝ)⁻¹ ^ order) :=
          mul_le_mul ((lamBounded parameter membership).trans (le_max_left _ _))
            (bounded parameter membership order) (norm_nonneg _) (le_max_right _ _)
        _ = _ := by ring)
  have equal : SmoothJets.matrixExtension
      (liftVector data holomorphic family induced weight circleRadius lam compact) =
      fun point => Real.circleAverage (fun parameter => lam parameter •
        circleValue data holomorphic family induced weight compact parameter point)
        cohomologicalPoint circleRadius :=
    funext fun point => EndpointLift.endpointLift_eq_circleAverage circlePositive lam _
  rw [equal]
  have analytic := circle.analyticAt
  have centerEquality : (fun index => (invertibleMatrix (matrices index)).val) = matrices :=
    funext fun index => PlaneEisensteinContinuation.OrbitSmooth.invertibleMatrix_val _
      (membership index)
  rw [centerEquality] at analytic
  exact analytic.analyticWithinAt

end Circle

end TernaryPeriodPolynomials.EdgeConvergence.HCLift
