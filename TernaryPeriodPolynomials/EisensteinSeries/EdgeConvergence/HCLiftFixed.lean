module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftCircle
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftLinear
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalFinite

@[expose] public section


/-!
# The Cauchy lift of the local vectors is fixed by a finite level

Original work by Claude Sonnet 5.5.

The vector `liftVector x` is the circle integral of local Hilbert vectors, each fixed by the open
compact subgroup `LineOrbitLevel.level (κ · x_last)` of `GL₂(𝔸_f)` (`localValue_fixed`); continuous
linear maps commute with the circle integral (`EndpointLift.map_endpointLift`), which needs the
continuity of the local vectors on the circle (`continuousOn_liftValue`, from the analytic
expansions of `exists_circleSeries`). We also record the elementary facts about the splitting of a
maximal compact element and the constant multiples of the endpoint lift used for the orbit of the
lift under `GL₂(ℝ)`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix MeasureTheory
  Metric
open scoped Matrix.Norms.Elementwise NNReal
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCLift

/-- An adelic matrix is the product of its finite and its real parts. -/
theorem eq_atFinite_mul_atInfinity (element : AdelicGL) :
    element = atFinite (finiteGroup element) * atInfinity (realGroup element) := by
  apply InducedContinuity.adelic_ext
  · simp only [map_mul, InducedContinuity.realGroup_atFinite,
      InducedContinuity.realGroup_atInfinity, one_mul]
  · simp only [map_mul, InducedContinuity.finiteGroup_atFinite,
      InducedContinuity.finiteGroup_atInfinity, mul_one]

/-- A maximal compact element times a real translation is the finite part times the translation
rotated by the real part. -/
theorem compact_mul_atInfinity (element : AdelicGL) (translation : RealGL3) :
    element * atInfinity translation =
      atFinite (finiteGroup element) * atInfinity (realGroup element * translation) := by
  conv_lhs => rw [eq_atFinite_mul_atInfinity element]
  rw [mul_assoc, RealTranslations.atInfinity_mul]

theorem inMaximalCompact_atFinite (element : AdelicGL) (compact : inMaximalCompact element) :
    inMaximalCompact (atFinite (finiteGroup element)) := by
  constructor
  · rw [InducedContinuity.realGroup_atFinite]
    simp
  · rw [InducedContinuity.finiteGroup_atFinite]
    exact compact.2

/-- The endpoint lift only depends on the values on the circle. -/
theorem endpointLift_congr {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {circleRadius : ℝ} (circlePositive : 0 < circleRadius) (lam : ℂ → ℂ) {first second : ℂ → E}
    (equality : ∀ parameter ∈ sphere cohomologicalPoint circleRadius,
      first parameter = second parameter) :
    EndpointLift.endpointLift cohomologicalPoint circleRadius lam first =
      EndpointLift.endpointLift cohomologicalPoint circleRadius lam second := by
  unfold EndpointLift.endpointLift
  congr 1
  refine circleIntegral.integral_congr circlePositive.le (fun parameter membership => ?_)
  simp only [equality parameter membership]

/-- The endpoint lift of a constant multiple. -/
theorem endpointLift_const_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {circleRadius : ℝ} (circlePositive : 0 < circleRadius) (lam : ℂ → ℂ)
    (scalar : ℂ) (values : ℂ → E) :
    EndpointLift.endpointLift cohomologicalPoint circleRadius lam (fun parameter =>
      scalar • values parameter) =
      scalar • EndpointLift.endpointLift cohomologicalPoint circleRadius lam values := by
  rw [EndpointLift.endpointLift_eq_circleAverage circlePositive,
    EndpointLift.endpointLift_eq_circleAverage circlePositive]
  rw [← Real.circleAverage_fun_smul]
  congr 1
  funext parameter
  exact smul_comm _ _ _

section Fixed

variable {degree arity : ℕ} (data : InducingData degree)
  (holomorphic : PlaneEisensteinHolomorphic data)
  (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
  (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices))
  (weight : (Fin arity → RealGL3) → ℝ)

/-- The Cauchy lift at given vertices and translation. -/
def liftAt (circleRadius : ℝ) (lam : ℂ → ℂ) (compact : AdelicGL)
    (vertices : Fin arity → RealGL3) (translation : RealGL3) : data.cusp.H :=
  EndpointLift.endpointLift cohomologicalPoint circleRadius lam (fun parameter =>
    localFamilyValue data parameter (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter) vertices
      (compact * atInfinity translation))

theorem liftVector_eq_liftAt (circleRadius : ℝ) (lam : ℂ → ℂ) (compact : AdelicGL)
    (x : Fin (arity + 1) → RealGL3) :
    liftVector data holomorphic family induced weight circleRadius lam compact x =
      liftAt data holomorphic family induced weight circleRadius lam compact
        (fun index => x index.castSucc) (x (Fin.last arity)) :=
  rfl

theorem liftAt_compact (circleRadius : ℝ) (lam : ℂ → ℂ) (compact : AdelicGL)
    (vertices : Fin arity → RealGL3) (translation : RealGL3) :
    liftAt data holomorphic family induced weight circleRadius lam compact vertices translation =
      liftAt data holomorphic family induced weight circleRadius lam
        (atFinite (finiteGroup compact)) vertices (realGroup compact * translation) := by
  unfold liftAt
  rw [compact_mul_atInfinity compact translation]

/-- The local Hilbert vector at given vertices and translation is continuous in the parameter on
the circle. -/
theorem continuousOn_liftValue (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (circleRadius : ℝ) (circlePositive : 0 < circleRadius)
    (halfPlane : closedBall cohomologicalPoint circleRadius ⊆ EdgeInputs.localHalfPlane degree)
    (compact : AdelicGL) (compactMembership : inMaximalCompact compact)
    (vertices : Fin arity → RealGL3) (translation : RealGL3) :
    ContinuousOn (fun parameter => localFamilyValue data parameter
      (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter) vertices
      (compact * atInfinity translation)) (sphere cohomologicalPoint circleRadius) := by
  have point := continuousOn_circleValue data holomorphic family induced weight lift weightSmooth
    circleRadius circlePositive halfPlane compact compactMembership
    (fun index => (Fin.snoc (α := fun _ => RealGL3) vertices translation index).val)
    (fun index => GeneralLinearGroup.det_ne_zero _)
  refine point.congr (fun parameter _ => ?_)
  simp only [circleValue, AdelicFamilyTaylor.matrixOrbit, SmoothJets.matrixExtension,
    AdelicFamilyTaylor.orbit, SmoothContinuity.invertibleMatrix_coe, Fin.snoc_castSucc,
    Fin.snoc_last]

/-- The Cauchy lift is fixed by the finite level of the argument. -/
theorem liftAt_fixed (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (circleRadius : ℝ) (circlePositive : 0 < circleRadius)
    (halfPlane : closedBall cohomologicalPoint circleRadius ⊆ EdgeInputs.localHalfPlane degree)
    (lam : ℂ → ℂ) (lamContinuous : ContinuousOn lam (sphere cohomologicalPoint circleRadius))
    (compact : AdelicGL) (compactMembership : inMaximalCompact compact)
    (vertices : Fin arity → RealGL3) (translation : RealGL3)
    (unit : LineOrbitLevel.level (compact * atInfinity translation)) :
    data.cusp.π (atFinite unit.val)
        (liftAt data holomorphic family induced weight circleRadius lam compact vertices
          translation) =
      liftAt data holomorphic family induced weight circleRadius lam compact vertices
        translation := by
  have continuous := continuousOn_liftValue data holomorphic family induced weight lift
    weightSmooth circleRadius circlePositive halfPlane compact compactMembership vertices
    translation
  let transformation :=
    (CuspHilbertAction.isometry data.cusp (atFinite unit.val)).toContinuousLinearMap
  have mapped := EndpointLift.map_endpointLift transformation circlePositive lamContinuous
    continuous
  have fixed : ∀ parameter : ℂ, transformation
      (localFamilyValue data parameter (twistedAt data holomorphic family induced weight parameter)
        (twistedAt_induced data holomorphic family induced weight parameter) vertices
        (compact * atInfinity translation)) =
      localFamilyValue data parameter (twistedAt data holomorphic family induced weight parameter)
        (twistedAt_induced data holomorphic family induced weight parameter) vertices
        (compact * atInfinity translation) :=
    fun parameter => localValue_fixed data parameter _ _ _ unit
  simp only [fixed] at mapped
  unfold liftAt
  exact mapped

end Fixed

end TernaryPeriodPolynomials.EdgeConvergence.HCLift
