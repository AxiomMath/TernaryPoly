module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Analytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FamilyCuspTaylor
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TaylorIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.OrbitSmooth

@[expose] public section


/-!
# Joint smoothness of the local Hilbert standard integral in vertex families

The local analogue of `FamilyHilbertIntegral`: for a family of plane sections indexed by tuples of
real vertices, with a smooth cusp lift, the local standard integral is jointly smooth in the
vertices and the real right translation, provided the Taylor coefficients of the integrand have an
integrable geometric majorant on a common ball.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise NNReal
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

open CompactTaylorBounds FamilyCuspTaylor

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedAddCommGroup
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  ContinuousMultilinearMap.normedAddCommGroup'

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedSpace ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  ContinuousMultilinearMap.normedSpace'

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    ContinuousENorm
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  SeminormedAddGroup.toContinuousENorm

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  PseudoEMetricSpace.pseudoMetrizableSpace

/-- The Taylor series, at the real vertices `real`, of the joint right orbit of the cusp lift of
a family of plane sections at the local standard argument with local coordinates `coordinates`. -/
def localFamilySeries {degree arity : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (real : Fin (arity + 1) → RealGL3) (argument : AdelicGL)
    (coordinates : LocalLine × LocalLine) :
    FormalMultilinearSeries ℝ (SmoothJets.MatrixTuples 3 arity.succ) data.cusp.H :=
  coefficients (FamilyCuspTaylor.matrixOrbit data .plane parameter function induced
    (weyl⁻¹ * localRadical coordinates * argument)) (fun index => (real index).val)

theorem localFamilySeries_continuous {degree arity : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (lift : HasSmoothCuspLift data .plane parameter function) (real : Fin (arity + 1) → RealGL3)
    (argument : AdelicGL) (order : ℕ) :
    Continuous (fun coordinates =>
      localFamilySeries data parameter function induced real argument coordinates order) :=
  (FamilyCuspTaylor.coefficients_continuous data .plane parameter function induced lift real
    order).comp ((continuous_const.mul localRadical_continuous).mul continuous_const)

/-- A common ball of convergence and an integrable geometric majorant of the Taylor coefficients,
at the vertices `real`, of the joint right orbits of the cusp lifts at the points of the local
integrand. -/
structure LocalFamilyTaylorMajorant {degree arity : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (real : Fin (arity + 1) → RealGL3) (argument : AdelicGL) where
  radius : ℝ≥0
  radius_pos : 0 < radius
  bound : LocalLine × LocalLine → ℝ
  integrable : Integrable bound localRadicalMeasure
  expansions : ∀ coordinates, HasFPowerSeriesOnBall
    (FamilyCuspTaylor.matrixOrbit data .plane parameter function induced
      (weyl⁻¹ * localRadical coordinates * argument))
    (localFamilySeries data parameter function induced real argument coordinates)
    (fun index => (real index).val) radius
  dominates : ∀ coordinates order,
    ‖localFamilySeries data parameter function induced real argument coordinates order‖ ≤
      bound coordinates * (radius : ℝ)⁻¹ ^ order

/-- The local standard integral of a vertex family of plane sections. -/
def localFamilyValue {degree arity : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (vertices : Fin arity → RealGL3) (argument : AdelicGL) : data.cusp.H :=
  localValue data parameter (function vertices) (induced vertices) argument

namespace LocalFamilyTaylorMajorant

variable {degree arity : ℕ} {data : InducingData degree} {parameter : ℂ}
  {function : (Fin arity → RealGL3) → AdelicGL → ℂ}
  {induced : ∀ vertices, IsInduced data .plane parameter (function vertices)}
  {real : Fin (arity + 1) → RealGL3} {argument : AdelicGL}

/-- The Taylor coefficients of the local integrand are Bochner integrable, with a geometric bound
on their integral norms. -/
theorem coefficient_bounds (lift : HasSmoothCuspLift data .plane parameter function)
    (majorant : LocalFamilyTaylorMajorant data parameter function induced real argument)
    (order : ℕ) :
    Integrable (fun coordinates =>
      localFamilySeries data parameter function induced real argument coordinates order)
        localRadicalMeasure ∧
      (∫ coordinates, ‖localFamilySeries data parameter function induced real argument
        coordinates order‖ ∂localRadicalMeasure) ≤
          (∫ coordinates, majorant.bound coordinates ∂localRadicalMeasure) *
            (majorant.radius : ℝ)⁻¹ ^ order := by
  have dominating : Integrable (fun coordinates =>
      majorant.bound coordinates * (majorant.radius : ℝ)⁻¹ ^ order) localRadicalMeasure :=
    majorant.integrable.mul_const _
  have integrable : Integrable (fun coordinates =>
      localFamilySeries data parameter function induced real argument coordinates order)
        localRadicalMeasure :=
    dominating.mono' (localFamilySeries_continuous data parameter function induced lift real
      argument order).aestronglyMeasurable (Eventually.of_forall (fun coordinates =>
        majorant.dominates coordinates order))
  refine ⟨integrable, ?_⟩
  calc
    _ ≤ ∫ coordinates, majorant.bound coordinates * (majorant.radius : ℝ)⁻¹ ^ order
          ∂localRadicalMeasure :=
      integral_mono integrable.norm dominating (fun coordinates =>
        majorant.dominates coordinates order)
    _ = _ := integral_mul_const _ _

/-- The local standard integral of a vertex family has a power series expansion in the vertices
and the right translation. -/
theorem value_expansion (lift : HasSmoothCuspLift data .plane parameter function)
    (majorant : LocalFamilyTaylorMajorant data parameter function induced real argument) :
    HasFPowerSeriesOnBall
      (AdelicFamilyTaylor.matrixOrbit (localFamilyValue data parameter function induced) argument)
      (fun order => ∫ coordinates,
        localFamilySeries data parameter function induced real argument coordinates order
          ∂localRadicalMeasure)
      (fun index => (real index).val) majorant.radius := by
  have expansion := TaylorIntegral.hasFPowerSeriesOnBall localRadicalMeasure
    (fun coordinates => FamilyCuspTaylor.matrixOrbit data .plane parameter function induced
      (weyl⁻¹ * localRadical coordinates * argument))
    (localFamilySeries data parameter function induced real argument)
    (fun index => (real index).val) majorant.radius majorant.radius_pos
    (∫ coordinates, majorant.bound coordinates ∂localRadicalMeasure)
    majorant.expansions (fun order => (majorant.coefficient_bounds lift order).1)
    (fun order => (majorant.coefficient_bounds lift order).2)
  apply expansion.congr
  intro matrices _
  change (∫ coordinates, FamilyCuspTaylor.matrixOrbit data .plane parameter function induced
      (weyl⁻¹ * localRadical coordinates * argument) matrices ∂localRadicalMeasure) =
    localValue data parameter (function (fun index => invertibleMatrix (matrices index.castSucc)))
      (induced (fun index => invertibleMatrix (matrices index.castSucc)))
      (argument * atInfinity (invertibleMatrix (matrices (Fin.last arity))))
  unfold localValue
  apply integral_congr_ae
  filter_upwards [] with coordinates
  simp only [FamilyCuspTaylor.matrixOrbit, AdelicFamilyTaylor.matrixOrbit,
    SmoothJets.matrixExtension, AdelicFamilyTaylor.orbit, FamilyCuspLift.vector, localIntegrand,
    mul_assoc]

end LocalFamilyTaylorMajorant

/-- The local standard integral of a vertex family of plane sections is jointly smooth in the
vertices and the real right translation, when the Taylor majorants exist at every real tuple. -/
theorem localFamilyValue_joint_smooth {degree arity : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (lift : HasSmoothCuspLift data .plane parameter function) (argument : AdelicGL)
    (majorant : ∀ real : Fin (arity + 1) → RealGL3,
      LocalFamilyTaylorMajorant data parameter function induced real argument) :
    Smooth (AdelicFamilyTaylor.orbit (localFamilyValue data parameter function induced)
      argument) := by
  apply (SmoothAnalyticity.smooth_iff_analyticOn _).mpr
  intro matrices membership
  have expansion := (majorant (fun index => invertibleMatrix (matrices index))).value_expansion lift
  have analytic := expansion.analyticAt
  simp only [TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth.invertibleMatrix_val
    _ (membership _)] at analytic
  exact analytic.analyticWithinAt

end TernaryPeriodPolynomials.EdgeConvergence
