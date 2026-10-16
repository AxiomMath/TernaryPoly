module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FamilyCuspMajorant
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TaylorIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.OrbitSmooth

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FamilyHilbertIntegral

open CompactTaylorBounds FamilyCuspTaylor

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  ContinuousMultilinearMap.normedAddCommGroup'

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  ContinuousMultilinearMap.normedSpace'

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    ContinuousENorm (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  SeminormedAddGroup.toContinuousENorm

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  PseudoEMetricSpace.pseudoMetrizableSpace

def integrandSeries {degree arity : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ) (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (real : Fin (arity + 1) → RealGL3)
    (argument : AdelicGL) (coordinates : Adeles × Adeles) : FormalMultilinearSeries ℝ (SmoothJets.MatrixTuples 3 arity.succ) data.cusp.H :=
  coefficients (matrixOrbit data .plane parameter function induced
    (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument)) (fun index => (real index).val)

theorem integrandSeries_continuous {degree arity : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ) (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (lift : HasSmoothCuspLift data .plane parameter function) (real : Fin (arity + 1) → RealGL3)
    (argument : AdelicGL) (order : ℕ) :
    Continuous (fun coordinates => integrandSeries data parameter function induced real argument coordinates order) :=
  (FamilyCuspTaylor.coefficients_continuous data .plane parameter function induced lift real order).comp
    ((continuous_const.mul InducedContinuity.lineUnipotent_continuous).mul continuous_const)

/-- The full standard-integral coefficients are Bochner integrable, and their
integral norms satisfy a single geometric estimate. -/
theorem integrandSeries_bounds {degree arity : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ) (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (lift : HasSmoothCuspLift data .plane parameter function) (real : Fin (arity + 1) → RealGL3)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      (∀ coordinates, HasFPowerSeriesOnBall
        (matrixOrbit data .plane parameter function induced
          (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument))
        (integrandSeries data parameter function induced real argument coordinates) (fun index => (real index).val) radius) ∧
      ∀ order,
        Integrable (fun coordinates => integrandSeries data parameter function induced real argument coordinates order)
          radicalMeasure ∧
        (∫ coordinates, ‖integrandSeries data parameter function induced real argument coordinates order‖
          ∂radicalMeasure) ≤ constant * (radius : ℝ)⁻¹ ^ order := by
  obtain ⟨radius, positive, majorant, nonnegative, summable, expansions, bounded⟩ :=
    FamilyCuspMajorant.domain_majorant data parameter function induced lift real halfPlane argument
  let openMajorant := fun rational => majorant (BruhatCells.openFlag rational)
  have openNonnegative : ∀ rational, 0 ≤ openMajorant rational := fun _ => nonnegative _
  have openSummable : Summable openMajorant := summable.comp_injective BruhatCells.openFlag_injective
  refine ⟨radius, positive, ∑' rational, openMajorant rational, tsum_nonneg openNonnegative,
    fun coordinates => expansions _, ?_⟩
  intro order
  have estimate := RadicalIntegralBound.integrable_norm_bound
    (fun coordinates => integrandSeries data parameter function induced real argument coordinates order)
    (integrandSeries_continuous data parameter function induced lift real argument order).aestronglyMeasurable
    (fun rational => openMajorant rational * (radius : ℝ)⁻¹ ^ order)
    (fun rational => mul_nonneg (openNonnegative rational) (pow_nonneg (inv_nonneg.mpr radius.property) _))
    (openSummable.mul_right _)
    (by
      intro rational coordinates membership
      have bound := bounded coordinates membership (BruhatCells.openRepresentative rational) order
      rw [FamilyCuspMajorant.open_shift] at bound
      exact bound)
  refine ⟨estimate.1, ?_⟩
  simpa only [tsum_mul_right] using estimate.2

def value {degree arity : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (vertices : Fin arity → RealGL3) (argument : AdelicGL) : data.cusp.H :=
  HilbertStandard.value data parameter (function vertices) (induced vertices) argument

theorem value_expansion {degree arity : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (lift : HasSmoothCuspLift data .plane parameter function) (real : Fin (arity + 1) → RealGL3)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    ∃ radius : ℝ≥0, 0 < radius ∧
      HasFPowerSeriesOnBall (AdelicFamilyTaylor.matrixOrbit (value data parameter function induced) argument)
        (fun order => ∫ coordinates,
          integrandSeries data parameter function induced real argument coordinates order ∂radicalMeasure)
        (fun index => (real index).val) radius := by
  obtain ⟨radius, positive, constant, _, expansions, bounded⟩ :=
    integrandSeries_bounds data parameter function induced lift real halfPlane argument
  refine ⟨radius, positive, ?_⟩
  have expansion := TaylorIntegral.hasFPowerSeriesOnBall radicalMeasure
    (fun coordinates => matrixOrbit data .plane parameter function induced
      (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument))
    (integrandSeries data parameter function induced real argument) (fun index => (real index).val)
    radius positive constant expansions (fun order => (bounded order).1) (fun order => (bounded order).2)
  apply expansion.congr
  intro matrices _
  change (∫ coordinates, matrixOrbit data .plane parameter function induced
      (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument) matrices ∂radicalMeasure) =
    ∫ coordinates, HilbertStandard.integrand data parameter
      (function (fun index => invertibleMatrix (matrices index.castSucc))) _
      (argument * atInfinity (invertibleMatrix (matrices (Fin.last arity)))) coordinates ∂radicalMeasure
  apply integral_congr_ae
  filter_upwards [] with coordinates
  simp only [matrixOrbit, AdelicFamilyTaylor.matrixOrbit, SmoothJets.matrixExtension,
    AdelicFamilyTaylor.orbit, FamilyCuspLift.vector, HilbertStandard.integrand, mul_assoc]

theorem joint_smooth {degree arity : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (lift : HasSmoothCuspLift data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    Smooth (AdelicFamilyTaylor.orbit (value data parameter function induced) argument) := by
  apply (SmoothAnalyticity.smooth_iff_analyticOn _).mpr
  intro matrices membership
  obtain ⟨radius, _, expansion⟩ := value_expansion data parameter function induced lift
    (fun index => invertibleMatrix (matrices index)) halfPlane argument
  have analytic := expansion.analyticAt
  simp only [TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth.invertibleMatrix_val _ (membership _)] at analytic
  exact analytic.analyticWithinAt

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FamilyHilbertIntegral
