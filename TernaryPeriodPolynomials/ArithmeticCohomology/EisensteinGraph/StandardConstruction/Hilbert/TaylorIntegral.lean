module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.TaylorMajorant
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TaylorIntegral

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertTaylorIntegral

open CompactTaylorBounds CuspTaylorBounds AdelicTaylorBounds

local instance {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin order => Matrices) E) :=
  ContinuousMultilinearMap.normedAddCommGroup'

local instance {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin order => Matrices) E) :=
  ContinuousMultilinearMap.normedSpace'

local instance {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    ContinuousENorm (ContinuousMultilinearMap ℝ (fun _ : Fin order => Matrices) E) :=
  SeminormedAddGroup.toContinuousENorm

local instance {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin order => Matrices) E) :=
  PseudoEMetricSpace.pseudoMetrizableSpace

def integrandSeries {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (coordinates : Adeles × Adeles) : FormalMultilinearSeries ℝ Matrices data.cusp.H :=
  coefficients (matrixOrbit data .plane parameter function induced
    (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument)) 1

theorem integrandSeries_continuous {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (order : ℕ) :
    Continuous (fun coordinates => integrandSeries data parameter function induced argument coordinates order) :=
  (CuspTaylorBounds.coefficients_continuous data .plane parameter function induced order).comp
    ((continuous_const.mul InducedContinuity.lineUnipotent_continuous).mul continuous_const)

/-- The full standard-integral coefficients are Bochner integrable, and their
integral norms satisfy a single geometric estimate. -/
theorem integrandSeries_bounds {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      (∀ coordinates, HasFPowerSeriesOnBall
        (matrixOrbit data .plane parameter function induced
          (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument))
        (integrandSeries data parameter function induced argument coordinates) 1 radius) ∧
      ∀ order,
        Integrable (fun coordinates => integrandSeries data parameter function induced argument coordinates order)
          radicalMeasure ∧
        (∫ coordinates, ‖integrandSeries data parameter function induced argument coordinates order‖
          ∂radicalMeasure) ≤ constant * (radius : ℝ)⁻¹ ^ order := by
  obtain ⟨radius, positive, majorant, nonnegative, summable, expansions, bounded⟩ :=
    CuspTaylorMajorant.domain_majorant data parameter function induced halfPlane argument
  let openMajorant := fun rational => majorant (BruhatCells.openFlag rational)
  have openNonnegative : ∀ rational, 0 ≤ openMajorant rational := fun _ => nonnegative _
  have openSummable : Summable openMajorant := summable.comp_injective BruhatCells.openFlag_injective
  refine ⟨radius, positive, ∑' rational, openMajorant rational, tsum_nonneg openNonnegative,
    fun coordinates => expansions _, ?_⟩
  intro order
  have estimate := RadicalIntegralBound.integrable_norm_bound
    (fun coordinates => integrandSeries data parameter function induced argument coordinates order)
    (integrandSeries_continuous data parameter function induced argument order).aestronglyMeasurable
    (fun rational => openMajorant rational * (radius : ℝ)⁻¹ ^ order)
    (fun rational => mul_nonneg (openNonnegative rational) (pow_nonneg (inv_nonneg.mpr radius.property) _))
    (openSummable.mul_right _)
    (by
      intro rational coordinates membership
      have bound := bounded coordinates membership (BruhatCells.openRepresentative rational) order
      rw [CuspTaylorMajorant.open_shift] at bound
      exact bound)
  refine ⟨estimate.1, ?_⟩
  simpa only [tsum_mul_right] using estimate.2

theorem value_expansion {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    ∃ radius : ℝ≥0, 0 < radius ∧
      HasFPowerSeriesOnBall (rightMatrix (HilbertStandard.value data parameter function induced) argument)
        (fun order => ∫ coordinates,
          integrandSeries data parameter function induced argument coordinates order ∂radicalMeasure) 1 radius := by
  obtain ⟨radius, positive, constant, _, expansions, bounded⟩ :=
    integrandSeries_bounds data parameter function induced halfPlane argument
  refine ⟨radius, positive, ?_⟩
  have expansion := TaylorIntegral.hasFPowerSeriesOnBall radicalMeasure
    (fun coordinates => matrixOrbit data .plane parameter function induced
      (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument))
    (integrandSeries data parameter function induced argument) 1 radius positive constant expansions
    (fun order => (bounded order).1) (fun order => (bounded order).2)
  apply expansion.congr
  intro matrices _
  change (∫ coordinates, matrixOrbit data .plane parameter function induced
    (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument) matrices ∂radicalMeasure) =
      (∫ coordinates, HilbertStandard.integrand data parameter function induced
        (argument * atInfinity (invertibleMatrix (matrices 0))) coordinates ∂radicalMeasure)
  apply integral_congr_ae
  filter_upwards [] with coordinates
  simp only [rightMatrix, SmoothJets.matrixExtension, HilbertStandard.integrand,
    matrixOrbit, mul_assoc]

theorem value_analyticAt_one {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    AnalyticAt ℝ (rightMatrix (HilbertStandard.value data parameter function induced) argument) 1 := by
  obtain ⟨radius, _, expansion⟩ := value_expansion data parameter function induced halfPlane argument
  exact expansion.analyticAt

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertTaylorIntegral
