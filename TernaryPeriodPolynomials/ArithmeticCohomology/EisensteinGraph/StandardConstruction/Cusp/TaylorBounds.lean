module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.TaylorBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.UniformJets
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.HilbertAction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter Topology
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspTaylorBounds

open CompactTaylorBounds AdelicTaylorBounds

def matrixOrbit {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data side parameter function)
    (argument : AdelicGL) : Matrices → data.cusp.H :=
  rightMatrix (fun point => (CuspLift.vector data side parameter function induced point).val) argument

theorem uniform_on_compact {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data side parameter function)
    (compact : Set AdelicGL) (compactness : IsCompact compact) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ argument ∈ compact,
        HasFPowerSeriesOnBall (matrixOrbit data side parameter function induced argument)
          (coefficients (matrixOrbit data side parameter function induced argument) 1) 1 radius ∧
        ∀ order, ‖coefficients (matrixOrbit data side parameter function induced argument) 1 order‖ ≤
          constant * (radius : ℝ)⁻¹ ^ order :=
  AdelicTaylorBounds.uniform_on_compact _ (CuspLift.real_smooth data side parameter function induced)
    (fun level argument => congrArg Subtype.val
      (CuspLift.finite_invariant data side parameter function induced argument level)) compact compactness

theorem maximalCompact_uniform {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data side parameter function) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ compact, inMaximalCompact compact →
        HasFPowerSeriesOnBall (matrixOrbit data side parameter function induced compact)
          (coefficients (matrixOrbit data side parameter function induced compact) 1) 1 radius ∧
        ∀ order, ‖coefficients (matrixOrbit data side parameter function induced compact) 1 order‖ ≤
          constant * (radius : ℝ)⁻¹ ^ order :=
  uniform_on_compact data side parameter function induced _ MaximalCompact.isCompact

theorem coefficients_continuous {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data side parameter function)
    (order : ℕ) : Continuous (fun argument =>
      coefficients (matrixOrbit data side parameter function induced argument) 1 order) :=
  AdelicTaylorBounds.coefficients_continuous _ (CuspLift.real_smooth data side parameter function induced)
    (fun level argument => congrArg Subtype.val
      (CuspLift.finite_invariant data side parameter function induced argument level)) order

def planeWeight (degree : ℕ) (parameter : ℂ) (binary : BinaryAdelicGL) (unit : Adelesˣ) : ℝ :=
  (adeleNorm unit : ℝ) ^ (-2 * inductionExponent .plane parameter).re *
    (adeleNorm (GeneralLinearGroup.det binary) : ℝ) ^
      (binaryInductionExponent degree .plane parameter).re

theorem planeWeight_nonnegative (degree : ℕ) (parameter : ℂ)
    (binary : BinaryAdelicGL) (unit : Adelesˣ) : 0 ≤ planeWeight degree parameter binary unit :=
  mul_nonneg (Real.rpow_nonneg (adeleNorm unit).property _)
    (Real.rpow_nonneg (adeleNorm (GeneralLinearGroup.det binary)).property _)

def planeOperator {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (binary : BinaryAdelicGL) (unit : Adelesˣ) : data.cusp.H →L[ℝ] data.cusp.H :=
  ((data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter) *
    normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter)) •
      (CuspHilbertAction.isometry data.cusp binary).toContinuousLinearMap).restrictScalars ℝ

theorem planeOperator_norm_le {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (binary : BinaryAdelicGL) (unit : Adelesˣ) :
    ‖planeOperator data parameter binary unit‖ ≤ planeWeight degree parameter binary unit := by
  apply ContinuousLinearMap.opNorm_le_bound _ (planeWeight_nonnegative degree parameter binary unit)
  intro vector
  change ‖(data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter) *
    normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter)) •
      data.cusp.π binary vector‖ ≤ _
  rw [norm_smul, norm_mul, norm_mul, data.chi.unitary, one_mul,
    NormPower.normPower_norm, NormPower.normPower_norm, data.cusp.unitary]
  exact le_rfl

theorem plane_decomposition {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ) (compact : AdelicGL) :
    matrixOrbit data .plane parameter function induced
        (planeUnipotent first second * planeLevi binary unit * compact) =
      planeOperator data parameter binary unit ∘ matrixOrbit data .plane parameter function induced compact := by
  funext matrices
  unfold matrixOrbit rightMatrix SmoothJets.matrixExtension
  dsimp only [Function.comp_def]
  rw [mul_assoc (planeUnipotent first second * planeLevi binary unit), mul_assoc,
    CuspLiftCovariance.vector_plane_radical, FlatUniqueness.planeLevi_split, mul_assoc,
    CuspLiftCovariance.vector_plane_rankOne]
  change (data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter)) •
      (CuspLift.vector data .plane parameter function induced
        (binaryLevi .plane binary * (compact * atInfinity (invertibleMatrix (matrices 0))))).val = _
  rw [CuspLiftCovariance.vector_binary, smul_smul]
  rfl

theorem plane_decomposition_bound {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    {radius : ℝ≥0} (positive : 0 < radius) (constant : ℝ)
    (bounded : ∀ compact, inMaximalCompact compact →
      HasFPowerSeriesOnBall (matrixOrbit data .plane parameter function induced compact)
        (coefficients (matrixOrbit data .plane parameter function induced compact) 1) 1 radius ∧
      ∀ order, ‖coefficients (matrixOrbit data .plane parameter function induced compact) 1 order‖ ≤
        constant * (radius : ℝ)⁻¹ ^ order)
    (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ)
    (compact : AdelicGL) (membership : inMaximalCompact compact) :
    HasFPowerSeriesOnBall
        (matrixOrbit data .plane parameter function induced
          (planeUnipotent first second * planeLevi binary unit * compact))
        (coefficients (matrixOrbit data .plane parameter function induced
          (planeUnipotent first second * planeLevi binary unit * compact)) 1) 1 radius ∧
      ∀ order, ‖coefficients (matrixOrbit data .plane parameter function induced
          (planeUnipotent first second * planeLevi binary unit * compact)) 1 order‖ ≤
        (planeWeight degree parameter binary unit * constant) * (radius : ℝ)⁻¹ ^ order := by
  rw [plane_decomposition]
  exact TaylorFamilies.map positive constant (bounded compact membership)
    (planeOperator data parameter binary unit) (planeWeight degree parameter binary unit)
    (planeWeight_nonnegative degree parameter binary unit) (planeOperator_norm_le data parameter binary unit)

theorem matrixOrbit_analyticAt_one {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data side parameter function)
    (argument : AdelicGL) : AnalyticAt ℝ (matrixOrbit data side parameter function induced argument) 1 := by
  apply AnalyticOn.analyticAt ((SmoothJets.domain_open 3 1).mem_nhds
    (show (1 : Matrices) ∈ SmoothJets.domain 3 1 by
      intro index; change (1 : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0; simp))
  exact (SmoothAnalyticity.smooth_iff_analyticOn _).mp
    (CuspLift.real_smooth data side parameter function induced argument)

theorem plane_coefficient_norm_le {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ)
    (argument : AdelicGL) (order : ℕ) :
    ‖coefficients (matrixOrbit data .plane parameter function induced
        (planeUnipotent first second * planeLevi binary unit * argument)) 1 order‖ ≤
      planeWeight degree parameter binary unit *
        ‖coefficients (matrixOrbit data .plane parameter function induced argument) 1 order‖ := by
  obtain ⟨radius, positive, constant, _, bounded⟩ := CompactTaylorBounds.local_uniform
    (matrixOrbit_analyticAt_one data .plane parameter function induced argument)
  have expansion := (bounded 1 (Metric.mem_ball_self (by exact_mod_cast positive))).1
  rw [plane_decomposition]
  apply (coefficients_norm_le
    ((planeOperator data parameter binary unit).comp_hasFPowerSeriesOnBall expansion) order).trans
  exact ((planeOperator data parameter binary unit).norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_right (planeOperator_norm_le data parameter binary unit) (norm_nonneg _))

theorem plane_common_radius {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∀ argument,
      HasFPowerSeriesOnBall (matrixOrbit data .plane parameter function induced argument)
        (coefficients (matrixOrbit data .plane parameter function induced argument) 1) 1 radius := by
  obtain ⟨radius, positive, constant, _, bounded⟩ :=
    maximalCompact_uniform data .plane parameter function induced
  refine ⟨radius, positive, ?_⟩
  intro argument
  obtain ⟨first, second, binary, unit, compact, membership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition argument
  rw [decomposition]
  exact (plane_decomposition_bound data parameter function induced positive constant bounded
    first second binary unit compact membership).1

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspTaylorBounds
