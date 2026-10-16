module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TaylorFamilies
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.Jets
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.Analyticity

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter Topology
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicTaylorBounds

open SmoothJets CompactTaylorBounds

abbrev Matrices := MatrixTuples 3 1

def rightMatrix {E : Type} (function : AdelicGL → E) (argument : AdelicGL) : Matrices → E :=
  matrixExtension (fun elements : Fin 1 → RealGL3 => function (argument * atInfinity (elements 0)))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem local_uniform (function : AdelicGL → E)
    (smooth : ∀ argument, Smooth (fun elements : Fin 1 → RealGL3 =>
      function (argument * atInfinity (elements 0))))
    (invariant : ∀ level : finiteLevel, ∀ argument,
      function (argument * atFinite level.val) = function argument)
    (base : AdelicGL) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ᶠ argument in 𝓝 base,
        HasFPowerSeriesOnBall (rightMatrix function argument)
          (coefficients (rightMatrix function argument) 1) 1 radius ∧
        ∀ order, ‖coefficients (rightMatrix function argument) 1 order‖ ≤
          constant * (radius : ℝ)⁻¹ ^ order := by
  let reference := finiteGroup base
  let coordinates : AdelicGL → Matrices := fun argument _ => (realGroup argument).val
  let fixed := matrixExtension (fun elements : Fin 1 → RealGL3 =>
    function (atFinite reference * atInfinity (elements 0)))
  let multiplication : Matrices →L[ℝ] Matrices →L[ℝ] Matrices :=
    TranslatedJets.leftMulLinear.toContinuousLinearMap
  have multiplyOne (matrices : Matrices) : multiplication matrices 1 = matrices := by
    funext index
    change matrices index * 1 = matrices index
    exact mul_one _
  have baseAnalytic : AnalyticAt ℝ fixed (multiplication (coordinates base) 1) := by
    rw [multiplyOne]
    exact AnalyticOn.analyticAt ((domain_open 3 1).mem_nhds
      (fun _ => GeneralLinearGroup.det_ne_zero _))
      ((SmoothAnalyticity.smooth_iff_analyticOn _).mp (smooth (atFinite reference)))
  let joint : Matrices × Matrices → E := fun pair => fixed (multiplication pair.1 pair.2)
  have jointAnalytic : AnalyticAt ℝ joint (coordinates base, 1) := by
    exact AnalyticAt.comp (g := fixed)
      (f := fun pair : Matrices × Matrices => multiplication pair.1 pair.2)
      (x := (coordinates base, 1)) baseAnalytic
      (multiplication.analyticAt_bilinear (coordinates base, 1))
  obtain ⟨largeRadius, largePositive, constant, nonnegative, bounded⟩ :=
    CompactTaylorBounds.local_uniform jointAnalytic
  have identityMembership : (1 : Matrices) ∈ domain 3 1 := by
    intro index
    change (1 : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0
    simp
  obtain ⟨epsilon, epsilonPositive, inDomain⟩ :=
    Metric.mem_nhds_iff.mp ((domain_open 3 1).mem_nhds identityMembership)
  let domainRadius : ℝ≥0 := ⟨epsilon, epsilonPositive.le⟩
  let radius := min largeRadius domainRadius
  have positive : 0 < radius := lt_min largePositive epsilonPositive
  have coordinatesContinuous : Continuous coordinates :=
    continuous_pi (fun _ => Units.continuous_val.comp InducedContinuity.realGroup_continuous)
  have nearReal : ∀ᶠ argument in 𝓝 base,
      (coordinates argument, (1 : Matrices)) ∈ Metric.ball (coordinates base, 1) largeRadius :=
    (coordinatesContinuous.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds _ (by exact_mod_cast largePositive))
  have nearFinite : ∀ᶠ argument in 𝓝 base,
      reference⁻¹ * finiteGroup argument ∈ finiteLevel :=
    (FiniteLevelTopology.finiteLevel_isOpen.preimage
      (continuous_const.mul InducedContinuity.finiteGroup_continuous)).mem_nhds (by
        dsimp [reference]
        simp)
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  filter_upwards [nearReal, nearFinite] with argument realNear finiteNear
  have restricted := TaylorFamilies.restrict_snd largePositive
    (bounded (coordinates argument, 1) realNear).1 constant
    (bounded (coordinates argument, 1) realNear).2
  have smaller := TaylorFamilies.weaken positive (min_le_left _ _) nonnegative le_rfl restricted
  apply TaylorFamilies.congr positive constant smaller
  intro matrices membership
  have invertible : matrices ∈ domain 3 1 := inDomain
    (Metric.ball_subset_ball (show (radius : ℝ) ≤ epsilon from
      NNReal.coe_le_coe.mpr (min_le_right _ _)) membership)
  change function (atFinite reference * atInfinity (invertibleMatrix
      ((realGroup argument).val * matrices 0))) =
    function (argument * atInfinity (invertibleMatrix (matrices 0)))
  rw [TranslatedJets.invertibleMatrix_mul_left _ _ (invertible 0)]
  exact (AdelicJets.finite_local_formula function invariant reference argument finiteNear _).symm

/-- The actual finite level and analytic real orbits give a common Taylor radius
and coefficient bound on any compact adelic set. -/
theorem uniform_on_compact (function : AdelicGL → E)
    (smooth : ∀ argument, Smooth (fun elements : Fin 1 → RealGL3 =>
      function (argument * atInfinity (elements 0))))
    (invariant : ∀ level : finiteLevel, ∀ argument,
      function (argument * atFinite level.val) = function argument)
    (compact : Set AdelicGL) (compactness : IsCompact compact) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ argument ∈ compact,
        HasFPowerSeriesOnBall (rightMatrix function argument)
          (coefficients (rightMatrix function argument) 1) 1 radius ∧
        ∀ order, ‖coefficients (rightMatrix function argument) 1 order‖ ≤
          constant * (radius : ℝ)⁻¹ ^ order :=
  TaylorFamilies.uniform_on_compact (rightMatrix function) 1 compact compactness
    (fun argument _ => local_uniform function smooth invariant argument)

omit [CompleteSpace E] in
theorem coefficients_eq_rightJet (function : AdelicGL → E) (argument : AdelicGL) (order : ℕ) :
    coefficients (rightMatrix function argument) 1 order =
      (order.factorial : ℝ)⁻¹ • AdelicJets.rightJet order function argument 1 := by
  unfold coefficients AdelicJets.rightJet SmoothJets.jet rightMatrix
  congr 1
  exact ((iteratedFDerivWithin_of_isOpen order (domain_open 3 1))
    (show (1 : Matrices) ∈ domain 3 1 by intro index; change (1 : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0; simp)).symm

omit [CompleteSpace E] in
theorem coefficients_continuous (function : AdelicGL → E)
    (smooth : ∀ argument, Smooth (fun elements : Fin 1 → RealGL3 =>
      function (argument * atInfinity (elements 0))))
    (invariant : ∀ level : finiteLevel, ∀ argument,
      function (argument * atFinite level.val) = function argument) (order : ℕ) :
    Continuous (fun argument => coefficients (rightMatrix function argument) 1 order) := by
  simp_rw [coefficients_eq_rightJet]
  exact ((AdelicJets.rightJet_continuous function smooth invariant order).comp
    (continuous_id.prodMk continuous_const)).const_smul (order.factorial : ℝ)⁻¹

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicTaylorBounds
