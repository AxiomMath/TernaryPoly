module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.TaylorBounds

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter Topology
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicFamilyTaylor

open CompactTaylorBounds SmoothJets

variable {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def orbit (function : (Fin arity → RealGL3) → AdelicGL → E) (argument : AdelicGL)
    (real : Fin (arity + 1) → RealGL3) : E :=
  function (fun index => real index.castSucc) (argument * atInfinity (real (Fin.last arity)))

def matrixOrbit (function : (Fin arity → RealGL3) → AdelicGL → E) (argument : AdelicGL) :
    MatrixTuples 3 arity.succ → E := matrixExtension (orbit function argument)

def leftUnits (argument : AdelicGL) : Fin (arity + 1) → RealGL3 :=
  fun index => if index = Fin.last arity then realGroup argument else 1

theorem leftUnits_continuous : Continuous (leftUnits (arity := arity)) := by
  apply continuous_pi
  intro index
  by_cases last : index = Fin.last arity
  · simpa only [leftUnits, ite_eq_left last] using InducedContinuity.realGroup_continuous
  · simpa only [leftUnits, ite_eq_right last] using (continuous_const : Continuous (fun _ : AdelicGL => (1 : RealGL3)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
theorem finite_local_formula (function : (Fin arity → RealGL3) → AdelicGL → E)
    (invariant : ∀ vertices, ∀ level : finiteLevel, ∀ argument,
      function vertices (argument * atFinite level.val) = function vertices argument)
    (reference : FiniteGL) (argument : AdelicGL)
    (membership : reference⁻¹ * finiteGroup argument ∈ finiteLevel)
    (real : Fin (arity + 1) → RealGL3) :
    orbit function argument real = orbit function (atFinite reference)
      (fun index => leftUnits argument index * real index) := by
  simp only [orbit, leftUnits, Fin.castSucc_ne_last, ite_false, one_mul, ite_true]
  exact AdelicJets.finite_local_formula _ (invariant _) reference argument membership _

theorem local_uniform (function : (Fin arity → RealGL3) → AdelicGL → E)
    (smooth : ∀ argument, Smooth (orbit function argument))
    (invariant : ∀ vertices, ∀ level : finiteLevel, ∀ argument,
      function vertices (argument * atFinite level.val) = function vertices argument)
    (real : Fin (arity + 1) → RealGL3) (base : AdelicGL) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ᶠ argument in 𝓝 base,
        HasFPowerSeriesOnBall (matrixOrbit function argument)
          (coefficients (matrixOrbit function argument) (fun index => (real index).val))
          (fun index => (real index).val) radius ∧
        ∀ order, ‖coefficients (matrixOrbit function argument) (fun index => (real index).val) order‖ ≤
          constant * (radius : ℝ)⁻¹ ^ order := by
  let center : MatrixTuples 3 arity.succ := fun index => (real index).val
  let reference := finiteGroup base
  let coordinates : AdelicGL → MatrixTuples 3 arity.succ :=
    fun argument index => (leftUnits argument index).val
  let fixed := matrixOrbit function (atFinite reference)
  let multiplication : MatrixTuples 3 arity.succ →L[ℝ]
      MatrixTuples 3 arity.succ →L[ℝ] MatrixTuples 3 arity.succ :=
    TranslatedJets.leftMulLinear.toContinuousLinearMap
  have inDomain : multiplication (coordinates base) center ∈ domain 3 arity.succ := by
    intro index
    change ((leftUnits base index).val * (real index).val).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (GeneralLinearGroup.det_ne_zero _) (GeneralLinearGroup.det_ne_zero _)
  have baseAnalytic : AnalyticAt ℝ fixed (multiplication (coordinates base) center) :=
    AnalyticOn.analyticAt ((domain_open 3 arity.succ).mem_nhds inDomain)
      ((SmoothAnalyticity.smooth_iff_analyticOn _).mp (smooth (atFinite reference)))
  let joint : MatrixTuples 3 arity.succ × MatrixTuples 3 arity.succ → E :=
    fun pair => fixed (multiplication pair.1 pair.2)
  have jointAnalytic : AnalyticAt ℝ joint (coordinates base, center) :=
    AnalyticAt.comp (g := fixed)
      (f := fun pair : MatrixTuples 3 arity.succ × MatrixTuples 3 arity.succ => multiplication pair.1 pair.2)
      (x := (coordinates base, center)) baseAnalytic
      (multiplication.analyticAt_bilinear (coordinates base, center))
  obtain ⟨largeRadius, largePositive, constant, nonnegative, bounded⟩ :=
    CompactTaylorBounds.local_uniform jointAnalytic
  have centerMembership : center ∈ domain 3 arity.succ := fun index => GeneralLinearGroup.det_ne_zero _
  obtain ⟨epsilon, epsilonPositive, inDomainBall⟩ :=
    Metric.mem_nhds_iff.mp ((domain_open 3 arity.succ).mem_nhds centerMembership)
  let domainRadius : ℝ≥0 := ⟨epsilon, epsilonPositive.le⟩
  let radius := min largeRadius domainRadius
  have positive : 0 < radius := lt_min largePositive epsilonPositive
  have coordinatesContinuous : Continuous coordinates := continuous_pi (fun index =>
    Units.continuous_val.comp ((continuous_apply index).comp leftUnits_continuous))
  have nearReal : ∀ᶠ argument in 𝓝 base,
      (coordinates argument, center) ∈ Metric.ball (coordinates base, center) largeRadius :=
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
    (bounded (coordinates argument, center) realNear).1 constant
    (bounded (coordinates argument, center) realNear).2
  have smaller := TaylorFamilies.weaken positive (min_le_left _ _) nonnegative le_rfl restricted
  apply TaylorFamilies.congr positive constant smaller
  intro matrices membership
  have invertible : matrices ∈ domain 3 arity.succ := inDomainBall
    (Metric.ball_subset_ball (show (radius : ℝ) ≤ epsilon from
      NNReal.coe_le_coe.mpr (min_le_right _ _)) membership)
  have equality := finite_local_formula function invariant reference argument finiteNear
    (fun index => invertibleMatrix (matrices index))
  unfold matrixOrbit matrixExtension
  change orbit function (atFinite reference)
      (fun index => invertibleMatrix ((leftUnits argument index).val * matrices index)) = _
  simp only [TranslatedJets.invertibleMatrix_mul_left _ _ (invertible _)]
  exact equality.symm

theorem uniform_on_compact (function : (Fin arity → RealGL3) → AdelicGL → E)
    (smooth : ∀ argument, Smooth (orbit function argument))
    (invariant : ∀ vertices, ∀ level : finiteLevel, ∀ argument,
      function vertices (argument * atFinite level.val) = function vertices argument)
    (real : Fin (arity + 1) → RealGL3) (compact : Set AdelicGL) (compactness : IsCompact compact) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ argument ∈ compact,
        HasFPowerSeriesOnBall (matrixOrbit function argument)
          (coefficients (matrixOrbit function argument) (fun index => (real index).val))
          (fun index => (real index).val) radius ∧
        ∀ order, ‖coefficients (matrixOrbit function argument) (fun index => (real index).val) order‖ ≤
          constant * (radius : ℝ)⁻¹ ^ order :=
  TaylorFamilies.uniform_on_compact (matrixOrbit function) _ compact compactness
    (fun argument _ => local_uniform function smooth invariant real argument)

omit [CompleteSpace E] in
theorem jet_continuous (function : (Fin arity → RealGL3) → AdelicGL → E)
    (smooth : ∀ argument, Smooth (orbit function argument))
    (invariant : ∀ vertices, ∀ level : finiteLevel, ∀ argument,
      function vertices (argument * atFinite level.val) = function vertices argument) (order : ℕ) :
    Continuous (fun pair : AdelicGL × (Fin (arity + 1) → RealGL3) =>
      SmoothJets.jet order (orbit function pair.1) pair.2) := by
  apply continuous_iff_continuousAt.mpr
  intro pair
  have localContinuous : Continuous (fun other : AdelicGL × (Fin (arity + 1) → RealGL3) =>
      SmoothJets.jet order (fun elements => orbit function (atFinite (finiteGroup pair.1))
        (fun index => leftUnits other.1 index * elements index)) other.2) := by
    have translation := TranslatedJets.jet_mul_left_continuous
      (orbit function (atFinite (finiteGroup pair.1))) (smooth (atFinite (finiteGroup pair.1))) order
    exact translation.comp ((leftUnits_continuous.comp continuous_fst).prodMk continuous_snd)
  have near : ∀ᶠ other : AdelicGL × (Fin (arity + 1) → RealGL3) in 𝓝 pair,
      (finiteGroup pair.1)⁻¹ * finiteGroup other.1 ∈ finiteLevel :=
    (FiniteLevelTopology.finiteLevel_isOpen.preimage
      (continuous_const.mul (InducedContinuity.finiteGroup_continuous.comp continuous_fst))).mem_nhds
        (by simp)
  apply localContinuous.continuousAt.congr_of_eventuallyEq
  filter_upwards [near] with other membership
  have equality : orbit function other.1 = fun elements =>
      orbit function (atFinite (finiteGroup pair.1))
        (fun index => leftUnits other.1 index * elements index) :=
    funext (fun elements => finite_local_formula function invariant (finiteGroup pair.1) other.1 membership elements)
  rw [equality]

omit [CompleteSpace E] in
theorem coefficients_eq_jet (function : (Fin arity → RealGL3) → AdelicGL → E)
    (argument : AdelicGL) (real : Fin (arity + 1) → RealGL3) (order : ℕ) :
    coefficients (matrixOrbit function argument) (fun index => (real index).val) order =
      (order.factorial : ℝ)⁻¹ • SmoothJets.jet order (orbit function argument) real := by
  unfold coefficients SmoothJets.jet matrixOrbit
  congr 1
  exact ((iteratedFDerivWithin_of_isOpen order (domain_open 3 arity.succ))
    (show (fun index => (real index).val) ∈ domain 3 arity.succ from
      fun _ => GeneralLinearGroup.det_ne_zero _)).symm

omit [CompleteSpace E] in
theorem coefficients_continuous (function : (Fin arity → RealGL3) → AdelicGL → E)
    (smooth : ∀ argument, Smooth (orbit function argument))
    (invariant : ∀ vertices, ∀ level : finiteLevel, ∀ argument,
      function vertices (argument * atFinite level.val) = function vertices argument)
    (real : Fin (arity + 1) → RealGL3) (order : ℕ) :
    Continuous (fun argument =>
      coefficients (matrixOrbit function argument) (fun index => (real index).val) order) := by
  simp_rw [coefficients_eq_jet]
  exact ((jet_continuous function smooth invariant order).comp
    (continuous_id.prodMk continuous_const)).const_smul (order.factorial : ℝ)⁻¹

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicFamilyTaylor
