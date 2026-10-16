module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.SchwartzBounds
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.AdelicTheta

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaParameterBounds TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachAdelicTheta

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformThetaMajorants

variable {Target : Type} [NormedAddCommGroup Target] [NormedSpace ℂ Target]

theorem lattice {Space : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (tests : Set (SchwartzMap Space Target)) (testsBounded : UniformSchwartzBounds.Bounded tests) (distortion : ℝ) (distortionNonnegative : 0 ≤ distortion) :
    ∃ majorant : lattice → ℝ, Summable majorant ∧ (∀ point, 0 ≤ majorant point) ∧
      ∀ function ∈ tests, ∀ transform : Space →L[ℝ] Space, (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) →
        ∀ point : lattice, ‖function (transform point.val)‖ ≤ majorant point := by
  classical
  let order := Module.finrank ℤ lattice + 1
  obtain ⟨bound, nonnegative, decay⟩ := UniformSchwartzBounds.norm_pow_bound tests testsBounded order
  obtain ⟨zeroBound, zeroNonnegative, zeroBounds⟩ := UniformSchwartzBounds.norm_pow_bound tests testsBounded 0
  have atZero : ∀ function ∈ tests, ‖function 0‖ ≤ zeroBound := by
    intro function membership
    simpa only [pow_zero, one_mul] using zeroBounds function membership 0
  let majorant : lattice → ℝ := fun point =>
    (if point = 0 then zeroBound else 0) + distortion ^ order * bound * ‖point‖⁻¹ ^ order
  have summableDecay := (ZLattice.summable_norm_pow_inv lattice order (Nat.lt_succ_self _)).mul_left
    (distortion ^ order * bound)
  refine ⟨majorant, (hasSum_ite_eq (0 : lattice) zeroBound).summable.add summableDecay, ?_, ?_⟩
  · intro point
    dsimp [majorant]
    positivity
  · intro function membership transform distortionBound point
    by_cases zeroPoint : point = 0
    · subst point
      simp only [majorant, ite_true, ZeroMemClass.coe_zero, map_zero]
      exact (atZero function membership).trans (le_add_of_nonneg_right (by positivity))
    · have normPositive : 0 < ‖point.val‖ := norm_pos_iff.mpr (fun zero => zeroPoint (Subtype.ext zero))
      have powerBound : ‖point.val‖ ^ order ≤ distortion ^ order * ‖transform point.val‖ ^ order := by
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (distortionBound point.val) order
      have weightedBound : ‖point.val‖ ^ order * ‖function (transform point.val)‖ ≤ distortion ^ order * bound := by
        calc
          _ ≤ (distortion ^ order * ‖transform point.val‖ ^ order) * ‖function (transform point.val)‖ :=
            mul_le_mul_of_nonneg_right powerBound (norm_nonneg _)
          _ = distortion ^ order * (‖transform point.val‖ ^ order * ‖function (transform point.val)‖) := mul_assoc _ _ _
          _ ≤ distortion ^ order * bound := mul_le_mul_of_nonneg_left (decay function membership _) (pow_nonneg distortionNonnegative _)
      simp only [majorant, ite_eq_right zeroPoint, zero_add]
      change ‖function (transform point.val)‖ ≤ distortion ^ order * bound * ‖point.val‖⁻¹ ^ order
      rw [inv_pow, ← div_eq_mul_inv]
      exact (le_div_iff₀ (pow_pos normPositive order)).mpr (by simpa only [mul_comm] using weightedBound)

theorem rational (compact : Set (Rectangular FiniteAdeles)) (compactIs : IsCompact compact)
    (tests : Set (SchwartzMap RealSpace Target)) (testsBounded : UniformSchwartzBounds.Bounded tests) (distortion : ℝ) (distortionNonnegative : 0 ≤ distortion) :
    ∃ majorant : Rectangular ℚ → ℝ, Summable majorant ∧ (∀ matrix, 0 ≤ majorant matrix) ∧
      ∀ function ∈ tests, ∀ transform : RealSpace →L[ℝ] RealSpace, (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) →
        ∀ matrix, finiteMatrix matrix ∈ compact → ‖function (transform (realVector matrix))‖ ≤ majorant matrix := by
  classical
  obtain ⟨denominator, nonzero, integral⟩ := compact_integer_multiples compact compactIs
  have denominatorPositive : 0 < (denominator : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero nonzero
  let intoLattice : {matrix : Rectangular ℚ // finiteMatrix matrix ∈ compact} → integerLattice :=
    fun matrix => ⟨(denominator : ℝ) • realVector matrix.val, scaled_mem_lattice denominator matrix.val (integral _ matrix.property)⟩
  have injective : Function.Injective intoLattice := by
    intro first second equality
    apply Subtype.ext
    apply realVector_injective
    exact (smul_right_injective _ denominatorPositive.ne') (congrArg Subtype.val equality)
  let scale : RealSpace ≃L[ℝ] RealSpace := ContinuousLinearEquiv.smulLeft
    (Units.mk0 (denominator : ℝ) denominatorPositive.ne')⁻¹
  have scaleEquality : ∀ matrix, scale (intoLattice matrix).val = realVector matrix.val := by
    intro matrix
    exact inv_smul_smul₀ denominatorPositive.ne' _
  obtain ⟨latticeMajorant, summableLattice, nonnegativeLattice, boundedLattice⟩ :=
    lattice integerLattice tests testsBounded ((denominator : ℝ) * distortion)
      (mul_nonneg denominatorPositive.le distortionNonnegative)
  let majorant : Rectangular ℚ → ℝ := fun matrix =>
    if membership : finiteMatrix matrix ∈ compact then latticeMajorant (intoLattice ⟨matrix, membership⟩) else 0
  have restricted : Summable (fun matrix : {matrix : Rectangular ℚ // finiteMatrix matrix ∈ compact} => majorant matrix.val) := by
    have result : Summable (fun matrix : {matrix : Rectangular ℚ // finiteMatrix matrix ∈ compact} =>
        latticeMajorant (intoLattice matrix)) := summableLattice.comp_injective injective
    apply result.congr
    intro matrix
    simp only [majorant, dite_eq_left matrix.property]
  have indicated : Summable ({matrix | finiteMatrix matrix ∈ compact}.indicator majorant) :=
    summable_subtype_iff_indicator.mp restricted
  have summableMajorant : Summable majorant := by
    apply indicated.congr
    intro matrix
    by_cases membership : matrix ∈ {matrix | finiteMatrix matrix ∈ compact}
    · exact Set.indicator_of_mem membership _
    · rw [Set.indicator_of_notMem membership]
      change finiteMatrix matrix ∉ compact at membership
      simp only [majorant, dite_eq_right membership]
  refine ⟨majorant, summableMajorant, ?_, ?_⟩
  · intro matrix
    dsimp [majorant]
    split_ifs
    · exact nonnegativeLattice _
    · exact le_rfl
  · intro function testMembership transform distortionBound matrix membership
    have scaledBound : ∀ vector : RealSpace,
        ‖vector‖ ≤ ((denominator : ℝ) * distortion) * ‖(transform.comp scale.toContinuousLinearMap) vector‖ := by
      intro vector
      have scaling : (denominator : ℝ) • scale vector = vector := smul_inv_smul₀ denominatorPositive.ne' _
      calc
        ‖vector‖ = (denominator : ℝ) * ‖scale vector‖ := by
          conv_lhs => rw [← scaling]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos denominatorPositive]
        _ ≤ (denominator : ℝ) * (distortion * ‖transform (scale vector)‖) :=
          mul_le_mul_of_nonneg_left (distortionBound (scale vector)) denominatorPositive.le
        _ = _ := (mul_assoc _ _ _).symm
    have bound := boundedLattice function testMembership (transform.comp scale.toContinuousLinearMap) scaledBound (intoLattice ⟨matrix, membership⟩)
    change ‖function (transform (scale (intoLattice ⟨matrix, membership⟩).val))‖ ≤ _ at bound
    rw [scaleEquality] at bound
    simpa only [majorant, dite_eq_left membership] using bound

theorem adelic (tests : Set (SchwartzMap RealSpace Target)) (testsBounded : UniformSchwartzBounds.Bounded tests)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (parameters : Set Parameter) (compact : IsCompact parameters) :
    ∃ majorant : Rectangular ℚ → ℝ, Summable majorant ∧ (∀ matrix, 0 ≤ majorant matrix) ∧
      ∀ realTest ∈ tests, ∀ parameter ∈ parameters, ∀ matrix,
        ‖matrixTerm (tensorTest realTest finiteTest) parameter.1 parameter.2 matrix‖ ≤ majorant matrix := by
  obtain ⟨hull, hullCompact, hullMembership⟩ := exists_finite_hull finiteTest finiteSupport parameters compact
  obtain ⟨distortion, distortionNonnegative, distortionBound⟩ := exists_distortion_bound parameters compact
  obtain ⟨majorant, majorantSummable, majorantNonnegative, majorantBound⟩ :=
    rational hull hullCompact tests testsBounded distortion distortionNonnegative
  obtain ⟨bound, bounded⟩ := finiteSupport.exists_bound_of_continuous finiteContinuous
  refine ⟨fun matrix => max bound 0 * majorant matrix, majorantSummable.mul_left _,
    fun matrix => mul_nonneg (le_max_right _ _) (majorantNonnegative matrix), ?_⟩
  intro realTest testMembership parameter membership matrix
  rw [matrixTerm_factorization, norm_smul]
  by_cases finiteZero : finiteTest (finiteAction parameter (finiteMatrix matrix)) = 0
  · rw [finiteZero, norm_zero, zero_mul]
    exact mul_nonneg (le_max_right _ _) (majorantNonnegative matrix)
  · have realBound := majorantBound realTest testMembership (realAction parameter).toContinuousLinearMap (distortionBound parameter membership)
      matrix (hullMembership parameter membership (finiteMatrix matrix) finiteZero)
    exact mul_le_mul ((bounded _).trans (le_max_left _ _)) realBound (norm_nonneg _) (le_max_right _ _)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformThetaMajorants
