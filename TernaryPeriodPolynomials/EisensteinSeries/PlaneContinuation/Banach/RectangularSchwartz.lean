module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.SchwartzLattice

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachRectangularSchwartz

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]

theorem summable_norm_on_finite_compact (compact : Set (Rectangular FiniteAdeles)) (compactIs : IsCompact compact)
    (function : SchwartzMap RealSpace Target) :
    Summable (fun matrix : {matrix : Rectangular ℚ // finiteMatrix matrix ∈ compact} => ‖function (realVector matrix.val)‖) := by
  obtain ⟨denominator, nonzero, integral⟩ := compact_integer_multiples compact compactIs
  have realNonzero : (denominator : ℝ) ≠ 0 := by exact_mod_cast nonzero
  let intoLattice : {matrix : Rectangular ℚ // finiteMatrix matrix ∈ compact} → integerLattice :=
    fun matrix => ⟨(denominator : ℝ) • realVector matrix.val, scaled_mem_lattice denominator matrix.val (integral _ matrix.property)⟩
  have injective : Function.Injective intoLattice := by
    intro first second equality
    apply Subtype.ext
    apply realVector_injective
    exact (smul_right_injective _ realNonzero) (congrArg Subtype.val equality)
  let scale : RealSpace ≃L[ℝ] RealSpace := ContinuousLinearEquiv.smulLeft (Units.mk0 (denominator : ℝ) realNonzero)⁻¹
  have scaleEquality : ∀ matrix, scale (intoLattice matrix).val = realVector matrix.val := by
    intro matrix
    change (denominator : ℝ)⁻¹ • ((denominator : ℝ) • realVector matrix.val) = realVector matrix.val
    exact inv_smul_smul₀ realNonzero _
  have result : Summable (fun matrix : {matrix : Rectangular ℚ // finiteMatrix matrix ∈ compact} =>
      ‖function (scale (intoLattice matrix).val)‖) :=
    (BanachSchwartzLattice.summable_norm_transform integerLattice scale function).comp_injective injective
  simpa only [scaleEquality] using result

theorem summable_norm_of_bound (compact : Set (Rectangular FiniteAdeles)) (compactIs : IsCompact compact)
    (function : SchwartzMap RealSpace Target) (kernel : Rectangular ℚ → Target) (bound : ℝ)
    (supported : ∀ matrix, finiteMatrix matrix ∉ compact → kernel matrix = 0)
    (bounded : ∀ matrix, finiteMatrix matrix ∈ compact → ‖kernel matrix‖ ≤ bound * ‖function (realVector matrix)‖) :
    Summable (fun matrix => ‖kernel matrix‖) := by
  have restricted : Summable (fun matrix : {matrix : Rectangular ℚ // finiteMatrix matrix ∈ compact} => ‖kernel matrix.val‖) :=
    ((summable_norm_on_finite_compact compact compactIs function).mul_left bound).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun matrix => bounded matrix.val matrix.property)
  have indicated : Summable ({matrix | finiteMatrix matrix ∈ compact}.indicator (fun matrix => ‖kernel matrix‖)) :=
    summable_subtype_iff_indicator.mp restricted
  apply indicated.congr
  intro matrix
  by_cases membership : finiteMatrix matrix ∈ compact
  · change matrix ∈ {matrix | finiteMatrix matrix ∈ compact} at membership
    exact Set.indicator_of_mem membership _
  · change matrix ∉ {matrix | finiteMatrix matrix ∈ compact} at membership
    rw [Set.indicator_of_notMem membership, supported matrix membership, norm_zero]

theorem summable_of_bound [CompleteSpace Target] (compact : Set (Rectangular FiniteAdeles)) (compactIs : IsCompact compact)
    (function : SchwartzMap RealSpace Target) (kernel : Rectangular ℚ → Target) (bound : ℝ)
    (supported : ∀ matrix, finiteMatrix matrix ∉ compact → kernel matrix = 0)
    (bounded : ∀ matrix, finiteMatrix matrix ∈ compact → ‖kernel matrix‖ ≤ bound * ‖function (realVector matrix)‖) :
    Summable kernel :=
  (summable_norm_of_bound compact compactIs function kernel bound supported bounded).of_norm

theorem exists_uniform_majorant (compact : Set (Rectangular FiniteAdeles)) (compactIs : IsCompact compact)
    (function : SchwartzMap RealSpace Target) (distortion : ℝ) (distortionNonnegative : 0 ≤ distortion) :
    ∃ majorant : Rectangular ℚ → ℝ, Summable majorant ∧ (∀ matrix, 0 ≤ majorant matrix) ∧
      ∀ transform : RealSpace →L[ℝ] RealSpace, (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) →
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
    BanachSchwartzLattice.exists_uniform_majorant integerLattice function ((denominator : ℝ) * distortion)
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
  · intro transform distortionBound matrix membership
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
    have bound := boundedLattice (transform.comp scale.toContinuousLinearMap) scaledBound (intoLattice ⟨matrix, membership⟩)
    change ‖function (transform (scale (intoLattice ⟨matrix, membership⟩).val))‖ ≤ _ at bound
    rw [scaleEquality] at bound
    simpa only [majorant, dite_eq_left membership] using bound

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachRectangularSchwartz
