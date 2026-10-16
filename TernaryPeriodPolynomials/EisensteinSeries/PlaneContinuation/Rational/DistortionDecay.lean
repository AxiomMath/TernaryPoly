module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Schwartz.DistortionDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalDistortionDecay

def tailTerm (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (transform : RealSpace →L[ℝ] RealSpace) (scale : ℝ) (matrix : Rectangular ℚ) : ℂ :=
  if matrix = 0 then 0 else realTest (scale • transform (realVector matrix)) * finiteTest (finiteMatrix matrix)

theorem rapid_tail (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (transform : RealSpace →L[ℝ] RealSpace) (distortion : ℝ), 0 ≤ distortion →
        (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) → ∀ scale : ℝ, 1 ≤ scale →
          Summable (fun matrix => ‖tailTerm realTest finiteTest transform scale matrix‖) ∧
          scale ^ power * (∑' matrix, ‖tailTerm realTest finiteTest transform scale matrix‖) ≤
            constant * distortion ^ (power + Module.finrank ℤ integerLattice + 1) := by
  obtain ⟨denominator, nonzero, integral⟩ := compact_integer_multiples (tsupport finiteTest) finiteSupport
  have realNonzero : (denominator : ℝ) ≠ 0 := by exact_mod_cast nonzero
  let Index := {matrix : Rectangular ℚ // matrix ≠ 0 ∧ finiteMatrix matrix ∈ tsupport finiteTest}
  let intoLattice : Index → integerLattice := fun matrix =>
    ⟨(denominator : ℝ) • realVector matrix.val, scaled_mem_lattice denominator matrix.val (integral _ matrix.property.2)⟩
  have injective : Function.Injective intoLattice := by
    intro first second equality
    apply Subtype.ext
    apply realVector_injective
    exact (smul_right_injective _ realNonzero) (congrArg Subtype.val equality)
  have intoNonzero : ∀ matrix : Index, intoLattice matrix ≠ 0 := by
    intro matrix equality
    have vectorZero : realVector matrix.val = 0 := by
      have scaledZero := congrArg Subtype.val equality
      change (denominator : ℝ) • realVector matrix.val = 0 at scaledZero
      exact (smul_eq_zero.mp scaledZero).resolve_left realNonzero
    apply matrix.property.1
    apply realVector_injective
    rw [vectorZero]
    ext coordinate
    simp [realVector]
  let inverseScale : RealSpace ≃L[ℝ] RealSpace :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (denominator : ℝ) realNonzero)⁻¹
  let adapted : SchwartzMap RealSpace ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ inverseScale realTest
  have adaptedEquality (transform : RealSpace →L[ℝ] RealSpace) (scale : ℝ) (matrix : Index) :
      adapted (scale • transform (intoLattice matrix).val) = realTest (scale • transform (realVector matrix.val)) := by
    change realTest ((denominator : ℝ)⁻¹ • (scale • transform ((denominator : ℝ) • realVector matrix.val))) = _
    rw [transform.map_smul (denominator : ℝ), smul_comm (denominator : ℝ)⁻¹ scale, inv_smul_smul₀ realNonzero]
  obtain ⟨bound, bounded⟩ := finiteSupport.exists_bound_of_continuous finiteContinuous
  obtain ⟨constant, nonnegative, boundAtScale⟩ := SchwartzDistortionDecay.weighted_sum_bound integerLattice adapted power
    intoLattice injective intoNonzero (fun matrix => finiteTest (finiteMatrix matrix.val)) bound
    (fun matrix => bounded (finiteMatrix matrix.val))
  refine ⟨constant, nonnegative, fun transform distortion distortionNonnegative distortionBound scale scaleLower => ?_⟩
  obtain ⟨restrictedSummable, restrictedBound⟩ := boundAtScale transform distortion distortionNonnegative distortionBound scale scaleLower
  have restrictedEquality (matrix : Index) :
      adapted (scale • transform (intoLattice matrix).val) * finiteTest (finiteMatrix matrix.val) =
        tailTerm realTest finiteTest transform scale matrix.val := by
    rw [adaptedEquality, tailTerm, ite_eq_right matrix.property.1]
  have supported : Function.support (tailTerm realTest finiteTest transform scale) ⊆ Set.range (Subtype.val : Index → Rectangular ℚ) := by
    intro matrix nonvanishing
    have matrixNonzero : matrix ≠ 0 := by
      intro equality
      exact nonvanishing (by simp only [tailTerm, equality, ite_true])
    have finiteNonzero : finiteTest (finiteMatrix matrix) ≠ 0 := by
      intro equality
      exact nonvanishing (by rw [tailTerm, ite_eq_right matrixNonzero, equality, mul_zero])
    exact ⟨⟨matrix, matrixNonzero, subset_closure finiteNonzero⟩, rfl⟩
  have outside (matrix : Rectangular ℚ) (notIn : matrix ∉ Set.range (Subtype.val : Index → Rectangular ℚ)) :
      tailTerm realTest finiteTest transform scale matrix = 0 := by
    by_contra nonzero
    exact notIn (supported nonzero)
  have restrictedNorm : Summable (fun matrix : Index => ‖tailTerm realTest finiteTest transform scale matrix.val‖) := by
    simpa only [restrictedEquality] using restrictedSummable
  have fullNorm : Summable (fun matrix => ‖tailTerm realTest finiteTest transform scale matrix‖) := by
    apply (Subtype.val_injective.hasSum_iff (f := fun matrix => ‖tailTerm realTest finiteTest transform scale matrix‖)
      (fun matrix notIn => by rw [outside matrix notIn, norm_zero])).mp restrictedNorm.hasSum |>.summable
  refine ⟨fullNorm, ?_⟩
  have normSupported : Function.support (fun matrix => ‖tailTerm realTest finiteTest transform scale matrix‖) ⊆
      Set.range (Subtype.val : Index → Rectangular ℚ) := by
    intro matrix membership
    exact supported (fun zero => membership (by dsimp only; rw [zero, norm_zero]))
  rw [← Subtype.val_injective.tsum_eq normSupported]
  simpa only [restrictedEquality] using restrictedBound

theorem sum_eq_zero_add_tail (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (transform : RealSpace →L[ℝ] RealSpace) (scale : ℝ)
    (summableTail : Summable (tailTerm realTest finiteTest transform scale)) :
    (∑' matrix : Rectangular ℚ, realTest (scale • transform (realVector matrix)) * finiteTest (finiteMatrix matrix)) =
      realTest 0 * finiteTest 0 + ∑' matrix, tailTerm realTest finiteTest transform scale matrix := by
  have pointwise : (fun matrix : Rectangular ℚ => realTest (scale • transform (realVector matrix)) * finiteTest (finiteMatrix matrix)) =
      fun matrix => (if matrix = 0 then realTest 0 * finiteTest 0 else 0) + tailTerm realTest finiteTest transform scale matrix := by
    funext matrix
    by_cases zero : matrix = 0
    · subst matrix
      have realZero : realVector (0 : Rectangular ℚ) = 0 := by ext coordinate; simp [realVector]
      have finiteZero : finiteMatrix (0 : Rectangular ℚ) = 0 := by ext row column; simp [finiteMatrix]
      simp only [realZero, finiteZero, map_zero, smul_zero, tailTerm, ite_true, add_zero]
    · simp only [tailTerm, ite_eq_right zero, zero_add]
  rw [pointwise, Summable.tsum_add (hasSum_ite_eq (0 : Rectangular ℚ) (realTest 0 * finiteTest 0)).summable summableTail,
    (hasSum_ite_eq (0 : Rectangular ℚ) (realTest 0 * finiteTest 0)).tsum_eq]

theorem rapid_remainder (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (transform : RealSpace →L[ℝ] RealSpace) (distortion : ℝ), 0 ≤ distortion →
        (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) → ∀ scale : ℝ, 1 ≤ scale →
          scale ^ power * ‖(∑' matrix : Rectangular ℚ,
            realTest (scale • transform (realVector matrix)) * finiteTest (finiteMatrix matrix)) - realTest 0 * finiteTest 0‖ ≤
              constant * distortion ^ (power + Module.finrank ℤ integerLattice + 1) := by
  obtain ⟨constant, nonnegative, bounded⟩ := rapid_tail realTest finiteTest finiteContinuous finiteSupport power
  refine ⟨constant, nonnegative, fun transform distortion distortionNonnegative distortionBound scale scaleLower => ?_⟩
  obtain ⟨summable, bound⟩ := bounded transform distortion distortionNonnegative distortionBound scale scaleLower
  rw [sum_eq_zero_add_tail realTest finiteTest transform scale summable.of_norm, add_sub_cancel_left]
  exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm summable)
    (pow_nonneg (zero_le_one.trans scaleLower) _)).trans bound

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalDistortionDecay
