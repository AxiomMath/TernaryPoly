module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Schwartz.Lattice

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

abbrev Coordinate := Fin 3 × Fin 2
abbrev RealSpace := EuclideanSpace ℝ Coordinate

noncomputable def realVector (matrix : Rectangular ℚ) : RealSpace :=
  WithLp.toLp 2 (fun coordinate => (matrix coordinate.1 coordinate.2 : ℝ))

noncomputable def finiteMatrix (matrix : Rectangular ℚ) : Rectangular FiniteAdeles :=
  matrix.map (algebraMap ℚ FiniteAdeles)

noncomputable abbrev integerLattice : Submodule ℤ RealSpace :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun Coordinate ℝ).toBasis)

theorem integerVector_mem_lattice (vector : Coordinate → ℤ) :
    (WithLp.toLp 2 (fun coordinate => (vector coordinate : ℝ)) : RealSpace) ∈ integerLattice := by
  have expansion : (WithLp.toLp 2 (fun coordinate => (vector coordinate : ℝ)) : RealSpace) =
      ∑ coordinate : Coordinate, vector coordinate • (EuclideanSpace.basisFun Coordinate ℝ) coordinate := by
    ext coordinate
    simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
  rw [expansion]
  exact Submodule.sum_mem _ (fun coordinate _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨coordinate, rfl⟩))

theorem compact_integer_multiples (compact : Set (Rectangular FiniteAdeles)) (compactIs : IsCompact compact) :
    ∃ denominator : ℕ, denominator ≠ 0 ∧ ∀ matrix : Rectangular ℚ, finiteMatrix matrix ∈ compact →
      ∀ coordinate : Coordinate, ∃ integer : ℤ, (denominator : ℚ) * matrix coordinate.1 coordinate.2 = integer := by
  let coordinateSet : Set FiniteAdeles := ⋃ coordinate : Coordinate,
    (fun matrix : Rectangular FiniteAdeles => matrix coordinate.1 coordinate.2) '' compact
  have coordinateCompact : IsCompact coordinateSet :=
    isCompact_iUnion (fun coordinate => compactIs.image
      ((continuous_apply coordinate.2).comp (continuous_apply coordinate.1)))
  obtain ⟨denominator, nonzero, integral⟩ := CompactDenominators.exists_integer_multiples coordinateSet coordinateCompact
  refine ⟨denominator, nonzero, fun matrix membership coordinate => integral _ ?_⟩
  exact Set.mem_iUnion.mpr ⟨coordinate, finiteMatrix matrix, membership, rfl⟩

theorem scaled_mem_lattice (denominator : ℕ) (matrix : Rectangular ℚ)
    (integerMultiples : ∀ coordinate : Coordinate, ∃ integer : ℤ,
      (denominator : ℚ) * matrix coordinate.1 coordinate.2 = integer) :
    (denominator : ℝ) • realVector matrix ∈ integerLattice := by
  choose integers equality using integerMultiples
  have vectorEquality : (denominator : ℝ) • realVector matrix =
      WithLp.toLp 2 (fun coordinate => (integers coordinate : ℝ)) := by
    ext coordinate
    change (denominator : ℝ) * (matrix coordinate.1 coordinate.2 : ℝ) = (integers coordinate : ℝ)
    exact_mod_cast equality coordinate
  rw [vectorEquality]
  exact integerVector_mem_lattice integers

theorem realVector_injective : Function.Injective realVector := by
  intro first second equality
  ext row column
  exact Rat.cast_injective (congrArg (fun vector : RealSpace => vector (row, column)) equality)

theorem summable_norm_on_finite_compact (compact : Set (Rectangular FiniteAdeles)) (compactIs : IsCompact compact)
    (function : SchwartzMap RealSpace ℂ) :
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
    (SchwartzLattice.summable_norm_transform integerLattice scale function).comp_injective injective
  simpa only [scaleEquality] using result

theorem summable_norm_of_bound (compact : Set (Rectangular FiniteAdeles)) (compactIs : IsCompact compact)
    (function : SchwartzMap RealSpace ℂ) (kernel : Rectangular ℚ → ℂ) (bound : ℝ)
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

theorem summable_of_bound (compact : Set (Rectangular FiniteAdeles)) (compactIs : IsCompact compact)
    (function : SchwartzMap RealSpace ℂ) (kernel : Rectangular ℚ → ℂ) (bound : ℝ)
    (supported : ∀ matrix, finiteMatrix matrix ∉ compact → kernel matrix = 0)
    (bounded : ∀ matrix, finiteMatrix matrix ∈ compact → ‖kernel matrix‖ ≤ bound * ‖function (realVector matrix)‖) :
    Summable kernel :=
  (summable_norm_of_bound compact compactIs function kernel bound supported bounded).of_norm

theorem summable_norm_product (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) :
    Summable (fun matrix : Rectangular ℚ => ‖realTest (realVector matrix) * finiteTest (finiteMatrix matrix)‖) := by
  obtain ⟨bound, bounded⟩ := finiteSupport.exists_bound_of_continuous finiteContinuous
  apply summable_norm_of_bound (tsupport finiteTest) finiteSupport realTest _ bound
  · intro matrix outside
    have vanishing : finiteTest (finiteMatrix matrix) = 0 := by
      by_contra nonzero
      exact outside (subset_closure nonzero)
    rw [vanishing, mul_zero]
  · intro matrix _
    rw [norm_mul]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (bounded (finiteMatrix matrix)) (norm_nonneg (realTest (realVector matrix)))

theorem summable_product (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) :
    Summable (fun matrix : Rectangular ℚ => realTest (realVector matrix) * finiteTest (finiteMatrix matrix)) :=
  (summable_norm_product realTest finiteTest finiteContinuous finiteSupport).of_norm

theorem exists_uniform_majorant (compact : Set (Rectangular FiniteAdeles)) (compactIs : IsCompact compact)
    (function : SchwartzMap RealSpace ℂ) (distortion : ℝ) (distortionNonnegative : 0 ≤ distortion) :
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
    SchwartzLattice.exists_uniform_majorant integerLattice function ((denominator : ℝ) * distortion)
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

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
