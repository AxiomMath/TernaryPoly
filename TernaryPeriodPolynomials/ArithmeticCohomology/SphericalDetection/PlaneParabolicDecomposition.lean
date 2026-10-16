module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.ParabolicCompact
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.ParabolicCompact

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- A plane-parabolic matrix has the literal radical, scalar, and binary Levi factors. -/
theorem planeParabolic_exists_decomposition {ring : Type*} [CommRing ring]
    (matrix : planeParabolic ring) :
    ∃ (first second : ring) (scalar : ringˣ) (block : GeneralLinearGroup (Fin 2) ring),
      matrix.val = planeUnipotent first second * (planeLevi 1 scalar * planeLevi block 1) := by
  have forward := matrix.property
  have backward := (matrix⁻¹).property
  change matrix.val⁻¹.val 2 0 = 0 ∧ matrix.val⁻¹.val 2 1 = 0 at backward
  have backward_matrix : matrix.val.val⁻¹ 2 0 = 0 ∧ matrix.val.val⁻¹ 2 1 = 0 := by
    simpa only [GeneralLinearGroup.coe_inv] using backward
  have scalar_right : matrix.val.val 2 2 * matrix.val⁻¹.val 2 2 = 1 := by
    have equality := congrArg (fun value => value 2 2) matrix.val.mul_inv
    simpa only [Matrix.mul_apply, Fin.sum_univ_three, forward.1, forward.2, zero_mul,
      zero_add, Matrix.one_apply_eq] using equality
  have scalar_left : matrix.val⁻¹.val 2 2 * matrix.val.val 2 2 = 1 := by
    rw [mul_comm, scalar_right]
  have scalar_left_matrix : matrix.val.val⁻¹ 2 2 * matrix.val.val 2 2 = 1 := by
    simpa only [GeneralLinearGroup.coe_inv] using scalar_left
  let scalar : ringˣ := ⟨matrix.val.val 2 2, matrix.val⁻¹.val 2 2, scalar_right, scalar_left⟩
  let block : GeneralLinearGroup (Fin 2) ring :=
    { val := fun row column => matrix.val.val row.castSucc column.castSucc
      inv := fun row column => matrix.val⁻¹.val row.castSucc column.castSucc
      val_inv := by
        funext row column
        change (∑ index : Fin 2, matrix.val.val row.castSucc index.castSucc *
          matrix.val⁻¹.val index.castSucc column.castSucc) = (1 : Matrix (Fin 2) (Fin 2) ring) row column
        have equality := congrArg (fun value => value row.castSucc column.castSucc) matrix.val.mul_inv
        fin_cases row <;> fin_cases column <;>
          simpa [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
            backward_matrix.1, backward_matrix.2] using equality
      inv_val := by
        funext row column
        change (∑ index : Fin 2, matrix.val⁻¹.val row.castSucc index.castSucc *
          matrix.val.val index.castSucc column.castSucc) = (1 : Matrix (Fin 2) (Fin 2) ring) row column
        have equality := congrArg (fun value => value row.castSucc column.castSucc) matrix.val.inv_mul
        fin_cases row <;> fin_cases column <;>
          simpa [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, forward.1, forward.2] using equality }
  refine ⟨matrix.val.val 0 2 * scalar.inv, matrix.val.val 1 2 * scalar.inv, scalar, block, ?_⟩
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeUnipotent, planeLevi, planeBlock, scalar, block,
      Matrix.mul_apply, Fin.sum_univ_three,
      forward.1, forward.2, mul_assoc, scalar_left_matrix]

theorem realGroup_combineGL (real : RealGL3) (finite : FiniteGL) :
    realGroup (combineGL real finite) = real := by
  apply Units.ext
  rfl

theorem finiteGroup_combineGL (real : RealGL3) (finite : FiniteGL) :
    finiteGroup (combineGL real finite) = finite := by
  apply Units.ext
  rfl

/-- The full adelic plane Iwasawa decomposition uses exactly the statement's maximal compact. -/
theorem adelicGL_parabolic_compact_factorization (matrix : AdelicGL) :
    ∃ (parabolic : planeParabolic Adeles) (compact : AdelicGL),
      inMaximalCompact compact ∧ matrix = parabolic.val * compact := by
  obtain ⟨real_parabolic, real_compact, real_orthogonal, real_factorization⟩ :=
    realGL_parabolic_compact_factorization (realGroup matrix)
  obtain ⟨finite_parabolic, finite_compact, finite_factorization⟩ :=
    finiteGL_parabolic_compact_factorization (finiteGroup matrix)
  let parabolic := combineGL real_parabolic.val finite_parabolic.val
  have parabolic_member : parabolic ∈ planeParabolic Adeles := by
    constructor
    · exact Prod.ext real_parabolic.property.1 finite_parabolic.property.1
    · exact Prod.ext real_parabolic.property.2 finite_parabolic.property.2
  let compact := combineGL real_compact (GeneralLinearGroup.map integralEmbedding finite_compact)
  have compact_member : inMaximalCompact compact := by
    constructor
    · rw [show realGroup compact = real_compact from realGroup_combineGL _ _]
      exact real_orthogonal
    · exact ⟨finite_compact, (finiteGroup_combineGL _ _).symm⟩
  refine ⟨⟨parabolic, parabolic_member⟩, compact, compact_member, ?_⟩
  apply adelicGL_ext
  · rw [map_mul, realGroup_combineGL, realGroup_combineGL]
    exact real_factorization
  · rw [map_mul, finiteGroup_combineGL, finiteGroup_combineGL]
    exact finite_factorization

theorem adelicGL_exists_induction_coordinates (matrix : AdelicGL) :
    ∃ (first second : Adeles) (scalar : Adelesˣ) (block : BinaryAdelicGL) (compact : AdelicGL),
      inMaximalCompact compact ∧
      matrix = planeUnipotent first second * (planeLevi 1 scalar * (planeLevi block 1 * compact)) := by
  obtain ⟨parabolic, compact, compact_member, factorization⟩ := adelicGL_parabolic_compact_factorization matrix
  obtain ⟨first, second, scalar, block, parabolic_factors⟩ := planeParabolic_exists_decomposition parabolic
  exact ⟨first, second, scalar, block, compact, compact_member,
    factorization.trans (by rw [parabolic_factors, mul_assoc, mul_assoc])⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
