module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Parabolic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition

theorem lastRow_ne_zero (realMatrix : RealGL3) :
    (fun column : Fin 3 => realMatrix.val 2 column) ≠ 0 := by
  intro zeroRow
  have rowEntry (column : Fin 3) : realMatrix.val 2 column = 0 := congrFun zeroRow column
  have identityEntry := congrArg
    (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix 2 2) realMatrix.mul_inv
  simp [Matrix.mul_apply, rowEntry] at identityEntry

theorem exists_orthogonal_columns (rowVector : EuclideanSpace ℝ (Fin 3))
    (nonzeroRow : rowVector ≠ 0) :
    ∃ orthogonalMatrix : Matrix (Fin 3) (Fin 3) ℝ,
      orthogonalMatrix.transpose * orthogonalMatrix = 1 ∧
      orthogonalMatrix * orthogonalMatrix.transpose = 1 ∧
      ∀ column : Fin 3,
        (∑ index : Fin 3, rowVector index * orthogonalMatrix index column) =
          if column = 2 then ‖rowVector‖ else 0 := by
  classical
  let normalizedRow : EuclideanSpace ℝ (Fin 3) := ‖rowVector‖⁻¹ • rowVector
  have normalizedNorm : ‖normalizedRow‖ = 1 := norm_smul_inv_norm nonzeroRow
  have singletonOrthonormal : Orthonormal ℝ
      (({2} : Set (Fin 3)).domRestrict (fun _ : Fin 3 => normalizedRow)) := by
    rw [orthonormal_iff_ite]
    intro first second
    have equalIndices : first = second := Subtype.ext
      ((Set.mem_singleton_iff.mp first.property).trans
        (Set.mem_singleton_iff.mp second.property).symm)
    simp [equalIndices, normalizedNorm]
  obtain ⟨orthonormalBasis, basisLast⟩ :=
    singletonOrthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have basisLastValue : orthonormalBasis 2 = normalizedRow := basisLast 2 (by simp)
  let standardBasis := EuclideanSpace.basisFun (Fin 3) ℝ
  let orthogonalMatrix := standardBasis.toBasis.toMatrix (fun index => orthonormalBasis index)
  have orthogonalMembership : orthogonalMatrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    standardBasis.toMatrix_orthonormalBasis_mem_orthogonal orthonormalBasis
  refine ⟨orthogonalMatrix, (Matrix.mem_orthogonalGroup_iff' _ _).mp orthogonalMembership,
    (Matrix.mem_orthogonalGroup_iff _ _).mp orthogonalMembership, fun column => ?_⟩
  have rowRecovery : rowVector = ‖rowVector‖ • orthonormalBasis 2 := by
    rw [basisLastValue]
    dsimp [normalizedRow]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr nonzeroRow), one_smul]
  have matrixEntry (index : Fin 3) : orthogonalMatrix index column =
      orthonormalBasis column index := by
    simp [orthogonalMatrix, standardBasis, Module.Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply]
  calc
    (∑ index : Fin 3, rowVector index * orthogonalMatrix index column) =
        inner ℝ rowVector (orthonormalBasis column) := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, matrixEntry, mul_comm]
    _ = ‖rowVector‖ * (if (2 : Fin 3) = column then 1 else 0) := by
      conv_lhs => rw [rowRecovery]
      rw [real_inner_smul_left, orthonormalBasis.inner_eq_ite]
    _ = if column = 2 then ‖rowVector‖ else 0 := by
      by_cases equalIndex : column = 2
      · simp only [equalIndex, ↓reduceIte, mul_one]
      · simp only [ite_eq_right equalIndex, ite_eq_right (Ne.symm equalIndex), mul_zero]

theorem exists_plane_orthogonal (realMatrix : RealGL3) :
    ∃ (parabolicElement : planeParabolic ℝ) (orthogonalElement : RealGL3),
      realMatrix = parabolicElement.val * orthogonalElement ∧
      orthogonalElement.val.transpose * orthogonalElement.val = 1 ∧
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeCornerUnit parabolicElement).val =
        ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
          EuclideanSpace ℝ (Fin 3))‖ := by
  let rowVector : EuclideanSpace ℝ (Fin 3) :=
    WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column)
  have nonzeroRow : rowVector ≠ 0 := by
    intro zeroRow
    apply lastRow_ne_zero realMatrix
    exact congrArg WithLp.ofLp zeroRow
  obtain ⟨orthogonalMatrix, transposeIdentity, identityTranspose, rowProduct⟩ :=
    exists_orthogonal_columns rowVector nonzeroRow
  let columnElement : RealGL3 :=
    ⟨orthogonalMatrix, orthogonalMatrix.transpose, identityTranspose, transposeIdentity⟩
  have parabolicMembership : InPlaneParabolic (realMatrix * columnElement) := by
    constructor
    · simpa [Units.val_mul, Matrix.mul_apply, rowVector, columnElement] using rowProduct 0
    · simpa [Units.val_mul, Matrix.mul_apply, rowVector, columnElement] using rowProduct 1
  let parabolicElement : planeParabolic ℝ := ⟨realMatrix * columnElement, parabolicMembership⟩
  refine ⟨parabolicElement, columnElement⁻¹, ?_, ?_, ?_⟩
  · exact (mul_inv_cancel_right realMatrix columnElement).symm
  · change orthogonalMatrix.transpose.transpose * orthogonalMatrix.transpose = 1
    simpa only [Matrix.transpose_transpose] using identityTranspose
  · change (realMatrix.val * orthogonalMatrix) 2 2 = ‖rowVector‖
    simpa [Matrix.mul_apply, rowVector] using rowProduct 2

theorem abs_det_orthogonal (orthogonalElement : RealGL3)
    (orthogonality : orthogonalElement.val.transpose * orthogonalElement.val = 1) :
    |orthogonalElement.val.det| = 1 := by
  have determinantIdentity := congrArg Matrix.det orthogonality
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at determinantIdentity
  have absoluteIdentity := congrArg abs determinantIdentity
  rw [abs_mul, abs_one] at absoluteIdentity
  nlinarith [abs_nonneg orthogonalElement.val.det]

theorem real_heightLog_formula (realMatrix : RealGL3)
    (parabolicElement : planeParabolic ℝ) (orthogonalElement : RealGL3)
    (factorization : realMatrix = parabolicElement.val * orthogonalElement)
    (orthogonality : orthogonalElement.val.transpose * orthogonalElement.val = 1)
    (cornerValue : (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeCornerUnit parabolicElement).val =
      ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
        EuclideanSpace ℝ (Fin 3))‖) :
    (Real.log |(TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeBinaryBlock parabolicElement).val.det| -
      2 * Real.log |(TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeCornerUnit parabolicElement).val|) / 3 =
      Real.log |realMatrix.val.det| / 3 -
        Real.log ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
          EuclideanSpace ℝ (Fin 3))‖ := by
  have determinantFactorization := congrArg
    (fun matrix : RealGL3 => (Matrix.GeneralLinearGroup.det matrix).val) factorization
  rw [map_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.det_planeParabolic] at determinantFactorization
  change realMatrix.val.det =
    ((TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeBinaryBlock parabolicElement).val.det *
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeCornerUnit parabolicElement).val) *
        orthogonalElement.val.det at determinantFactorization
  have absoluteFactorization := congrArg abs determinantFactorization
  rw [abs_mul, abs_mul, abs_det_orthogonal orthogonalElement orthogonality,
    mul_one] at absoluteFactorization
  have binaryDetNonzero := Matrix.GeneralLinearGroup.det_ne_zero
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeBinaryBlock parabolicElement)
  have cornerNonzero := (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeCornerUnit parabolicElement).ne_zero
  have logarithmFactorization := congrArg Real.log absoluteFactorization
  rw [Real.log_mul (abs_ne_zero.mpr binaryDetNonzero)
    (abs_ne_zero.mpr cornerNonzero)] at logarithmFactorization
  rw [logarithmFactorization]
  rw [cornerValue, abs_of_nonneg (norm_nonneg _)]
  ring

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition
