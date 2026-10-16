module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MaximalCompact

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.HeightProperties

theorem planeCornerUnit_one {ring : Type*} [CommRing ring] :
    planeCornerUnit (1 : planeParabolic ring) = 1 := by
  apply Units.ext
  rfl

theorem planeCornerUnit_mul {ring : Type*} [CommRing ring]
    (first second : planeParabolic ring) :
    planeCornerUnit (first * second) = planeCornerUnit first * planeCornerUnit second := by
  apply Units.ext
  change (first.val * second.val).val 2 2 = first.val.val 2 2 * second.val.val 2 2
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three,
    first.property.1, first.property.2, zero_mul, zero_add]

theorem log_adeleNorm_mul (first second : Adelesˣ) :
    Real.log (adeleNorm (first * second) : ℝ) =
      Real.log (adeleNorm first : ℝ) + Real.log (adeleNorm second : ℝ) := by
  have firstNonzero : (adeleNorm first : ℝ) ≠ 0 := ne_of_gt (adeleNorm_pos first)
  have secondNonzero : (adeleNorm second : ℝ) ≠ 0 := ne_of_gt (adeleNorm_pos second)
  rw [map_mul, NNReal.coe_mul, Real.log_mul firstNonzero secondNonzero]

theorem planeHeightLog_eq_det_corner (element : planeParabolic Adeles) :
    planeHeightLog element =
      Real.log (adeleNorm (GeneralLinearGroup.det element.val) : ℝ) / 3 -
        Real.log (adeleNorm (planeCornerUnit element) : ℝ) := by
  rw [planeHeightLog, det_planeParabolic, log_adeleNorm_mul]
  ring

theorem planeHeightLog_one : planeHeightLog (1 : planeParabolic Adeles) = 0 := by
  rw [planeHeightLog_eq_det_corner, planeCornerUnit_one]
  simp

theorem planeHeightLog_mul (first second : planeParabolic Adeles) :
    planeHeightLog (first * second) = planeHeightLog first + planeHeightLog second := by
  rw [planeHeightLog_eq_det_corner, planeHeightLog_eq_det_corner, planeHeightLog_eq_det_corner,
    planeCornerUnit_mul]
  change Real.log (adeleNorm (GeneralLinearGroup.det (first.val * second.val)) : ℝ) / 3 - _ = _
  rw [map_mul, log_adeleNorm_mul, log_adeleNorm_mul]
  ring

theorem planeHeightLog_inv (element : planeParabolic Adeles) :
    planeHeightLog element⁻¹ = -planeHeightLog element := by
  have equality := planeHeightLog_mul element element⁻¹
  rw [mul_inv_cancel, planeHeightLog_one] at equality
  linarith

theorem abs_real_corner_of_orthogonal (element : planeParabolic ℝ)
    (orthogonality : element.val.val.transpose * element.val.val = 1) :
    |(planeCornerUnit element).val| = 1 := by
  have rowsOrthogonal := (Matrix.mem_orthogonalGroup_iff _ _).mp
    ((Matrix.mem_orthogonalGroup_iff' _ _).mpr orthogonality)
  have cornerEntry := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix 2 2) rowsOrthogonal
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
    element.property.1, element.property.2, zero_mul, zero_add, Matrix.one_apply_eq] at cornerEntry
  have cornerSquare : (planeCornerUnit element).val ^ 2 = 1 := by
    change element.val.val 2 2 ^ 2 = 1
    nlinarith
  rcases sq_eq_one_iff.mp cornerSquare with equality | equality <;> simp [equality]

theorem adeleNorm_corner_of_compact (element : planeParabolic Adeles)
    (compactness : inMaximalCompact element.val) :
    (adeleNorm (planeCornerUnit element) : ℝ) = 1 := by
  let realElement : planeParabolic ℝ :=
    ⟨realGroup element.val, inPlane_map (RingHom.fst ℝ FiniteAdeles) element.val element.property⟩
  obtain ⟨integralMatrix, finiteEquality⟩ := compactness.2
  have integralParabolic : integralMatrix ∈ planeParabolic IntegralAdeles := by
    constructor
    · apply integralEmbedding_injective
      rw [map_zero]
      exact (congrArg (fun matrix : FiniteGL => matrix.val 2 0) finiteEquality).trans
        (congrArg Prod.snd element.property.1)
    · apply integralEmbedding_injective
      rw [map_zero]
      exact (congrArg (fun matrix : FiniteGL => matrix.val 2 1) finiteEquality).trans
        (congrArg Prod.snd element.property.2)
  let integralElement : planeParabolic IntegralAdeles := ⟨integralMatrix, integralParabolic⟩
  have factorization : planeCornerUnit element =
      realAdeleUnit (planeCornerUnit realElement) * integralAdeleUnit (planeCornerUnit integralElement) := by
    apply Units.ext
    apply Prod.ext
    · change (element.val.val 2 2).1 = (element.val.val 2 2).1 * 1
      rw [mul_one]
    · change (element.val.val 2 2).2 = 1 * integralEmbedding (integralMatrix.val 2 2)
      rw [one_mul]
      exact (congrArg (fun matrix : FiniteGL => matrix.val 2 2) finiteEquality).symm
  have integralNorm : adeleNorm (integralAdeleUnit (planeCornerUnit integralElement)) = 1 :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_integralUnit _
  rw [factorization, map_mul, NNReal.coe_mul, integralNorm, NNReal.coe_one, mul_one,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_real]
  exact abs_real_corner_of_orthogonal realElement compactness.1

theorem planeHeightLog_of_compact (element : planeParabolic Adeles)
    (compactness : inMaximalCompact element.val) : planeHeightLog element = 0 := by
  rw [planeHeightLog_eq_det_corner,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.adeleNorm_det_maximalCompact element.val compactness,
    adeleNorm_corner_of_compact element compactness, Real.log_one, zero_div, sub_self]

theorem height_of_factorization (matrix : AdelicGL) (element : planeParabolic Adeles)
    (compactElement : AdelicGL) (factorization : matrix = element.val * compactElement)
    (compactness : inMaximalCompact compactElement) : height matrix = planeHeightLog element := by
  let difference := (parabolicPart matrix)⁻¹ * element
  have parabolicEquality : element.val = matrix * compactElement⁻¹ := by
    rw [factorization, mul_assoc, mul_inv_cancel, mul_one]
  have differenceEquality : difference.val = compactPart matrix * compactElement⁻¹ := by
    change (parabolicPart matrix).val⁻¹ * element.val = _
    calc
      (parabolicPart matrix).val⁻¹ * element.val =
          (parabolicPart matrix).val⁻¹ * (matrix * compactElement⁻¹) := by rw [parabolicEquality]
      _ = (parabolicPart matrix).val⁻¹ *
          (((parabolicPart matrix).val * compactPart matrix) * compactElement⁻¹) :=
        congrArg (fun value => (parabolicPart matrix).val⁻¹ * (value * compactElement⁻¹))
          (parabolicPart_mul_compactPart matrix)
      _ = compactPart matrix * compactElement⁻¹ := by simp only [mul_assoc, inv_mul_cancel_left]
  have differenceCompact : inMaximalCompact difference.val := by
    rw [differenceEquality]
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.maximalCompact.mul_mem (compactPart_mem matrix)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.maximalCompact.inv_mem compactness)
  have zeroHeight := planeHeightLog_of_compact difference differenceCompact
  change planeHeightLog ((parabolicPart matrix)⁻¹ * element) = 0 at zeroHeight
  rw [planeHeightLog_mul, planeHeightLog_inv] at zeroHeight
  change planeHeightLog (parabolicPart matrix) = _
  linarith

theorem height_mul_compact (matrix : AdelicGL) (compactElement : AdelicGL)
    (compactness : inMaximalCompact compactElement) :
    height (matrix * compactElement) = height matrix := by
  apply height_of_factorization (matrix * compactElement) (parabolicPart matrix)
    (compactPart matrix * compactElement)
  · exact (congrArg (fun value => value * compactElement)
      (parabolicPart_mul_compactPart matrix)).trans (mul_assoc _ _ _)
  · exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.maximalCompact.mul_mem (compactPart_mem matrix) compactness

theorem height_plane_mul (element : planeParabolic Adeles) (matrix : AdelicGL) :
    height (element.val * matrix) = planeHeightLog element + height matrix := by
  change height (element.val * matrix) = planeHeightLog element + planeHeightLog (parabolicPart matrix)
  rw [← planeHeightLog_mul]
  apply height_of_factorization _ (element * parabolicPart matrix) (compactPart matrix)
  · exact (congrArg (fun value => element.val * value)
      (parabolicPart_mul_compactPart matrix)).trans (mul_assoc _ _ _).symm
  · exact compactPart_mem matrix

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.HeightProperties
