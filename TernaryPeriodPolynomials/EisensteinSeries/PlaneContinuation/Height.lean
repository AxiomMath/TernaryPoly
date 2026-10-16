module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Norm
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.Decomposition

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height

theorem inMaximalCompact_atInfinity (realMatrix : RealGL3) :
    inMaximalCompact (atInfinity realMatrix) ↔
      realMatrix.val.transpose * realMatrix.val = 1 := by
  constructor
  · exact fun membership => membership.1
  · intro orthogonality
    refine ⟨orthogonality, 1, ?_⟩
    exact map_one (Matrix.GeneralLinearGroup.map integralEmbedding)

theorem adeleNorm_det_maximalCompact (matrix : AdelicGL)
    (compactMembership : inMaximalCompact matrix) :
    (adeleNorm (Matrix.GeneralLinearGroup.det matrix) : ℝ) = 1 := by
  obtain ⟨integralMatrix, finiteEquality⟩ := compactMembership.2
  conv_lhs => rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adelicGL_eq_mul matrix]
  rw [map_mul, map_mul, NNReal.coe_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_atInfinity,
    ← finiteEquality, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_integral, NNReal.coe_one, mul_one]
  exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.abs_det_orthogonal (realGroup matrix) compactMembership.1

theorem atInfinity_mul {matrixSize : ℕ}
    (first second : Matrix.GeneralLinearGroup (Fin matrixSize) ℝ) :
    atInfinity (first * second) = atInfinity first * atInfinity second := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · simp only [Units.val_mul, atInfinity, combineGL, pairMatrix, Matrix.mul_apply,
      Prod.fst_sum, Prod.fst_mul]
  · simp only [Units.val_mul, atInfinity, combineGL, pairMatrix, Matrix.mul_apply,
      Prod.snd_sum, Prod.snd_mul]
    exact (congrArg (fun matrix : Matrix (Fin matrixSize) (Fin matrixSize) FiniteAdeles =>
      matrix row column) (one_mul (1 : Matrix (Fin matrixSize) (Fin matrixSize)
        FiniteAdeles))).symm

noncomputable def planeParabolicAtInfinity (parabolicElement : planeParabolic ℝ) :
    planeParabolic Adeles :=
  ⟨atInfinity parabolicElement.val, by
    constructor
    · change (parabolicElement.val.val 2 0,
        (1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) 2 0) = 0
      simp [parabolicElement.property.1]
    · change (parabolicElement.val.val 2 1,
        (1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) 2 1) = 0
      simp [parabolicElement.property.2]⟩

theorem corner_atInfinity (parabolicElement : planeParabolic ℝ) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeCornerUnit (planeParabolicAtInfinity parabolicElement) =
      realAdeleUnit (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeCornerUnit parabolicElement) := by
  apply Units.ext
  rfl

theorem binaryBlock_atInfinity (parabolicElement : planeParabolic ℝ) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeBinaryBlock (planeParabolicAtInfinity parabolicElement) =
      atInfinity (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeBinaryBlock parabolicElement) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · rfl
  · change (1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) row.castSucc column.castSucc =
      (1 : Matrix (Fin 2) (Fin 2) FiniteAdeles) row column
    simp only [Matrix.one_apply, Fin.castSucc_inj]

theorem planeHeightLog_atInfinity (parabolicElement : planeParabolic ℝ) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeHeightLog (planeParabolicAtInfinity parabolicElement) =
      (Real.log |(TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeBinaryBlock parabolicElement).val.det| -
        2 * Real.log |(TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeCornerUnit parabolicElement).val|) / 3 := by
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeHeightLog, corner_atInfinity, binaryBlock_atInfinity,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_real, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_atInfinity]

theorem flatSection_real_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3)
    (parabolicElement : planeParabolic ℝ) (orthogonalElement : RealGL3)
    (factorization : realMatrix = parabolicElement.val * orthogonalElement)
    (orthogonality : orthogonalElement.val.transpose * orthogonalElement.val = 1)
    (cornerValue : (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeCornerUnit parabolicElement).val =
      ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
        EuclideanSpace ℝ (Fin 3))‖)
    (compactness : inMaximalCompact (atInfinity orthogonalElement)) (parameter : ℂ) :
    sectionFamily parameter (atInfinity realMatrix) =
      Complex.exp ((parameter - cohomologicalPoint) *
        ((Real.log |realMatrix.val.det| / 3 -
          Real.log ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
            EuclideanSpace ℝ (Fin 3))‖ : ℝ) : ℂ)) *
        sectionFamily cohomologicalPoint (atInfinity realMatrix) := by
  have sectionFormula := TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.flatSection_planeParabolic_exp flatSection
    (planeParabolicAtInfinity parabolicElement) (atInfinity orthogonalElement) compactness
    parameter
  have embeddedFactorization : atInfinity realMatrix =
      (planeParabolicAtInfinity parabolicElement).val * atInfinity orthogonalElement := by
    rw [factorization, atInfinity_mul]
    rfl
  rw [← embeddedFactorization, planeHeightLog_atInfinity,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.real_heightLog_formula realMatrix parabolicElement
      orthogonalElement factorization orthogonality cornerValue] at sectionFormula
  exact sectionFormula

theorem flatSection_atInfinity_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3)
    (parameter : ℂ) :
    sectionFamily parameter (atInfinity realMatrix) =
      Complex.exp ((parameter - cohomologicalPoint) *
        ((Real.log |realMatrix.val.det| / 3 -
          Real.log ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
            EuclideanSpace ℝ (Fin 3))‖ : ℝ) : ℂ)) *
        sectionFamily cohomologicalPoint (atInfinity realMatrix) := by
  obtain ⟨parabolicElement, orthogonalElement, factorization, orthogonality, cornerValue⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.exists_plane_orthogonal realMatrix
  exact flatSection_real_parameter flatSection realMatrix parabolicElement orthogonalElement
    factorization orthogonality cornerValue
    ((inMaximalCompact_atInfinity orthogonalElement).mpr orthogonality) parameter

theorem norm_flatSection_atInfinity {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3)
    (parameter : ℂ) :
    ‖sectionFamily parameter (atInfinity realMatrix)‖ =
      Real.exp ((parameter.re - cohomologicalPoint.re) *
        (Real.log |realMatrix.val.det| / 3 -
          Real.log ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
            EuclideanSpace ℝ (Fin 3))‖)) *
        ‖sectionFamily cohomologicalPoint (atInfinity realMatrix)‖ := by
  rw [flatSection_atInfinity_parameter flatSection realMatrix parameter,
    norm_mul, Complex.norm_exp]
  simp

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height
