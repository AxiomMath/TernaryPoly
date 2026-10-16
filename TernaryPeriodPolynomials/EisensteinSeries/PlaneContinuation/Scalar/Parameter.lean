module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.Bounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarParameter

noncomputable def flagRadius (flag : Flags .plane) : ℝ :=
  ‖(WithLp.toLp 2 (fun column =>
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ)) :
      EuclideanSpace ℝ (Fin 3))‖

theorem one_le_flagRadius (flag : Flags .plane) : 1 ≤ flagRadius flag := by
  have nonzero := TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow_ne_zero flag
  obtain ⟨column, nonzeroColumn⟩ : ∃ column,
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column ≠ 0 := by
    by_contra h
    apply nonzero
    funext column
    simpa using not_exists.mp h column
  have integerBound : (1 : ℤ) ≤ |TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column| :=
    Int.one_le_abs nonzeroColumn
  have realBound : (1 : ℝ) ≤
      |(TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ)| := by
    exact_mod_cast integerBound
  exact realBound.trans (PiLp.norm_apply_le
    (WithLp.toLp 2 (fun column =>
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ))) column)

theorem flagRadius_pos (flag : Flags .plane) : 0 < flagRadius flag :=
  lt_of_lt_of_le zero_lt_one (one_le_flagRadius flag)

theorem flatSection_real_integral_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3)
    (integralMatrix : IntegralGL3) (parameter : ℂ) :
    sectionFamily parameter (atInfinity realMatrix * atFinite (integralFinite integralMatrix)) =
      Complex.exp ((parameter - cohomologicalPoint) *
        ((Real.log |realMatrix.val.det| / 3 -
          Real.log ‖(WithLp.toLp 2 (fun column => realMatrix.val 2 column) :
            EuclideanSpace ℝ (Fin 3))‖ : ℝ) : ℂ)) *
        sectionFamily cohomologicalPoint
          (atInfinity realMatrix * atFinite (integralFinite integralMatrix)) := by
  obtain ⟨parabolicElement, orthogonalElement, factorization, orthogonality, cornerValue⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.exists_plane_orthogonal realMatrix
  have formula := flatSection_planeParabolic_exp flatSection
    (planeParabolicAtInfinity parabolicElement)
    (atInfinity orthogonalElement * atFinite (integralFinite integralMatrix))
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.orthogonal_integral_compact orthogonalElement orthogonality
      integralMatrix) parameter
  have embeddedFactorization : atInfinity realMatrix =
      (planeParabolicAtInfinity parabolicElement).val * atInfinity orthogonalElement := by
    rw [factorization, atInfinity_mul]
    rfl
  rw [← mul_assoc, ← embeddedFactorization, planeHeightLog_atInfinity,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.real_heightLog_formula realMatrix parabolicElement
      orthogonalElement factorization orthogonality cornerValue] at formula
  exact formula

theorem flatSection_integral_real_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3)
    (integralMatrix : IntegralGL3) (parameter : ℂ) :
    sectionFamily parameter (rationalGroup (integralRational integralMatrix) * atInfinity realMatrix) =
      Complex.exp ((parameter - cohomologicalPoint) *
        ((Real.log |realMatrix.val.det| / 3 -
          Real.log ‖(WithLp.toLp 2 ((fun column => (integralMatrix.val 2 column : ℝ)) ᵥ*
            realMatrix.val) : EuclideanSpace ℝ (Fin 3))‖ : ℝ) : ℂ)) *
        sectionFamily cohomologicalPoint
          (rationalGroup (integralRational integralMatrix) * atInfinity realMatrix) := by
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralGroup_eq_mul, mul_assoc,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute, ← mul_assoc, ← atInfinity_mul]
  have formula := flatSection_real_integral_parameter flatSection
    (GeneralLinearGroup.map (Int.castRingHom ℝ) integralMatrix * realMatrix)
    integralMatrix parameter
  rw [Units.val_mul, Matrix.det_mul, abs_mul,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds.abs_det_integral_real, one_mul] at formula
  exact formula

theorem eisensteinSummand_atInfinity_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3)
    (flag : Flags .plane) (parameter : ℂ) :
    eisensteinSummand sectionFamily parameter (atInfinity realMatrix) flag =
      Complex.exp ((parameter - cohomologicalPoint) *
        ((Real.log |realMatrix.val.det| / 3 -
          Real.log ‖(WithLp.toLp 2 ((fun column =>
            (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ)) ᵥ*
              realMatrix.val) : EuclideanSpace ℝ (Fin 3))‖ : ℝ) : ℂ)) *
        eisensteinSummand sectionFamily cohomologicalPoint (atInfinity realMatrix) flag := by
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.eisensteinSummand_eq_integral (flatSection.1 parameter),
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.eisensteinSummand_eq_integral (flatSection.1 cohomologicalPoint),
    ← map_inv]
  exact flatSection_integral_real_parameter flatSection realMatrix
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)⁻¹ parameter

theorem eisensteinSummand_one_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (flag : Flags .plane) (parameter : ℂ) :
    eisensteinSummand sectionFamily parameter 1 flag =
      Complex.exp (-(parameter - cohomologicalPoint) * (Real.log (flagRadius flag) : ℂ)) *
        eisensteinSummand sectionFamily cohomologicalPoint 1 flag := by
  have formula := eisensteinSummand_atInfinity_parameter flatSection 1 flag parameter
  have atInfinityOne : atInfinity (1 : RealGL3) = 1 := by
    apply Units.ext
    apply Matrix.ext
    intro row column
    change ((1 : Matrix (Fin 3) (Fin 3) ℝ) row column,
      (1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) row column) =
        (1 : Matrix (Fin 3) (Fin 3) Adeles) row column
    by_cases equality : row = column <;> simp [Matrix.one_apply, equality]
  simpa only [atInfinityOne, Units.val_one, Matrix.det_one, abs_one, Real.log_one,
    zero_div, zero_sub, Matrix.vecMul_one, flagRadius, Complex.ofReal_neg, mul_neg,
    neg_mul] using formula

theorem eisensteinSummand_one_change_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (flag : Flags .plane)
    (parameter reference : ℂ) :
    eisensteinSummand sectionFamily parameter 1 flag =
      Complex.exp (-(parameter - reference) * (Real.log (flagRadius flag) : ℂ)) *
        eisensteinSummand sectionFamily reference 1 flag := by
  rw [eisensteinSummand_one_parameter flatSection flag parameter,
    eisensteinSummand_one_parameter flatSection flag reference, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem norm_eisensteinSummand_one_change_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (flag : Flags .plane)
    (parameter reference : ℂ) :
    ‖eisensteinSummand sectionFamily parameter 1 flag‖ =
      (flagRadius flag) ^ (-(parameter.re - reference.re)) *
        ‖eisensteinSummand sectionFamily reference 1 flag‖ := by
  rw [eisensteinSummand_one_change_parameter flatSection flag parameter reference,
    norm_mul, Complex.norm_exp, Real.rpow_def_of_pos (flagRadius_pos flag)]
  congr 2
  simp [mul_comm]

theorem norm_eisensteinSummand_one_antitone {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (flag : Flags .plane)
    (parameter reference : ℂ) (parameterBound : reference.re ≤ parameter.re) :
    ‖eisensteinSummand sectionFamily parameter 1 flag‖ ≤
      ‖eisensteinSummand sectionFamily reference 1 flag‖ := by
  rw [norm_eisensteinSummand_one_change_parameter flatSection flag parameter reference]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.rpow_le_one_of_one_le_of_nonpos (one_le_flagRadius flag) (by linarith))

noncomputable def flagHeight (realMatrix : RealGL3) (flag : Flags .plane) : ℝ :=
  Real.log |realMatrix.val.det| / 3 -
    Real.log ‖(WithLp.toLp 2 ((fun column =>
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ)) ᵥ* realMatrix.val) :
        EuclideanSpace ℝ (Fin 3))‖

theorem flagHeight_boundedAbove (realMatrix : RealGL3) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ flag, flagHeight realMatrix flag ≤ bound := by
  let equivalence := TernaryPeriodPolynomials.PlaneEisensteinContinuation.RowAction.rowAction realMatrix
  let lowerBound := ‖equivalence.symm.toContinuousLinearMap‖⁻¹
  have positiveLowerBound : 0 < lowerBound := inv_pos.mpr equivalence.norm_symm_pos
  have rowLowerBound (flag : Flags .plane) : lowerBound ≤
      ‖(WithLp.toLp 2 ((fun column =>
        (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ)) ᵥ* realMatrix.val) :
          EuclideanSpace ℝ (Fin 3))‖ := by
    let row : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2
      (fun column => (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ))
    have inverseBound := equivalence.symm.toContinuousLinearMap.le_opNorm (equivalence row)
    change ‖equivalence.symm (equivalence row)‖ ≤ _ at inverseBound
    rw [equivalence.symm_apply_apply] at inverseBound
    have productBound : 1 ≤ ‖equivalence.symm.toContinuousLinearMap‖ * ‖equivalence row‖ :=
      (one_le_flagRadius flag).trans inverseBound
    change ‖equivalence.symm.toContinuousLinearMap‖⁻¹ ≤ ‖equivalence row‖
    exact (inv_le_iff_one_le_mul₀ equivalence.norm_symm_pos).mpr
      (by simpa only [mul_comm] using productBound)
  refine ⟨max 0 (Real.log |realMatrix.val.det| / 3 - Real.log lowerBound),
    le_max_left _ _, fun flag => ?_⟩
  exact (sub_le_sub_left (Real.log_le_log positiveLowerBound (rowLowerBound flag)) _).trans
    (le_max_right _ _)

theorem eisensteinSummand_atInfinity_change_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3)
    (flag : Flags .plane) (parameter reference : ℂ) :
    eisensteinSummand sectionFamily parameter (atInfinity realMatrix) flag =
      Complex.exp ((parameter - reference) * (flagHeight realMatrix flag : ℂ)) *
        eisensteinSummand sectionFamily reference (atInfinity realMatrix) flag := by
  rw [eisensteinSummand_atInfinity_parameter flatSection realMatrix flag parameter,
    eisensteinSummand_atInfinity_parameter flatSection realMatrix flag reference,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  dsimp only [flagHeight]
  ring

theorem norm_eisensteinSummand_atInfinity_change_parameter
    {degree : ℕ} {data : InducingData degree} {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3)
    (flag : Flags .plane) (parameter reference : ℂ) :
    ‖eisensteinSummand sectionFamily parameter (atInfinity realMatrix) flag‖ =
      Real.exp ((parameter.re - reference.re) * flagHeight realMatrix flag) *
        ‖eisensteinSummand sectionFamily reference (atInfinity realMatrix) flag‖ := by
  rw [eisensteinSummand_atInfinity_change_parameter flatSection realMatrix flag parameter reference,
    norm_mul, Complex.norm_exp]
  simp

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarParameter
