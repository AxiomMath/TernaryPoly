module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.RowBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedHeight
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.Realization

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HeightMajorant

theorem compact_planeBinary_realizationSeminorm_eq {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (binary : BinaryAdelicGL)
    (argument : AdelicGL) (compact : inMaximalCompact (planeLevi binary 1)) :
    CuspRealization.realizationSeminorm data.cusp
        (CuspLift.vector data .plane parameter function induced
          (planeLevi binary 1 * argument)) =
      CuspRealization.realizationSeminorm data.cusp
        (CuspLift.vector data .plane parameter function induced argument) := by
  rw [CuspRealization.realizationSeminorm_cuspLift_planeBinary]
  have determinant : GeneralLinearGroup.det (planeLevi binary 1) =
      GeneralLinearGroup.det binary := by
    rw [InducedHeight.planeLevi_det]
    simp
  have normBinary : adeleNorm (GeneralLinearGroup.det binary) = 1 := by
    rw [← determinant]
    exact InducedHeight.compact_det_norm _ compact
  simp [normBinary]

theorem compact_planeParabolic_realizationSeminorm_eq {degree : ℕ}
    (data : InducingData degree) (extension : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension) (first second : Adeles)
    (binary : BinaryAdelicGL) (unit : Adelesˣ) (compact : AdelicGL)
    (binaryCompact : inMaximalCompact (planeLevi binary 1)) :
    CuspRealization.realizationSeminorm data.cusp
        (CuspLift.vector data .plane cohomologicalPoint (extension cohomologicalPoint)
          (flat.1 cohomologicalPoint)
          (planeUnipotent first second * planeLevi binary unit * compact)) =
      CuspRealization.realizationSeminorm data.cusp
        (CuspLift.vector data .plane cohomologicalPoint (extension cohomologicalPoint)
          (flat.1 cohomologicalPoint) compact) := by
  rw [mul_assoc, CuspLiftCovariance.vector_plane_radical,
    FlatUniqueness.planeLevi_split, mul_assoc,
    CuspRealization.realizationSeminorm_cuspLift_planeRankOne_cohomological,
    compact_planeBinary_realizationSeminorm_eq data cohomologicalPoint
      (extension cohomologicalPoint) (flat.1 cohomologicalPoint) binary compact binaryCompact]

theorem negative_power_bound {height constant value exponent : ℝ}
    (positiveHeight : 0 < height) (positiveConstant : 0 < constant)
    (lower : height ≤ constant * value) (negative : exponent ≤ 0) :
    value ^ exponent ≤ constant ^ (-exponent) * height ^ exponent := by
  have lower' : height / constant ≤ value :=
    (div_le_iff₀ positiveConstant).mpr (by simpa only [mul_comm] using lower)
  have estimate := Real.rpow_le_rpow_of_nonpos
    (div_pos positiveHeight positiveConstant) lower' negative
  rw [Real.div_rpow positiveHeight.le positiveConstant.le, div_eq_mul_inv,
    ← Real.rpow_neg positiveConstant.le] at estimate
  simpa only [mul_comm] using estimate

theorem exponent_lt (degree : ℕ) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    -((degree : ℝ) + 6) / 2 - parameter.re < -3 := by
  linarith

theorem domain_majorant (argument : AdelicGL) (exponent : ℝ) (negative : exponent < -3) :
    ∃ majorant : Flags .plane → ℝ,
      (∀ flag, 0 ≤ majorant flag) ∧ Summable majorant ∧
      ∀ coordinates ∈ additiveDomain ×ˢ additiveDomain, ∀ flag : Flags .plane,
      ∀ first second : Adeles, ∀ binary : BinaryAdelicGL, ∀ unit : Adelesˣ,
      ∀ compact : AdelicGL, inMaximalCompact compact →
      rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ)
          (IntegerRows.flagRepresentative flag))⁻¹) *
          (lineUnipotent coordinates.1 coordinates.2 * argument) =
        planeUnipotent first second * planeLevi binary unit * compact →
      (adeleNorm unit : ℝ) ^ exponent ≤ majorant flag := by
  obtain ⟨constant, positive, bounded⟩ := CompactRowBounds.domain_height_bound argument
  refine ⟨fun flag => constant ^ (-exponent) * FlagSummability.flagHeight flag ^ exponent,
    fun flag => mul_nonneg (Real.rpow_nonneg positive.le _)
      (Real.rpow_nonneg (FlagSummability.flagHeight_pos flag).le _),
    (FlagSummability.flagHeight_summable exponent negative).mul_left _, ?_⟩
  intro coordinates membership flag first second binary unit compact compactMembership decomposition
  exact negative_power_bound (FlagSummability.flagHeight_pos flag) positive
    (bounded coordinates membership (IntegerRows.flagRepresentative flag)
      first second binary unit compact compactMembership decomposition) (by linarith)

theorem lineUnipotent_det (first second : Adeles) :
    GeneralLinearGroup.det (lineUnipotent first second) = 1 := by
  apply Units.ext
  simp [lineUnipotent, upperUnipotent, GeneralLinearGroup.det, Matrix.det_fin_three]

theorem rational_det_norm (rational : RationalGL3) :
    adeleNorm (GeneralLinearGroup.det (rationalGroup rational)) = 1 := by
  change adeleNorm (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele rational)) = 1
  rw [GeneralLinearGroup.map_det]
  exact RationalNorm.rational_norm _

theorem translated_det_norm (rational : RationalGL3) (coordinates : Adeles × Adeles)
    (argument : AdelicGL) :
    adeleNorm (GeneralLinearGroup.det
      (rationalGroup rational * (lineUnipotent coordinates.1 coordinates.2 * argument))) =
        adeleNorm (GeneralLinearGroup.det argument) := by
  simp only [map_mul, rational_det_norm, lineUnipotent_det, one_mul]

theorem summand_integralRepresentative {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (flag : Flags .plane) :
    eisensteinSummand extension parameter argument flag =
      extension parameter (rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ)
        (IntegerRows.flagRepresentative flag))⁻¹) * argument) := by
  conv_lhs => rw [← IntegerRows.flagRepresentative_spec flag]
  exact RationalEisenstein.eisensteinSummand_mk data extension parameter induced argument _

theorem scalar_decomposition_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compact, inMaximalCompact compact → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact) binary‖ ≤ bound)
    (parameter : ℂ) (first second : Adeles) (binary : BinaryAdelicGL)
    (unit : Adelesˣ) (compact : AdelicGL) (membership : inMaximalCompact compact) :
    ‖extension parameter (planeUnipotent first second * planeLevi binary unit * compact)‖ ≤
      ((adeleNorm (GeneralLinearGroup.det
        (planeUnipotent first second * planeLevi binary unit * compact)) : ℝ) ^
          (binaryInductionExponent degree .plane parameter).re *
        (adeleNorm unit : ℝ) ^ (-((degree : ℝ) + 6) / 2 - parameter.re)) * bound := by
  rw [← InducedHeight.plane_weight_identity degree parameter first second binary unit compact membership,
    CuspLiftCovariance.flat_scalar_formula data extension flat parameter
      first second binary unit compact membership]
  simp only [norm_mul, data.chi.unitary, one_mul, NormPower.normPower_norm]
  exact mul_le_mul_of_nonneg_left (bounded compact membership binary)
    (mul_nonneg (Real.rpow_nonneg (adeleNorm unit).property _)
      (Real.rpow_nonneg (adeleNorm (GeneralLinearGroup.det binary)).property _))

theorem scalar_decomposition_bound_of_realizationSeminorm {degree : ℕ}
    (data : InducingData degree) (extension : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension) (bound : ℝ)
    (seminormBound : ∀ compact, inMaximalCompact compact →
      CuspRealization.realizationSeminorm data.cusp
        (CuspLift.vector data .plane cohomologicalPoint (extension cohomologicalPoint)
          (flat.1 cohomologicalPoint) compact) ≤ bound)
    (parameter : ℂ) (first second : Adeles) (binary : BinaryAdelicGL)
    (unit : Adelesˣ) (compact : AdelicGL) (membership : inMaximalCompact compact) :
    ‖extension parameter (planeUnipotent first second * planeLevi binary unit * compact)‖ ≤
      ((adeleNorm (GeneralLinearGroup.det
        (planeUnipotent first second * planeLevi binary unit * compact)) : ℝ) ^
          (binaryInductionExponent degree .plane parameter).re *
        (adeleNorm unit : ℝ) ^ (-((degree : ℝ) + 6) / 2 - parameter.re)) * bound := by
  apply scalar_decomposition_bound data extension flat bound
    (fun compact compactMembership binary =>
      CuspRealization.flat_vector_uniform_binary_bound data extension flat bound
        seminormBound cohomologicalPoint compact compactMembership binary)
    parameter first second binary unit compact membership

theorem cuspLift_scalar_evaluation_continuous {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (binary : BinaryAdelicGL) :
    Continuous (fun compact : AdelicGL =>
      data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact) binary) := by
  have pointwise : (fun compact : AdelicGL =>
      data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact) binary) =
    (fun compact => normPower (GeneralLinearGroup.det binary)
      (-binaryInductionExponent degree .plane cohomologicalPoint) *
      extension cohomologicalPoint (binaryLevi .plane binary * compact)) := by
    funext compact
    exact CuspLift.realizes data .plane cohomologicalPoint (extension cohomologicalPoint)
      (flat.1 cohomologicalPoint) compact binary
  rw [pointwise]
  exact continuous_const.mul
    ((InducedContinuity.induced_continuous data .plane cohomologicalPoint
      (extension cohomologicalPoint) (flat.1 cohomologicalPoint)).comp
      (continuous_const.mul continuous_id))

theorem flat_cuspLift_realizationSeminorm_lowerSemicontinuous {degree : ℕ}
    (data : InducingData degree) (extension : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension) :
    LowerSemicontinuous (fun compact : AdelicGL => CuspRealization.realizationSeminorm
      data.cusp (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact)) := by
  exact CuspRealization.seminorm_lowerSemicontinuous data.cusp
    (fun compact => CuspLift.vector data .plane cohomologicalPoint
      (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact)
    (fun binary => cuspLift_scalar_evaluation_continuous data extension flat binary)

theorem scalar_domain_majorant {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compact, inMaximalCompact compact → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact) binary‖ ≤ bound)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    ∃ majorant : Flags .plane → ℝ, (∀ flag, 0 ≤ majorant flag) ∧ Summable majorant ∧
      ∀ coordinates ∈ additiveDomain ×ˢ additiveDomain, ∀ flag,
        ‖eisensteinSummand extension parameter
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag‖ ≤ majorant flag := by
  obtain ⟨majorant, nonnegative, summable, dominates⟩ := domain_majorant argument
    (-((degree : ℝ) + 6) / 2 - parameter.re) (exponent_lt degree parameter halfPlane)
  let factor := (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
    (binaryInductionExponent degree .plane parameter).re
  have factorNonnegative : 0 ≤ factor := Real.rpow_nonneg (adeleNorm _).property _
  refine ⟨fun flag => (factor * majorant flag) * max bound 0,
    fun flag => mul_nonneg (mul_nonneg factorNonnegative (nonnegative flag)) (le_max_right _ _),
    (summable.mul_left factor).mul_right _, ?_⟩
  intro coordinates membership flag
  obtain ⟨first, second, binary, unit, compact, compactMembership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition
      (rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ)
        (IntegerRows.flagRepresentative flag))⁻¹) *
          (lineUnipotent coordinates.1 coordinates.2 * argument))
  have estimate := scalar_decomposition_bound data extension flat (max bound 0)
    (fun compact membership binary => (bounded compact membership binary).trans (le_max_left _ _))
    parameter first second binary unit compact compactMembership
  rw [← decomposition, translated_det_norm] at estimate
  rw [summand_integralRepresentative data extension parameter (flat.1 parameter)]
  exact estimate.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (dominates coordinates membership flag first second binary unit compact compactMembership decomposition)
      factorNonnegative) (le_max_right _ _))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HeightMajorant
