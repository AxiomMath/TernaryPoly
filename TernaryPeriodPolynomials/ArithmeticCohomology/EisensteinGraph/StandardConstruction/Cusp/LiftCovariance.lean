module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.Lift
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.NormPower

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspLiftCovariance

theorem binaryLevi_mul (side : Side) (first second : BinaryAdelicGL) :
    binaryLevi side (first * second) = binaryLevi side first * binaryLevi side second := by
  cases side with
  | plane => simpa only [Prod.mk_mul_mk, one_mul, binaryLevi, planeLeviHom,
      MonoidHom.coe_mk, OneHom.coe_mk] using
      (planeLeviHom Adeles).map_mul (first, 1) (second, 1)
  | line => simpa only [Prod.mk_mul_mk, one_mul, binaryLevi, lineLeviHom,
      MonoidHom.coe_mk, OneHom.coe_mk] using
      (lineLeviHom Adeles).map_mul (1, first) (1, second)

theorem vector_binary {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) (binary : BinaryAdelicGL)
    (argument : AdelicGL) :
    (CuspLift.vector data side parameter function induced (binaryLevi side binary * argument)).val =
      normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree side parameter) •
        data.cusp.π binary (CuspLift.vector data side parameter function induced argument).val := by
  let acted : data.cusp.smooth :=
    ⟨data.cusp.π binary (CuspLift.vector data side parameter function induced argument).val,
      data.cusp.smooth_stable binary _
        (CuspLift.vector data side parameter function induced argument).property⟩
  have equality : CuspLift.vector data side parameter function induced
      (binaryLevi side binary * argument) =
        normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree side parameter) •
          acted := by
    apply data.cusp.injective
    funext test
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, acted, data.cusp.equivariant,
      CuspLift.realizes, map_mul, NormPower.normPower_mul_units, binaryLevi_mul, mul_assoc,
      ParabolicInvariance.normPower_neg]
    field_simp [ParabolicInvariance.normPower_ne_zero]
  exact congrArg Subtype.val equality

theorem vector_binary_norm {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) (binary : BinaryAdelicGL)
    (argument : AdelicGL) :
    ‖(CuspLift.vector data side parameter function induced
      (binaryLevi side binary * argument)).val‖ =
      (adeleNorm (GeneralLinearGroup.det binary) : ℝ) ^
        (binaryInductionExponent degree side parameter).re *
          ‖(CuspLift.vector data side parameter function induced argument).val‖ := by
  rw [vector_binary, norm_smul, NormPower.normPower_norm, data.cusp.unitary]

theorem scalar_binary {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) (binary : BinaryAdelicGL)
    (argument : AdelicGL) :
    function (binaryLevi side binary * argument) =
      normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree side parameter) *
        data.cusp.realize (CuspLift.vector data side parameter function induced argument) binary := by
  rw [CuspLift.realizes, ParabolicInvariance.normPower_neg,
    mul_inv_cancel_left₀ (ParabolicInvariance.normPower_ne_zero _ _)]

theorem flat_binary_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) :
    ∃ bound : ℝ, ∀ parameter binary compact, inMaximalCompact compact →
      ‖(CuspLift.vector data .plane parameter (extension parameter) (flat.1 parameter)
        (planeLevi binary 1 * compact)).val‖ ≤
        (adeleNorm (GeneralLinearGroup.det binary) : ℝ) ^
          (binaryInductionExponent degree .plane parameter).re * bound := by
  obtain ⟨bound, bounded⟩ := CuspLift.flat_bounded data extension flat
  refine ⟨bound, ?_⟩
  intro parameter binary compact membership
  rw [show planeLevi binary 1 = binaryLevi .plane binary from rfl, vector_binary_norm]
  exact mul_le_mul_of_nonneg_left (bounded parameter compact membership)
    (Real.rpow_nonneg (adeleNorm (GeneralLinearGroup.det binary)).property _)

theorem planeLevi_normalizes_radical (binary : BinaryAdelicGL) (first second : Adeles) :
    planeLevi binary 1 * planeUnipotent first second =
      planeUnipotent (binary.val 0 0 * first + binary.val 0 1 * second)
        (binary.val 1 0 * first + binary.val 1 1 * second) * planeLevi binary 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, planeUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem planeLevi_blocks_commute (binary : BinaryAdelicGL) (unit : Adelesˣ) :
    planeLevi binary 1 * planeLevi 1 unit = planeLevi 1 unit * planeLevi binary 1 := by
  change (planeLeviHom Adeles) (binary, 1) * (planeLeviHom Adeles) (1, unit) =
    (planeLeviHom Adeles) (1, unit) * (planeLeviHom Adeles) (binary, 1)
  rw [← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, one_mul, mul_one]

theorem vector_plane_radical {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (first second : Adeles)
    (argument : AdelicGL) :
    CuspLift.vector data .plane parameter function induced
      (planeUnipotent first second * argument) =
        CuspLift.vector data .plane parameter function induced argument := by
  apply data.cusp.injective
  funext binary
  simp only [CuspLift.realizes, binaryLevi]
  rw [← mul_assoc, planeLevi_normalizes_radical, mul_assoc, induced.2.2.2.1]

theorem vector_plane_rankOne {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (unit : Adelesˣ)
    (argument : AdelicGL) :
    CuspLift.vector data .plane parameter function induced (planeLevi 1 unit * argument) =
      (data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter)) •
        CuspLift.vector data .plane parameter function induced argument := by
  apply data.cusp.injective
  funext binary
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, CuspLift.realizes, binaryLevi]
  rw [← mul_assoc, planeLevi_blocks_commute, mul_assoc, induced.2.2.2.2.1]
  ring

theorem vector_plane_decomposition_norm {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (first second : Adeles)
    (binary : BinaryAdelicGL) (unit : Adelesˣ) (compact : AdelicGL) :
    ‖(CuspLift.vector data .plane parameter function induced
      (planeUnipotent first second * planeLevi binary unit * compact)).val‖ =
      (adeleNorm unit : ℝ) ^ (-2 * inductionExponent .plane parameter).re *
        (adeleNorm (GeneralLinearGroup.det binary) : ℝ) ^
          (binaryInductionExponent degree .plane parameter).re *
            ‖(CuspLift.vector data .plane parameter function induced compact).val‖ := by
  rw [mul_assoc, vector_plane_radical, FlatUniqueness.planeLevi_split, mul_assoc,
    vector_plane_rankOne]
  change ‖(data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter)) •
    (CuspLift.vector data .plane parameter function induced (planeLevi binary 1 * compact)).val‖ = _
  rw [norm_smul, norm_mul, data.chi.unitary, one_mul, NormPower.normPower_norm,
    show planeLevi binary 1 = binaryLevi .plane binary from rfl, vector_binary_norm, mul_assoc]

theorem flat_plane_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) :
    ∃ bound : ℝ, ∀ parameter first second binary unit compact, inMaximalCompact compact →
      ‖(CuspLift.vector data .plane parameter (extension parameter) (flat.1 parameter)
        (planeUnipotent first second * planeLevi binary unit * compact)).val‖ ≤
        ((adeleNorm unit : ℝ) ^ (-2 * inductionExponent .plane parameter).re *
          (adeleNorm (GeneralLinearGroup.det binary) : ℝ) ^
            (binaryInductionExponent degree .plane parameter).re) * bound := by
  obtain ⟨bound, bounded⟩ := CuspLift.flat_bounded data extension flat
  refine ⟨bound, ?_⟩
  intro parameter first second binary unit compact membership
  rw [vector_plane_decomposition_norm]
  exact mul_le_mul_of_nonneg_left (bounded parameter compact membership)
    (mul_nonneg (Real.rpow_nonneg (adeleNorm unit).property _)
      (Real.rpow_nonneg (adeleNorm (GeneralLinearGroup.det binary)).property _))

theorem flat_scalar_formula {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ)
    (compact : AdelicGL) (membership : inMaximalCompact compact) :
    extension parameter (planeUnipotent first second * planeLevi binary unit * compact) =
      (data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter)) *
        normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter) *
          data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
            (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact) binary := by
  rw [mul_assoc, (flat.1 parameter).2.2.2.1, FlatUniqueness.planeLevi_split,
    mul_assoc, (flat.1 parameter).2.2.2.2.1]
  rw [show planeLevi binary 1 = binaryLevi .plane binary from rfl,
    scalar_binary data .plane parameter _ (flat.1 parameter) binary compact,
    CuspLift.flat_vector data extension flat parameter compact membership]
  simp only [mul_assoc]

theorem flat_scalar_bound_at_compact {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (compact : AdelicGL) (membership : inMaximalCompact compact) :
    ∃ bound : ℝ, ∀ parameter first second binary unit,
      ‖extension parameter (planeUnipotent first second * planeLevi binary unit * compact)‖ ≤
        ((adeleNorm unit : ℝ) ^ (-2 * inductionExponent .plane parameter).re *
          (adeleNorm (GeneralLinearGroup.det binary) : ℝ) ^
            (binaryInductionExponent degree .plane parameter).re) * bound := by
  obtain ⟨bound, bounded⟩ := data.cusp.bounded (CuspLift.vector data .plane cohomologicalPoint
    (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact)
  refine ⟨bound, ?_⟩
  intro parameter first second binary unit
  rw [flat_scalar_formula data extension flat parameter first second binary unit compact membership]
  simp only [norm_mul, data.chi.unitary, one_mul, NormPower.normPower_norm]
  exact mul_le_mul_of_nonneg_left (bounded binary)
    (mul_nonneg (Real.rpow_nonneg (adeleNorm unit).property _)
      (Real.rpow_nonneg (adeleNorm (GeneralLinearGroup.det binary)).property _))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspLiftCovariance
