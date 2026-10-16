module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.StandardAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BinaryRowMeasure
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.HilbertAction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertBinaryCovariance

theorem lineUnipotent_lineLevi (binary : BinaryAdelicGL)
    (coordinates : Adeles × Adeles) :
    lineUnipotent coordinates.1 coordinates.2 * lineLevi 1 binary =
      lineLevi 1 binary * lineUnipotent
        (BinaryGaussian.rowAction binary coordinates).1
        (BinaryGaussian.rowAction binary coordinates).2 := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [lineUnipotent, upperUnipotent, lineLevi_val, BinaryGaussian.rowAction,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem integrand_lineLevi {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (binary : BinaryAdelicGL) (argument : AdelicGL) (coordinates : Adeles × Adeles) :
    HilbertStandard.integrand data parameter function induced (lineLevi 1 binary * argument)
        coordinates =
      normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .plane parameter) •
        data.cusp.π binary
          (HilbertStandard.integrand data parameter function induced argument
            (BinaryGaussian.rowAction binary coordinates)) := by
  unfold HilbertStandard.integrand
  rw [mul_assoc (weyl⁻¹ : AdelicGL), ← mul_assoc (lineUnipotent _ _),
    lineUnipotent_lineLevi]
  rw [mul_assoc (lineLevi 1 binary)
    (lineUnipotent (BinaryGaussian.rowAction binary coordinates).1
      (BinaryGaussian.rowAction binary coordinates).2) argument,
    ← mul_assoc (weyl⁻¹ : AdelicGL) (lineLevi 1 binary), weyl_inverse_lineLevi]
  rw [mul_assoc (planeLevi binary 1) (weyl⁻¹ : AdelicGL),
    mul_assoc (weyl⁻¹ : AdelicGL)
      (lineUnipotent (BinaryGaussian.rowAction binary coordinates).1
        (BinaryGaussian.rowAction binary coordinates).2) argument]
  let base : AdelicGL := weyl⁻¹ *
    (lineUnipotent (BinaryGaussian.rowAction binary coordinates).1
      (BinaryGaussian.rowAction binary coordinates).2 * argument)
  change (CuspLift.vector data .plane parameter function induced
      (binaryLevi .plane binary * base)).val =
    normPower (GeneralLinearGroup.det binary)
      (binaryInductionExponent degree .plane parameter) •
      data.cusp.π binary (CuspLift.vector data .plane parameter function induced base).val
  exact CuspLiftCovariance.vector_binary data .plane parameter function induced binary base

theorem value_lineLevi_raw {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (binary : BinaryAdelicGL) (argument : AdelicGL) :
    ((adeleNorm (GeneralLinearGroup.det binary) : ℝ) •
      HilbertStandard.value data parameter function induced (lineLevi 1 binary * argument)) =
      normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .plane parameter) •
        data.cusp.π binary (HilbertStandard.value data parameter function induced argument) := by
  let transformed : Adeles × Adeles → data.cusp.H :=
    fun coordinates => HilbertStandard.integrand data parameter function induced argument
      (BinaryGaussian.rowAction binary coordinates)
  have commute : (∫ coordinates, data.cusp.π binary (transformed coordinates) ∂radicalMeasure) =
      data.cusp.π binary (∫ coordinates, transformed coordinates ∂radicalMeasure) :=
    (CuspHilbertAction.isometry data.cusp binary).integral_comp_comm transformed
  have scaled := BinaryRowMeasure.integral_row binary
    (HilbertStandard.integrand data parameter function induced argument)
  change (adeleNorm (GeneralLinearGroup.det binary) : ℝ) •
      (∫ coordinates, transformed coordinates ∂radicalMeasure) =
        HilbertStandard.value data parameter function induced argument at scaled
  unfold HilbertStandard.value
  simp_rw [integrand_lineLevi]
  rw [integral_smul, commute]
  rw [← IsScalarTower.algebraMap_smul (R := ℝ) ℂ]
  rw [smul_comm, ← map_smul, IsScalarTower.algebraMap_smul (R := ℝ) ℂ, scaled]
  rfl

theorem binaryExponent_shift (degree : ℕ) (parameter : ℂ) :
    binaryInductionExponent degree .plane parameter =
      binaryInductionExponent degree .line parameter + 1 := by
  simp only [binaryInductionExponent, inductionExponent]
  ring

theorem normPower_one_unit (unit : Adelesˣ) :
    normPower unit 1 = (adeleNorm unit : ℝ) := by
  have positive : (0 : ℝ) < (adeleNorm unit : ℝ) := adeleNorm_pos unit
  simp only [normPower, one_mul, ← Complex.ofReal_exp, Real.exp_log positive]

theorem value_lineLevi {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (binary : BinaryAdelicGL) (argument : AdelicGL) :
    HilbertStandard.value data parameter function induced (lineLevi 1 binary * argument) =
      normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .line parameter) •
        data.cusp.π binary (HilbertStandard.value data parameter function induced argument) := by
  apply smul_right_injective data.cusp.H
    (ne_of_gt (adeleNorm_pos (GeneralLinearGroup.det binary)))
  change (adeleNorm (GeneralLinearGroup.det binary) : ℝ) •
      HilbertStandard.value data parameter function induced (lineLevi 1 binary * argument) =
    (adeleNorm (GeneralLinearGroup.det binary) : ℝ) •
      (normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .line parameter) •
        data.cusp.π binary (HilbertStandard.value data parameter function induced argument))
  rw [value_lineLevi_raw data parameter function induced binary argument,
    ← IsScalarTower.algebraMap_smul (R := ℝ) ℂ, smul_smul,
    binaryExponent_shift, NormPower.normPower_add,
    normPower_one_unit, Complex.coe_algebraMap, mul_comm]

theorem lineOrbit_smooth {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL)
    (baseSmooth : HilbertStandard.value data parameter function induced argument ∈ data.cusp.smooth)
    (binary : BinaryAdelicGL) :
    HilbertStandard.value data parameter function induced (lineLevi 1 binary * argument) ∈
      data.cusp.smooth := by
  rw [value_lineLevi]
  exact data.cusp.smooth.smul_mem _
    (data.cusp.smooth_stable binary _ baseSmooth)

theorem normalized_lineOrbit_mem {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL)
    (baseSmooth : HilbertStandard.value data parameter function induced argument ∈ data.cusp.smooth) :
    (fun binary : BinaryAdelicGL =>
      normPower (GeneralLinearGroup.det binary)
          (-binaryInductionExponent degree .line parameter) *
        data.cusp.realize
          ⟨HilbertStandard.value data parameter function induced (lineLevi 1 binary * argument),
            lineOrbit_smooth data parameter function induced argument baseSmooth binary⟩ 1) ∈
      cuspFunctions data.cusp := by
  let base : data.cusp.smooth :=
    ⟨HilbertStandard.value data parameter function induced argument, baseSmooth⟩
  refine ⟨base, ?_⟩
  funext binary
  let acted : data.cusp.smooth :=
    ⟨data.cusp.π binary base.val, data.cusp.smooth_stable binary base.val base.property⟩
  have orbit : (⟨HilbertStandard.value data parameter function induced
      (lineLevi 1 binary * argument),
      lineOrbit_smooth data parameter function induced argument baseSmooth binary⟩ :
      data.cusp.smooth) =
        normPower (GeneralLinearGroup.det binary)
          (binaryInductionExponent degree .line parameter) • acted := by
    apply Subtype.ext
    exact value_lineLevi data parameter function induced binary argument
  change data.cusp.realize base binary =
    normPower (GeneralLinearGroup.det binary)
      (-binaryInductionExponent degree .line parameter) *
        data.cusp.realize _ 1
  rw [orbit, map_smul, Pi.smul_apply]
  change data.cusp.realize base binary =
    normPower _ _ * (normPower _ _ * data.cusp.realize acted 1)
  rw [ParabolicInvariance.normPower_neg_mul, data.cusp.equivariant]
  simp

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertBinaryCovariance
