module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.InducedVectors
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Plane.LeviMultiplication

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem planeLevi_binary_rankOne_commute {R : Type*} [CommRing R]
    (binary : GeneralLinearGroup (Fin 2) R) (scalar : Rˣ) :
    planeLevi binary 1 * planeLevi 1 scalar = planeLevi 1 scalar * planeLevi binary 1 := by
  change (planeLeviHom R) (binary, 1) * (planeLeviHom R) (1, scalar) =
    (planeLeviHom R) (1, scalar) * (planeLeviHom R) (binary, 1)
  rw [← map_mul, ← map_mul]
  simp

theorem planeLevi_binary_unipotent {R : Type*} [CommRing R]
    (binary : GeneralLinearGroup (Fin 2) R) (first second : R) :
    planeLevi binary 1 * planeUnipotent first second =
      planeUnipotent (binary.val 0 0 * first + binary.val 0 1 * second)
        (binary.val 1 0 * first + binary.val 1 1 * second) * planeLevi binary 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, planeUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem inducedCuspVector_reconstruct
    {degree : ℕ} {inducingData : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue) (matrix : AdelicGL) (binary : BinaryAdelicGL) :
    sectionValue (planeLevi binary 1 * matrix) =
      normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter) *
        inducingData.cusp.realize (inducedCuspVector induced matrix) binary := by
  rw [inducedCuspVector_realize, ← mul_assoc, ← normPower_add, add_neg_cancel, normPower_zero, one_mul]

theorem inducedCuspVector_binary
    {degree : ℕ} {inducingData : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue) (matrix : AdelicGL) (binary : BinaryAdelicGL) :
    inducedCuspVector induced (planeLevi binary 1 * matrix) =
      normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter) •
        (⟨inducingData.cusp.π binary (inducedCuspVector induced matrix).val,
          inducingData.cusp.smooth_stable binary _ (inducedCuspVector induced matrix).property⟩ :
            inducingData.cusp.smooth) := by
  apply inducingData.cusp.injective
  funext argument
  rw [map_smul, Pi.smul_apply, smul_eq_mul, inducingData.cusp.equivariant,
    inducedCuspVector_realize, ← mul_assoc, ← planeLevi_binary_mul,
    inducedCuspVector_reconstruct induced matrix (argument * binary), map_mul, normPower_mul]
  have cancel : normPower (GeneralLinearGroup.det argument) (-binaryInductionExponent degree .plane parameter) *
      normPower (GeneralLinearGroup.det argument) (binaryInductionExponent degree .plane parameter) = 1 := by
    rw [← normPower_add, neg_add_cancel, normPower_zero]
  calc
    _ = (normPower (GeneralLinearGroup.det argument) (-binaryInductionExponent degree .plane parameter) *
        normPower (GeneralLinearGroup.det argument) (binaryInductionExponent degree .plane parameter)) *
        (normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter) *
          inducingData.cusp.realize (inducedCuspVector induced matrix) (argument * binary)) := by ring
    _ = _ := by rw [cancel, one_mul]

theorem inducedCuspVector_rankOne
    {degree : ℕ} {inducingData : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue) (matrix : AdelicGL) (scalar : Adelesˣ) :
    inducedCuspVector induced (planeLevi 1 scalar * matrix) =
      (inducingData.chi.toMonoidHom scalar * normPower scalar (-2 * inductionExponent .plane parameter)) •
        inducedCuspVector induced matrix := by
  apply inducingData.cusp.injective
  funext binary
  rw [map_smul, Pi.smul_apply, smul_eq_mul, inducedCuspVector_realize, inducedCuspVector_realize,
    ← mul_assoc, planeLevi_binary_rankOne_commute, mul_assoc, induced.2.2.2.2.1]
  ring

theorem inducedCuspVector_unipotent
    {degree : ℕ} {inducingData : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue) (matrix : AdelicGL) (first second : Adeles) :
    inducedCuspVector induced (planeUnipotent first second * matrix) = inducedCuspVector induced matrix := by
  apply inducingData.cusp.injective
  funext binary
  rw [inducedCuspVector_realize, inducedCuspVector_realize, ← mul_assoc,
    planeLevi_binary_unipotent, mul_assoc, induced.2.2.2.1]

theorem inducedCuspVector_binary_norm
    {degree : ℕ} {inducingData : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue) (matrix : AdelicGL) (binary : BinaryAdelicGL) :
    ‖(inducedCuspVector induced (planeLevi binary 1 * matrix)).val‖ =
      Real.exp ((binaryInductionExponent degree .plane parameter).re *
        Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ)) *
          ‖(inducedCuspVector induced matrix).val‖ := by
  rw [inducedCuspVector_binary]
  change ‖normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter) •
    inducingData.cusp.π binary (inducedCuspVector induced matrix).val‖ = _
  rw [norm_smul, normPower_norm, inducingData.cusp.unitary]

theorem inducedCuspVector_rankOne_norm
    {degree : ℕ} {inducingData : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue) (matrix : AdelicGL) (scalar : Adelesˣ) :
    ‖(inducedCuspVector induced (planeLevi 1 scalar * matrix)).val‖ =
      Real.exp ((-2 * inductionExponent .plane parameter).re * Real.log (adeleNorm scalar : ℝ)) *
        ‖(inducedCuspVector induced matrix).val‖ := by
  rw [inducedCuspVector_rankOne]
  change ‖(inducingData.chi.toMonoidHom scalar * normPower scalar (-2 * inductionExponent .plane parameter)) •
    (inducedCuspVector induced matrix).val‖ = _
  rw [norm_smul, norm_mul, inducingData.chi.unitary, one_mul, normPower_norm]

theorem inducedCuspVector_parabolic_norm_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter first second binary scalar compactMatrix,
      inMaximalCompact compactMatrix →
      ‖(inducedCuspVector (flat.1 parameter)
        (planeUnipotent first second * planeLevi binary scalar * compactMatrix)).val‖ ≤
        Real.exp ((binaryInductionExponent degree .plane parameter).re *
          Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) +
          (-2 * inductionExponent .plane parameter).re * Real.log (adeleNorm scalar : ℝ)) * bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := inducedCuspVector_compact_bound flat
  refine ⟨bound, nonnegative, ?_⟩
  intro parameter first second binary scalar compactMatrix compact_spec
  rw [mul_assoc, inducedCuspVector_unipotent, planeLevi_rankOne_binary binary scalar,
    mul_assoc, inducedCuspVector_rankOne_norm, inducedCuspVector_binary_norm]
  rw [Real.exp_add]
  calc
    _ = (Real.exp ((binaryInductionExponent degree .plane parameter).re *
          Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ)) *
        Real.exp ((-2 * inductionExponent .plane parameter).re * Real.log (adeleNorm scalar : ℝ))) *
        ‖(inducedCuspVector (flat.1 parameter) compactMatrix).val‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (bounded parameter compactMatrix compact_spec) (by positivity)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
