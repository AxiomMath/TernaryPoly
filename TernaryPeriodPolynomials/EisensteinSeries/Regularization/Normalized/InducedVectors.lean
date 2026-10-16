module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.InducedVectorCovariance

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def normalizedCuspVector
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) : inducingData.cusp.smooth :=
  normPower (GeneralLinearGroup.det matrix) (-((degree : ℂ) + 3) / 3) •
    inducedCuspVector (induced (parameter - ((degree : ℂ) + 3) / 2)) matrix

theorem normalizedCuspVector_realize
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) (binary : BinaryAdelicGL) :
    inducingData.cusp.realize (normalizedCuspVector induced parameter matrix) binary =
      normPower (GeneralLinearGroup.det binary) (-inductionExponent .plane parameter) *
        unitaryNormalize degree family parameter (planeLevi binary 1 * matrix) := by
  rw [unitaryNormalize_binary_orbit_value]
  simp only [normalizedCuspVector, map_smul, Pi.smul_apply, smul_eq_mul, inducedCuspVector_realize]

theorem normalizedCuspVector_at_one
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) :
    inducingData.cusp.realize (normalizedCuspVector induced parameter matrix) 1 =
      unitaryNormalize degree family parameter matrix := by
  rw [normalizedCuspVector_realize, map_one, normPower_one, one_mul]
  have levi_one : planeLevi (1 : BinaryAdelicGL) 1 = 1 := (planeLeviHom Adeles).map_one
  rw [levi_one, one_mul]

theorem normalizedCuspVector_reconstruct
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) (binary : BinaryAdelicGL) :
    unitaryNormalize degree family parameter (planeLevi binary 1 * matrix) =
      normPower (GeneralLinearGroup.det binary) (inductionExponent .plane parameter) *
        inducingData.cusp.realize (normalizedCuspVector induced parameter matrix) binary := by
  rw [normalizedCuspVector_realize, ← mul_assoc, ← normPower_add, add_neg_cancel, normPower_zero, one_mul]

theorem normalizedCuspVector_binary
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) (binary : BinaryAdelicGL) :
    normalizedCuspVector induced parameter (planeLevi binary 1 * matrix) =
      normPower (GeneralLinearGroup.det binary) (inductionExponent .plane parameter) •
        (⟨inducingData.cusp.π binary (normalizedCuspVector induced parameter matrix).val,
          inducingData.cusp.smooth_stable binary _ (normalizedCuspVector induced parameter matrix).property⟩ :
            inducingData.cusp.smooth) := by
  apply inducingData.cusp.injective
  funext argument
  rw [map_smul, Pi.smul_apply, smul_eq_mul, inducingData.cusp.equivariant,
    normalizedCuspVector_realize, ← mul_assoc, ← planeLevi_binary_mul,
    normalizedCuspVector_reconstruct induced parameter matrix (argument * binary), map_mul, normPower_mul]
  have cancel : normPower (GeneralLinearGroup.det argument) (-inductionExponent .plane parameter) *
      normPower (GeneralLinearGroup.det argument) (inductionExponent .plane parameter) = 1 := by
    rw [← normPower_add, neg_add_cancel, normPower_zero]
  calc
    _ = (normPower (GeneralLinearGroup.det argument) (-inductionExponent .plane parameter) *
        normPower (GeneralLinearGroup.det argument) (inductionExponent .plane parameter)) *
        (normPower (GeneralLinearGroup.det binary) (inductionExponent .plane parameter) *
          inducingData.cusp.realize (normalizedCuspVector induced parameter matrix) (argument * binary)) := by ring
    _ = _ := by rw [cancel, one_mul]

theorem normalizedCuspVector_rankOne
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) (scalar : Adelesˣ) :
    normalizedCuspVector induced parameter (planeLevi 1 scalar * matrix) =
      (inducingData.chi.toMonoidHom scalar * normPower scalar (-2 * inductionExponent .plane parameter)) •
        normalizedCuspVector induced parameter matrix := by
  apply inducingData.cusp.injective
  funext binary
  rw [map_smul, Pi.smul_apply, smul_eq_mul, normalizedCuspVector_realize, normalizedCuspVector_realize,
    ← mul_assoc, planeLevi_binary_rankOne_commute, mul_assoc, unitaryNormalize_rankOne induced]
  ring

theorem normalizedCuspVector_unipotent
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) (first second : Adeles) :
    normalizedCuspVector induced parameter (planeUnipotent first second * matrix) =
      normalizedCuspVector induced parameter matrix := by
  rw [normalizedCuspVector, normalizedCuspVector, map_mul, det_planeUnipotent, one_mul,
    inducedCuspVector_unipotent]

theorem normalizedCuspVector_finite_level
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) (level : finiteLevel) :
    normalizedCuspVector induced parameter (matrix * atFinite level.val) =
      normalizedCuspVector induced parameter matrix := by
  apply inducingData.cusp.injective
  funext binary
  rw [normalizedCuspVector_realize, normalizedCuspVector_realize, ← mul_assoc,
    unitaryNormalize_finite_level induced]

theorem normalizedCuspVector_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) : Continuous (fun matrix => (normalizedCuspVector induced parameter matrix).val) := by
  exact (normPower_continuous.comp (adelicDet_continuous.prodMk continuous_const)).smul
    (inducedCuspVector_continuous (induced (parameter - ((degree : ℂ) + 3) / 2)))

theorem normalizedCuspVector_flat_compact
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (matrix : AdelicGL)
    (compact : inMaximalCompact matrix) :
    normalizedCuspVector flat.1 parameter matrix = inducedCuspVector (flat.1 cohomologicalPoint) matrix := by
  rw [normalizedCuspVector, normPower_det_compact matrix compact, one_smul,
    inducedCuspVector_flat_compact flat _ matrix compact]

theorem normalizedCuspVector_binary_norm
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) (binary : BinaryAdelicGL) :
    ‖(normalizedCuspVector induced parameter (planeLevi binary 1 * matrix)).val‖ =
      Real.exp ((inductionExponent .plane parameter).re *
        Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ)) *
          ‖(normalizedCuspVector induced parameter matrix).val‖ := by
  rw [normalizedCuspVector_binary]
  change ‖normPower (GeneralLinearGroup.det binary) (inductionExponent .plane parameter) •
    inducingData.cusp.π binary (normalizedCuspVector induced parameter matrix).val‖ = _
  rw [norm_smul, normPower_norm, inducingData.cusp.unitary]

theorem normalizedCuspVector_rankOne_norm
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) (scalar : Adelesˣ) :
    ‖(normalizedCuspVector induced parameter (planeLevi 1 scalar * matrix)).val‖ =
      Real.exp ((-2 * inductionExponent .plane parameter).re * Real.log (adeleNorm scalar : ℝ)) *
        ‖(normalizedCuspVector induced parameter matrix).val‖ := by
  rw [normalizedCuspVector_rankOne]
  change ‖(inducingData.chi.toMonoidHom scalar * normPower scalar (-2 * inductionExponent .plane parameter)) •
    (normalizedCuspVector induced parameter matrix).val‖ = _
  rw [norm_smul, norm_mul, inducingData.chi.unitary, one_mul, normPower_norm]

theorem normalizedCuspVector_compact_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter matrix, inMaximalCompact matrix →
      ‖(normalizedCuspVector flat.1 parameter matrix).val‖ ≤ bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := inducedCuspVector_compact_bound flat
  refine ⟨bound, nonnegative, ?_⟩
  intro parameter matrix compact
  rw [normalizedCuspVector_flat_compact flat parameter matrix compact]
  exact bounded cohomologicalPoint matrix compact

theorem normalizedCuspVector_parabolic_norm_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter first second binary scalar compactMatrix,
      inMaximalCompact compactMatrix →
      ‖(normalizedCuspVector flat.1 parameter
        (planeUnipotent first second * planeLevi binary scalar * compactMatrix)).val‖ ≤
        Real.exp ((inductionExponent .plane parameter).re *
          Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) +
          (-2 * inductionExponent .plane parameter).re * Real.log (adeleNorm scalar : ℝ)) * bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedCuspVector_compact_bound flat
  refine ⟨bound, nonnegative, ?_⟩
  intro parameter first second binary scalar compactMatrix compact_spec
  rw [mul_assoc, normalizedCuspVector_unipotent, planeLevi_rankOne_binary binary scalar,
    mul_assoc, normalizedCuspVector_rankOne_norm, normalizedCuspVector_binary_norm, Real.exp_add]
  calc
    _ = (Real.exp ((inductionExponent .plane parameter).re *
          Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ)) *
        Real.exp ((-2 * inductionExponent .plane parameter).re * Real.log (adeleNorm scalar : ℝ))) *
        ‖(normalizedCuspVector flat.1 parameter compactMatrix).val‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (bounded parameter compactMatrix compact_spec) (by positivity)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
