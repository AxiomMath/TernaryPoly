module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.MaximalCompact

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def inducedCuspVector
    {degree : ℕ} {inducingData : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue) (matrix : AdelicGL) :
    inducingData.cusp.smooth :=
  Classical.choose (induced.2.2.2.2.2 matrix)

theorem inducedCuspVector_realize
    {degree : ℕ} {inducingData : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue) (matrix : AdelicGL) (binary : BinaryAdelicGL) :
    inducingData.cusp.realize (inducedCuspVector induced matrix) binary =
      normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .plane parameter) *
        sectionValue (planeLevi binary 1 * matrix) :=
  congrFun (Classical.choose_spec (induced.2.2.2.2.2 matrix)) binary

theorem inducedCuspVector_at_one
    {degree : ℕ} {inducingData : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue) (matrix : AdelicGL) :
    inducingData.cusp.realize (inducedCuspVector induced matrix) 1 = sectionValue matrix := by
  rw [inducedCuspVector_realize, map_one, normPower_one, one_mul]
  have levi_one : planeLevi (1 : BinaryAdelicGL) 1 = 1 := (planeLeviHom Adeles).map_one
  rw [levi_one, one_mul]

theorem inducedCuspVector_realOrbit_smooth
    {degree : ℕ} {inducingData : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue) (matrix : AdelicGL) :
    Smooth (fun realElements : Fin 1 → RealGL3 =>
      (inducedCuspVector induced (matrix * atInfinity (realElements 0))).val) := by
  obtain ⟨vectors, smooth, realized⟩ := induced.2.2.1 matrix
  have vector_eq (realElements : Fin 1 → RealGL3) :
      inducedCuspVector induced (matrix * atInfinity (realElements 0)) = vectors realElements := by
    apply inducingData.cusp.injective
    funext binary
    rw [inducedCuspVector_realize]
    exact (realized realElements binary).symm
  simpa only [vector_eq] using smooth

theorem inducedCuspVector_finite_level
    {degree : ℕ} {inducingData : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (matrix : AdelicGL) (level : finiteLevel) :
    inducedCuspVector induced (matrix * atFinite level.val) = inducedCuspVector induced matrix := by
  apply inducingData.cusp.injective
  funext binary
  rw [inducedCuspVector_realize, inducedCuspVector_realize, ← mul_assoc, induced.2.1 level]

theorem inducedCuspVector_continuous
    {degree : ℕ} {inducingData : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue) :
    Continuous (fun matrix => (inducedCuspVector induced matrix).val) := by
  apply continuous_iff_continuousAt.mpr
  intro base
  have real_continuous : Continuous (fun realElements : Fin 1 → RealGL3 =>
      (inducedCuspVector induced (base * atInfinity (realElements 0))).val) :=
    smooth_continuous (E := inducingData.cusp.H)
      (function := fun realElements : Fin 1 → RealGL3 =>
        (inducedCuspVector induced (base * atInfinity (realElements 0))).val)
      (inducedCuspVector_realOrbit_smooth induced base)
  have correction_continuous : Continuous (fun target : AdelicGL =>
      fun _ : Fin 1 => (realGroup base)⁻¹ * realGroup target) :=
    continuous_pi (fun _ => continuous_const.mul realGroup_continuous)
  have model_continuous := real_continuous.comp correction_continuous
  dsimp only [Function.comp_def] at model_continuous
  apply model_continuous.continuousAt.congr_of_eventuallyEq
  have near : ∀ᶠ target : AdelicGL in nhds base,
      (finiteGroup base)⁻¹ * finiteGroup target ∈ finiteLevel :=
    (finiteLevel_isOpen.preimage (continuous_const.mul finiteGroup_continuous)).eventually_mem (by simp)
  filter_upwards [near] with target finite_in_level
  congr 1
  calc
    inducedCuspVector induced target = inducedCuspVector induced
      ((base * atInfinity ((realGroup base)⁻¹ * realGroup target)) *
        atFinite ((finiteGroup base)⁻¹ * finiteGroup target)) :=
      congrArg (inducedCuspVector induced) (adelicGroup_correction base target).symm
    _ = _ := inducedCuspVector_finite_level induced _ ⟨_, finite_in_level⟩

theorem inducedCuspVector_flat_compact
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (matrix : AdelicGL)
    (compact : inMaximalCompact matrix) :
    inducedCuspVector (flat.1 parameter) matrix = inducedCuspVector (flat.1 cohomologicalPoint) matrix := by
  apply inducingData.cusp.injective
  funext binary
  rw [inducedCuspVector_realize, inducedCuspVector_realize]
  exact flat.2.2 parameter binary matrix compact

theorem inducedCuspVector_compact_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter matrix, inMaximalCompact matrix →
      ‖(inducedCuspVector (flat.1 parameter) matrix).val‖ ≤ bound := by
  obtain ⟨bound, bounded⟩ := maximalCompact_isCompact.exists_bound_of_continuousOn
    (inducedCuspVector_continuous (flat.1 cohomologicalPoint)).continuousOn
  refine ⟨max 0 bound, le_max_left _ _, ?_⟩
  intro parameter matrix compact
  rw [inducedCuspVector_flat_compact flat parameter matrix compact]
  exact (bounded matrix compact).trans (le_max_right _ _)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
