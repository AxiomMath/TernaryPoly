module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Finite.LevelTopology

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem invertibleMatrix_val {size : ℕ} (matrix : GeneralLinearGroup (Fin size) ℝ) :
    invertibleMatrix matrix.val = matrix := by
  rw [invertibleMatrix, dite_eq_left matrix.det_ne_zero]
  apply Units.ext
  rfl

theorem smooth_continuous {size arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E}
    (smooth : Smooth function) : Continuous function := by
  have continuous_matrices : Continuous
      (fun matrices : Fin arity → GeneralLinearGroup (Fin size) ℝ => fun index => (matrices index).val) :=
    continuous_pi (fun index => Units.continuous_val.comp (continuous_apply index))
  have composed := smooth.continuousOn.comp_continuous continuous_matrices
    (fun matrices index => (matrices index).det_ne_zero)
  simpa only [Function.comp_def, invertibleMatrix_val] using composed

theorem realGroup_continuous : Continuous realGroup :=
  generalLinearGroup_map_continuous (RingHom.fst ℝ FiniteAdeles) continuous_fst 3

theorem finiteGroup_continuous : Continuous finiteGroup :=
  generalLinearGroup_map_continuous (RingHom.snd ℝ FiniteAdeles) continuous_snd 3

theorem realGroup_atInfinity (matrix : RealGL3) : realGroup (atInfinity matrix) = matrix := by
  apply Units.ext
  rfl

theorem finiteGroup_atInfinity (matrix : RealGL3) : finiteGroup (atInfinity matrix) = 1 := by
  apply Units.ext
  rfl

theorem adelicGroup_eq_of_components {first second : AdelicGL}
    (real_equal : realGroup first = realGroup second)
    (finite_equal : finiteGroup first = finiteGroup second) : first = second := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · exact congrArg (fun matrix : RealGL3 => matrix.val row column) real_equal
  · exact congrArg (fun matrix : FiniteGL => matrix.val row column) finite_equal

theorem adelicGroup_correction (base target : AdelicGL) :
    (base * atInfinity ((realGroup base)⁻¹ * realGroup target)) *
      atFinite ((finiteGroup base)⁻¹ * finiteGroup target) = target := by
  apply adelicGroup_eq_of_components
  · simp only [map_mul, realGroup_atInfinity, realGroup_atFinite, mul_one, mul_inv_cancel_left]
  · simp only [map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, mul_one, mul_inv_cancel_left]

theorem induced_continuous
    {degree : ℕ} {inducingData : InducingData degree} {side : Side}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData side parameter sectionValue) : Continuous sectionValue := by
  apply continuous_iff_continuousAt.mpr
  intro base
  have model_continuous : Continuous (fun target : AdelicGL =>
      sectionValue (base * atInfinity ((realGroup base)⁻¹ * realGroup target))) :=
    (smooth_continuous (induced.1 base)).comp
      (continuous_pi (fun _ : Fin 1 => continuous_const.mul realGroup_continuous))
  apply model_continuous.continuousAt.congr_of_eventuallyEq
  have near : ∀ᶠ target : AdelicGL in nhds base,
      (finiteGroup base)⁻¹ * finiteGroup target ∈ finiteLevel :=
    (finiteLevel_isOpen.preimage (continuous_const.mul finiteGroup_continuous)).eventually_mem
      (by simp)
  filter_upwards [near] with target finite_in_level
  calc
    sectionValue target = sectionValue ((base * atInfinity ((realGroup base)⁻¹ * realGroup target)) *
        atFinite ((finiteGroup base)⁻¹ * finiteGroup target)) :=
      congrArg sectionValue (adelicGroup_correction base target).symm
    _ = _ := induced.2.1 ⟨_, finite_in_level⟩ _

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
