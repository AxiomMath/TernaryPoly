module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionContinuity
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem adelic_matrix_eq_of_projections {size : ℕ}
    {first second : GeneralLinearGroup (Fin size) Adeles}
    (real_equal : GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) first =
      GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) second)
    (finite_equal : GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) first =
      GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) second) : first = second := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · exact congrArg (fun matrix : GeneralLinearGroup (Fin size) ℝ => matrix.val row column) real_equal
  · exact congrArg (fun matrix : GeneralLinearGroup (Fin size) FiniteAdeles => matrix.val row column) finite_equal

theorem adelic_matrix_correction {size : ℕ}
    (base target : GeneralLinearGroup (Fin size) Adeles) :
    (base * atInfinity
      ((GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) base)⁻¹ *
        GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) target)) *
      atFinite ((GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) base)⁻¹ *
        GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) target) = target := by
  have real_infinity (matrix : GeneralLinearGroup (Fin size) ℝ) :
      GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) (atInfinity matrix) = matrix := by
    apply Units.ext
    rfl
  have real_finite (matrix : GeneralLinearGroup (Fin size) FiniteAdeles) :
      GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) (atFinite matrix) = 1 := by
    apply Units.ext
    rfl
  have finite_infinity (matrix : GeneralLinearGroup (Fin size) ℝ) :
      GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (atInfinity matrix) = 1 := by
    apply Units.ext
    rfl
  have finite_finite (matrix : GeneralLinearGroup (Fin size) FiniteAdeles) :
      GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (atFinite matrix) = matrix := by
    apply Units.ext
    rfl
  apply adelic_matrix_eq_of_projections
  · simp only [map_mul, real_infinity, real_finite, mul_one, mul_inv_cancel_left]
  · simp only [map_mul, finite_infinity, finite_finite, mul_one, mul_inv_cancel_left]

theorem adelic_function_continuous_of_smooth_finite_invariant
    {size : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {function : GeneralLinearGroup (Fin size) Adeles → E}
    (smooth : ∀ base, Smooth (fun realElements : Fin 1 → GeneralLinearGroup (Fin size) ℝ =>
      function (base * atInfinity (realElements 0))))
    (level : Subgroup (GeneralLinearGroup (Fin size) FiniteAdeles))
    (level_open : IsOpen (level : Set (GeneralLinearGroup (Fin size) FiniteAdeles)))
    (invariant : ∀ element : level, ∀ base, function (base * atFinite element.val) = function base) :
    Continuous function := by
  have real_continuous := generalLinearGroup_map_continuous (RingHom.fst ℝ FiniteAdeles) continuous_fst size
  have finite_continuous := generalLinearGroup_map_continuous (RingHom.snd ℝ FiniteAdeles) continuous_snd size
  apply continuous_iff_continuousAt.mpr
  intro base
  have model_continuous : Continuous (fun target : GeneralLinearGroup (Fin size) Adeles =>
      function (base * atInfinity
        ((GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) base)⁻¹ *
          GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) target))) :=
    (smooth_continuous (smooth base)).comp
      (continuous_pi (fun _ : Fin 1 => continuous_const.mul real_continuous))
  apply model_continuous.continuousAt.congr_of_eventuallyEq
  have near : ∀ᶠ target : GeneralLinearGroup (Fin size) Adeles in nhds base,
      (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) base)⁻¹ *
        GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) target ∈ level :=
    (level_open.preimage (continuous_const.mul finite_continuous)).eventually_mem (by simp)
  filter_upwards [near] with target finite_in_level
  calc
    function target = function ((base * atInfinity
      ((GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) base)⁻¹ *
        GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) target)) *
      atFinite ((GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) base)⁻¹ *
        GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) target)) :=
      congrArg function (adelic_matrix_correction base target).symm
    _ = _ := invariant ⟨_, finite_in_level⟩ _

theorem cusp_realize_finite_invariant (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
      IsCompact (level : Set BinaryFiniteGL) ∧
      ∀ element : level, ∀ base, cusp.realize vector (base * atFinite element.val) =
        cusp.realize vector base := by
  obtain ⟨level, level_open, level_compact, fixed⟩ :=
    ((cusp.smooth_exact vector.val).mp vector.property).2
  refine ⟨level, level_open, level_compact, ?_⟩
  intro element base
  rw [← cusp.equivariant]
  apply congrArg (fun other : cusp.smooth => cusp.realize other base)
  exact Subtype.ext (fixed element)

theorem cusp_realize_continuous (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    Continuous (cusp.realize vector) := by
  obtain ⟨level, level_open, _, invariant⟩ := cusp_realize_finite_invariant cusp vector
  exact adelic_function_continuous_of_smooth_finite_invariant
    (cusp.scalarSmooth vector) level level_open invariant

noncomputable def cuspBoundedRealization (cusp : CuspidalRepresentation) :
    cusp.smooth →ₗ[ℂ] BoundedContinuousFunction BinaryAdelicGL ℂ where
  toFun vector :=
    { toContinuousMap := ⟨cusp.realize vector, cusp_realize_continuous cusp vector⟩
      map_bounded' := by
        obtain ⟨bound, bounded⟩ := cusp.bounded vector
        refine ⟨2 * bound, ?_⟩
        intro first second
        rw [dist_eq_norm]
        exact (norm_sub_le _ _).trans (by linarith [bounded first, bounded second]) }
  map_add' first second := by
    ext argument
    change cusp.realize (first + second) argument = cusp.realize first argument + cusp.realize second argument
    simp only [map_add, Pi.add_apply]
  map_smul' scalar vector := by
    ext argument
    change cusp.realize (scalar • vector) argument = scalar • cusp.realize vector argument
    simp only [map_smul, Pi.smul_apply]

theorem cuspBoundedRealization_apply (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) : cuspBoundedRealization cusp vector argument = cusp.realize vector argument := rfl

theorem cuspBoundedRealization_injective (cusp : CuspidalRepresentation) :
    Function.Injective (cuspBoundedRealization cusp) := by
  intro first second equality
  apply cusp.injective
  funext argument
  exact congrArg (fun function : BoundedContinuousFunction BinaryAdelicGL ℂ => function argument) equality

theorem cusp_realize_norm_le (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) :
    ‖cusp.realize vector argument‖ ≤ ‖cuspBoundedRealization cusp vector‖ :=
  BoundedContinuousFunction.norm_coe_le_norm (cuspBoundedRealization cusp vector) argument

theorem cuspBoundedRealization_translate_norm (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) (matrix : BinaryAdelicGL) :
    ‖cuspBoundedRealization cusp
      ⟨cusp.π matrix vector.val, cusp.smooth_stable matrix vector.val vector.property⟩‖ =
      ‖cuspBoundedRealization cusp vector‖ := by
  apply le_antisymm
  · apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
    intro argument
    rw [cuspBoundedRealization_apply, cusp.equivariant]
    exact cusp_realize_norm_le cusp vector (argument * matrix)
  · apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
    intro argument
    have bounded := cusp_realize_norm_le cusp
      ⟨cusp.π matrix vector.val, cusp.smooth_stable matrix vector.val vector.property⟩ (argument * matrix⁻¹)
    rw [cusp.equivariant, inv_mul_cancel_right] at bounded
    exact bounded

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
