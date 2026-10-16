module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Hilbert
public import TernaryPeriodPolynomials.Building.PlaneFlatExtensions.Construction
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Height

@[expose] public section


/-!
# Majorant of the local standard integrand

For `y = n · planeLevi(B, t) · k` with `k` in the maximal compact subgroup, the corner `|t|` is the
product of the Euclidean norm of the real bottom row of `y` and the mass of the finite row lattice of
`y`. For the local standard argument `w⁻¹ n(u) κ x` this is comparable to the local height
`√(1 + u₁² + u₂²) · max(1, |u₁|₃, |u₂|₃)`, which gives the norm majorant of the local integrand.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.PlaneFlatExtensions.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- The bottom row of a plane parabolic element times `k` is the corner times the bottom row of
`k`. -/
theorem planeParabolic_mul_row (first second : Adeles) (binary : BinaryAdelicGL)
    (unit : Adelesˣ) (other : AdelicGL) (column : Fin 3) :
    (planeUnipotent first second * planeLevi binary unit * other).val 2 column =
      unit.val * other.val 2 column := by
  simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

/-- The corner of a plane decomposition is the product of the real row norm and the finite row
mass. -/
theorem corner_eq_row (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ)
    (other : AdelicGL) (compactness : inMaximalCompact other) :
    (adeleNorm unit : ℝ) =
      Real.sqrt (rowSquare (realGroup (planeUnipotent first second * planeLevi binary unit * other))) *
        rowMass (finiteGroup (planeUnipotent first second * planeLevi binary unit * other)) := by
  set parabolic := planeUnipotent first second * planeLevi binary unit with parabolicDef
  have left := height_left parabolic other unit (by
    intro column
    exact planeParabolic_mul_row first second binary unit other column)
  rw [height_compact other compactness, add_zero] at left
  have determinant : (adeleNorm (Matrix.GeneralLinearGroup.det (parabolic * other)) : ℝ) =
      adeleNorm (Matrix.GeneralLinearGroup.det parabolic) := by
    rw [map_mul, map_mul, NNReal.coe_mul,
      PlaneEisensteinContinuation.Height.adeleNorm_det_maximalCompact other compactness, mul_one]
  unfold heightValue at left
  rw [determinant] at left
  have squarePositive := rowSquare_pos (realGroup (parabolic * other))
  have massPositive := rowMass_pos (finiteGroup (parabolic * other))
  have unitPositive : (0 : ℝ) < adeleNorm unit := PlaneFlatExtensions.Helpers.adeleNorm_pos unit
  have logarithm : Real.log (adeleNorm unit : ℝ) =
      Real.log (Real.sqrt (rowSquare (realGroup (parabolic * other))) *
        rowMass (finiteGroup (parabolic * other))) := by
    rw [Real.log_mul (Real.sqrt_pos.mpr squarePositive).ne' massPositive.ne', Real.log_sqrt
      squarePositive.le]
    linarith
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr unitPositive)
    (Set.mem_Ioi.mpr (mul_pos (Real.sqrt_pos.mpr squarePositive) massPositive)) logarithm

/-- Multiplication by an adele concentrated at `3`. -/
theorem finiteAtThreeScalar_mul_left (value : ℚ_[3]) (other : FiniteAdeles) :
    finiteAtThreeScalar value * other = finiteAtThreeScalar (value * finiteThree other) := by
  apply finiteAdeles_eq_of_three_and_away
  · rw [map_mul, finiteAtThreeScalar_three, finiteAtThreeScalar_three]
  · intro place away
    rw [map_mul, finiteAtThreeScalar_away _ _ away, finiteAtThreeScalar_away _ _ away, zero_mul]

/-- The embedding concentrated at `3` is additive. -/
theorem finiteAtThreeScalar_add' (first second : ℚ_[3]) :
    finiteAtThreeScalar (first + second) =
      finiteAtThreeScalar first + finiteAtThreeScalar second := by
  apply finiteAdeles_eq_of_three_and_away
  · rw [map_add, finiteAtThreeScalar_three, finiteAtThreeScalar_three, finiteAtThreeScalar_three]
  · intro place away
    rw [map_add, finiteAtThreeScalar_away _ _ away, finiteAtThreeScalar_away _ _ away,
      finiteAtThreeScalar_away _ _ away, add_zero]

/-- The bottom row of the finite local standard argument. -/
theorem localFiniteArgument_row (first second : FiniteAdeles) (column : Fin 3) :
    ((weyl⁻¹ : FiniteGL) * lineUnipotent first second).val 2 column =
      ![1, first, second] column := by
  fin_cases column <;>
    simp [weyl, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

/-- An element of `ℚ₃` of norm at most one gives an integral finite adele. -/
theorem finiteAtThreeScalar_integral_of_norm (value : ℚ_[3]) (small : ‖value‖ ≤ 1) :
    finiteAtThreeScalar value ∈ Set.range integralEmbedding :=
  finiteAtThreeScalar_integral (⟨value, small⟩ : ℤ_[3])

/-- The `3`-component of an integral finite adele has norm at most one. -/
theorem finiteThree_norm_le_of_integral (value : FiniteAdeles)
    (integral : value ∈ Set.range integralEmbedding) : ‖finiteThree value‖ ≤ 1 := by
  obtain ⟨integer, rfl⟩ := integral
  rw [finiteThree_integral]
  exact (integralThree integer).property

/-- The row lattice of the finite local standard argument, in the splitting `ℚ₃ × 𝔸_f^{(3)}`. -/
theorem localRowLattice (first second : ℚ_[3]) :
    finiteThreeSplit.symm ⁻¹'
        rowLattice ((weyl⁻¹ : FiniteGL) *
          lineUnipotent (finiteAtThreeScalar first) (finiteAtThreeScalar second)) =
      {value : ℚ_[3] | ‖value‖ ≤ max 1 (max ‖first‖ ‖second‖)} ×ˢ
        (Subtype.val ⁻¹' Set.range integralEmbedding) := by
  ext pair
  rw [Set.mem_preimage, rowLattice_mem, finiteThreeSplit_symm]
  simp only [localFiniteArgument_row, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul,
    Set.mem_prod, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨vector, integralVector, equality⟩
    have vectorIntegral (index : Fin 3) : vector index ∈ Set.range integralEmbedding := by
      have := integralVector index (Set.mem_univ _)
      exact this
    have three := congrArg finiteThree equality
    rw [map_add, map_add, map_add, map_mul, map_mul, finiteAtThreeScalar_three,
      finiteAtThreeScalar_three, finiteAtThreeScalar_three,
      (show finiteThree pair.2.val = 0 from pair.2.property), add_zero] at three
    constructor
    · rw [← three]
      have zeroBound := finiteThree_norm_le_of_integral _ (vectorIntegral 0)
      have oneBound := finiteThree_norm_le_of_integral _ (vectorIntegral 1)
      have twoBound := finiteThree_norm_le_of_integral _ (vectorIntegral 2)
      refine (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans
        (max_le ?_ ?_)) ?_)
      · exact zeroBound.trans (le_max_left _ _)
      · rw [norm_mul]
        calc ‖first‖ * ‖finiteThree (vector 1)‖ ≤ ‖first‖ * 1 :=
              mul_le_mul_of_nonneg_left oneBound (norm_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact (le_max_left _ _).trans (le_max_right _ _)
      · rw [norm_mul]
        calc ‖second‖ * ‖finiteThree (vector 2)‖ ≤ ‖second‖ * 1 :=
              mul_le_mul_of_nonneg_left twoBound (norm_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact (le_max_right _ _).trans (le_max_right _ _)
    · have away : pair.2.val = vector 0 - finiteAtThreeScalar (finiteThree (vector 0)) := by
        rw [finiteAtThreeScalar_mul_left, finiteAtThreeScalar_mul_left] at equality
        have expand : finiteAtThreeScalar pair.1 = finiteAtThreeScalar (finiteThree (vector 0)) +
            finiteAtThreeScalar (first * finiteThree (vector 1)) +
              finiteAtThreeScalar (second * finiteThree (vector 2)) := by
          rw [← three, finiteAtThreeScalar_add', finiteAtThreeScalar_add']
        rw [expand] at equality
        linear_combination -equality
      rw [away]
      exact (integralEmbedding.range).sub_mem (vectorIntegral 0)
        (finiteAtThreeScalar_integral_of_norm _ (finiteThree_norm_le_of_integral _
          (vectorIntegral 0)))
  · rintro ⟨bound, awayIntegral⟩
    by_cases small : ‖pair.1‖ ≤ 1
    · refine ⟨![finiteAtThreeScalar pair.1 + pair.2.val, 0, 0], ?_, by simp⟩
      intro index _
      fin_cases index
      · exact (integralEmbedding.range).add_mem
          (finiteAtThreeScalar_integral_of_norm _ small) awayIntegral
      · exact ⟨0, map_zero _⟩
      · exact ⟨0, map_zero _⟩
    · have large : 1 < max 1 (max ‖first‖ ‖second‖) :=
        lt_of_lt_of_le (lt_of_not_ge small) bound
      by_cases order : ‖second‖ ≤ ‖first‖
      · have maximum : max 1 (max ‖first‖ ‖second‖) = ‖first‖ := by
          rw [max_eq_left order]
          exact max_eq_right (le_of_lt (by
            rw [max_eq_left order] at large
            exact (lt_max_iff.mp large).resolve_left (lt_irrefl 1)))
        have nonzero : first ≠ 0 := by
          intro zero
          rw [maximum, zero, norm_zero] at large
          exact absurd large (by norm_num)
        refine ⟨![pair.2.val, finiteAtThreeScalar (pair.1 / first), 0], ?_, ?_⟩
        · intro index _
          fin_cases index
          · exact awayIntegral
          · apply finiteAtThreeScalar_integral_of_norm
            rw [norm_div, div_le_one (norm_pos_iff.mpr nonzero)]
            exact maximum ▸ bound
          · exact ⟨0, map_zero _⟩
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons, mul_zero, add_zero]
          rw [finiteAtThreeScalar_mul_left, finiteAtThreeScalar_three, mul_div_cancel₀ _ nonzero]
          ring
      · have reverse : ‖first‖ ≤ ‖second‖ := le_of_lt (lt_of_not_ge order)
        have maximum : max 1 (max ‖first‖ ‖second‖) = ‖second‖ := by
          rw [max_eq_right reverse]
          exact max_eq_right (le_of_lt (by
            rw [max_eq_right reverse] at large
            exact (lt_max_iff.mp large).resolve_left (lt_irrefl 1)))
        have nonzero : second ≠ 0 := by
          intro zero
          rw [maximum, zero, norm_zero] at large
          exact absurd large (by norm_num)
        refine ⟨![pair.2.val, 0, finiteAtThreeScalar (pair.1 / second)], ?_, ?_⟩
        · intro index _
          fin_cases index
          · exact awayIntegral
          · exact ⟨0, map_zero _⟩
          · apply finiteAtThreeScalar_integral_of_norm
            rw [norm_div, div_le_one (norm_pos_iff.mpr nonzero)]
            exact maximum ▸ bound
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons, mul_zero, add_zero]
          rw [finiteAtThreeScalar_mul_left, finiteAtThreeScalar_three, mul_div_cancel₀ _ nonzero]
          ring

end TernaryPeriodPolynomials.EdgeConvergence
