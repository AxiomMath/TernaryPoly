module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.RowMass
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Integrability

@[expose] public section


/-!
# The corner of the local standard argument

For `y = w⁻¹ n(a, b) g` the bottom row of `y` is `g₀ + a g₁ + b g₂`, the row vector `(1, a, b)` times
`g`. At the real place the squared norm of this row is bounded below by `(1 + a² + b²)` divided by a
constant depending only on `g`, and at the finite places the row lattice only depends on `g` through
its integrality, so the corner `|t|` of a plane decomposition of `y` is bounded below by a constant
times the local height.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.PlaneFlatExtensions.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- The bottom row of the Weyl-translated line radical element. -/
theorem weylLine_row {R : Type*} [CommRing R] (first second : R) (column : Fin 3) :
    ((weyl⁻¹ : GL3 R) * lineUnipotent first second).val 2 column = ![1, first, second] column := by
  fin_cases column <;>
    simp [weyl, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

/-- The bottom row of the standard argument. -/
theorem standardArgument_row {R : Type*} [CommRing R] (first second : R) (other : GL3 R)
    (column : Fin 3) :
    ((weyl⁻¹ : GL3 R) * lineUnipotent first second * other).val 2 column =
      other.val 0 column + first * other.val 1 column + second * other.val 2 column := by
  rw [Units.val_mul, Matrix.mul_apply]
  simp only [weylLine_row, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul]

/-- A vector is controlled by its image under an invertible real matrix. -/
theorem sum_sq_le_row_sum_sq (matrix : GL3 ℝ) (vector : Fin 3 → ℝ) :
    ∑ index, vector index ^ 2 ≤
      (∑ index, ∑ column, (matrix.inv column index) ^ 2) *
        ∑ column, (∑ row, vector row * matrix.val row column) ^ 2 := by
  have recover (index : Fin 3) : vector index =
      ∑ column, (∑ row, vector row * matrix.val row column) * matrix.inv column index := by
    have identity (row : Fin 3) : ∑ column, matrix.val row column * matrix.inv column index =
        if row = index then 1 else 0 := by
      have := congrArg (fun m : Matrix (Fin 3) (Fin 3) ℝ => m row index) matrix.val_inv
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    calc vector index = ∑ row, vector row * (if row = index then (1 : ℝ) else 0) := by simp
      _ = ∑ row, vector row * ∑ column, matrix.val row column * matrix.inv column index := by
        refine Finset.sum_congr rfl fun row _ => ?_
        rw [identity row]
      _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun row _ => Finset.sum_congr rfl fun column _ => by ring
  calc ∑ index, vector index ^ 2
      = ∑ index, (∑ column, (∑ row, vector row * matrix.val row column) *
          matrix.inv column index) ^ 2 := by
        refine Finset.sum_congr rfl fun index _ => ?_
        rw [← recover index]
    _ ≤ ∑ index, (∑ column, (∑ row, vector row * matrix.val row column) ^ 2) *
          ∑ column, (matrix.inv column index) ^ 2 :=
        Finset.sum_le_sum fun index _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := by
        rw [← Finset.mul_sum, mul_comm]

/-- The bottom row of the real part of the standard argument. -/
theorem realRow_standardArgument (first second : Adeles) (other : AdelicGL) (column : Fin 3) :
    (realGroup (weyl⁻¹ * lineUnipotent first second * other)).val 2 column =
      ∑ row, ![1, first.1, second.1] row * (realGroup other).val row column := by
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, one_mul]
  exact congrArg Prod.fst (standardArgument_row first second other column)

/-- The bottom row of the finite part of the standard argument. -/
theorem finiteRow_standardArgument (first second : Adeles) (other : AdelicGL) :
    (finiteGroup (weyl⁻¹ * lineUnipotent first second * other)).val 2 =
      ((weyl⁻¹ : FiniteGL) * lineUnipotent first.2 second.2 * finiteGroup other).val 2 := by
  funext column
  rw [standardArgument_row]
  exact congrArg Prod.snd (standardArgument_row first second other column)

/-- The finite row mass of the standard argument depends only on the `3`-adic coordinates when the
argument is integral at the finite places. -/
theorem rowMass_standardArgument (first second : Adeles) (other : AdelicGL)
    (integral : Matrix.GeneralLinearGroup (Fin 3) IntegralAdeles)
    (finite : finiteGroup other = Matrix.GeneralLinearGroup.map integralEmbedding integral) :
    rowMass (finiteGroup (weyl⁻¹ * lineUnipotent first second * other)) =
      rowMass ((weyl⁻¹ : FiniteGL) * lineUnipotent first.2 second.2) := by
  rw [rowMass, rowLattice_of_row_eq _ _ (finiteRow_standardArgument first second other), finite,
    ← rowMass, rowMass_right_integral]

/-- The corner of a plane decomposition of the local standard argument is bounded below by a
constant times the local height. -/
theorem corner_lower_bound (argument : AdelicGL)
    (integral : Matrix.GeneralLinearGroup (Fin 3) IntegralAdeles)
    (finite : finiteGroup argument = Matrix.GeneralLinearGroup.map integralEmbedding integral)
    (discriminant : ℝ)
    (discriminantBound : ∑ index, ∑ column, ((realGroup argument).inv column index) ^ 2 ≤
      discriminant) :
    ∀ (coordinates : LocalLine × LocalLine) (first second : Adeles)
      (binary : BinaryAdelicGL) (unit : Adelesˣ) (other : AdelicGL), inMaximalCompact other →
      weyl⁻¹ * localRadical coordinates * argument =
        planeUnipotent first second * planeLevi binary unit * other →
      (3 * Real.sqrt (discriminant + 1))⁻¹ * localHeight coordinates ≤ (adeleNorm unit : ℝ) := by
  set real := realGroup argument with realDef
  have discriminantNonneg : 0 ≤ ∑ index, ∑ column, (real.inv column index) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have rootPositive : 0 < Real.sqrt (discriminant + 1) := Real.sqrt_pos.mpr (by linarith)
  intro coordinates first second binary unit other compactness decomposition
  have corner := corner_eq_row first second binary unit other compactness
  rw [← decomposition] at corner
  rw [corner]
  have definition : weyl⁻¹ * localRadical coordinates * argument =
      weyl⁻¹ * lineUnipotent (localAdele coordinates.1) (localAdele coordinates.2) * argument :=
    rfl
  rw [definition]
  have rowEquality : rowSquare (realGroup (weyl⁻¹ * lineUnipotent (localAdele coordinates.1)
        (localAdele coordinates.2) * argument)) =
      ∑ column, (∑ row, ![1, coordinates.1.1, coordinates.2.1] row *
        real.val row column) ^ 2 := by
    unfold rowSquare
    exact Finset.sum_congr rfl fun column _ =>
      congrArg (· ^ 2) (realRow_standardArgument _ _ _ column)
  have squareNonneg : 0 ≤ ∑ column, (∑ row, ![1, coordinates.1.1, coordinates.2.1] row *
      real.val row column) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have realBound : 1 + coordinates.1.1 ^ 2 + coordinates.2.1 ^ 2 ≤
      rowSquare (realGroup (weyl⁻¹ * lineUnipotent (localAdele coordinates.1)
        (localAdele coordinates.2) * argument)) * (discriminant + 1) := by
    have control := sum_sq_le_row_sum_sq real ![1, coordinates.1.1, coordinates.2.1]
    have scaled := mul_le_mul_of_nonneg_right discriminantBound squareNonneg
    have vectorSquare : ∑ index, (![1, coordinates.1.1, coordinates.2.1] : Fin 3 → ℝ) index ^ 2 =
        1 + coordinates.1.1 ^ 2 + coordinates.2.1 ^ 2 := by
      simp [Fin.sum_univ_three]
    rw [vectorSquare] at control
    rw [rowEquality]
    nlinarith [control, squareNonneg, scaled]
  have finiteBound : max 1 (max ‖coordinates.1.2‖ ‖coordinates.2.2‖) / 3 ≤
      rowMass (finiteGroup (weyl⁻¹ * lineUnipotent (localAdele coordinates.1)
        (localAdele coordinates.2) * argument)) := by
    rw [rowMass_standardArgument _ _ argument integral finite]
    exact rowMass_local_ge coordinates.1.2 coordinates.2.2
  have rootBound : Real.sqrt (1 + coordinates.1.1 ^ 2 + coordinates.2.1 ^ 2) ≤
      Real.sqrt (rowSquare (realGroup (weyl⁻¹ * lineUnipotent (localAdele coordinates.1)
        (localAdele coordinates.2) * argument))) * Real.sqrt (discriminant + 1) := by
    have rowSquareNonneg : 0 ≤ rowSquare (realGroup (weyl⁻¹ * lineUnipotent (localAdele coordinates.1)
        (localAdele coordinates.2) * argument)) := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [← Real.sqrt_mul rowSquareNonneg]
    exact Real.sqrt_le_sqrt realBound
  have heightLarge : 1 ≤ max 1 (max ‖coordinates.1.2‖ ‖coordinates.2.2‖) := le_max_left _ _
  have rootNonneg : 0 ≤ Real.sqrt (rowSquare (realGroup (weyl⁻¹ * lineUnipotent
      (localAdele coordinates.1) (localAdele coordinates.2) * argument))) := Real.sqrt_nonneg _
  unfold localHeight
  calc (3 * Real.sqrt (discriminant + 1))⁻¹ *
        (Real.sqrt (1 + coordinates.1.1 ^ 2 + coordinates.2.1 ^ 2) *
          max 1 (max ‖coordinates.1.2‖ ‖coordinates.2.2‖))
      ≤ (3 * Real.sqrt (discriminant + 1))⁻¹ *
        (Real.sqrt (rowSquare (realGroup (weyl⁻¹ * lineUnipotent (localAdele coordinates.1)
            (localAdele coordinates.2) * argument))) * Real.sqrt (discriminant + 1) *
          max 1 (max ‖coordinates.1.2‖ ‖coordinates.2.2‖)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right rootBound
          (by linarith [heightLarge])) (inv_nonneg.mpr (mul_pos three_pos rootPositive).le)
    _ = Real.sqrt (rowSquare (realGroup (weyl⁻¹ * lineUnipotent (localAdele coordinates.1)
            (localAdele coordinates.2) * argument))) *
          (max 1 (max ‖coordinates.1.2‖ ‖coordinates.2.2‖) / 3) := by
        have rootNe := rootPositive.ne'
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left finiteBound rootNonneg

end TernaryPeriodPolynomials.EdgeConvergence
