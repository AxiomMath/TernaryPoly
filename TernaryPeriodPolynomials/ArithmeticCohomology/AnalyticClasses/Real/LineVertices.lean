module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineRealLeviMeasure
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismTranslation

@[expose] public section


/-!
# Real Levi and radical elements of the good-line stabilizer

The good-line argument `g(u) = standardGoodLineRealArgument u` intertwines the real points of the
good-line stabilizer — the opposite plane parabolic, with Levi `planeLevi m 1` and radical
`lowerPlaneUnipotent a b` — with an explicit action on `u ∈ ℝ²`:

* `g(u) · planeLevi m 1 = planeLevi (σ m σ) 1 · g(u ∗ m)` with `u ∗ m` linear in `u`
  (`σ = binaryPivotSwap`), measure preserving when `|det m| = 1`;
* `g(u) · lowerPlaneUnipotent a b = g(u + (b, a))`.

These are the real versions of `standardGoodLineRealArgument_levi` and
`standardGoodLineRealArgument_radical`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The real Levi action on the good-line coordinate. -/
def realLeviInput (m : BinaryRealGL) (u : ℝ × ℝ) : ℝ × ℝ :=
  (u.2 * m.val 0 1 + u.1 * m.val 1 1, u.2 * m.val 0 0 + u.1 * m.val 1 0)

/-- Conjugation of a binary matrix by the pivot swap. -/
def pivotConjugate (m : BinaryRealGL) : BinaryRealGL := binaryPivotSwap * m * binaryPivotSwap

/-- The real radical shift of the good-line coordinate. -/
def realRadicalShift (Y : ℝ × ℝ) (u : ℝ × ℝ) : ℝ × ℝ := (u.1 + Y.2, u.2 + Y.1)

theorem standardGoodLineRealArgument_realLevi (u : ℝ × ℝ) (m : BinaryRealGL) :
    standardGoodLineRealArgument u * planeLevi m 1 =
      planeLevi (pivotConjugate m) 1 * standardGoodLineRealArgument (realLeviInput m u) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, standardGoodLineRealArgument_val,
    standardGoodLineRealArgument_val]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, pivotConjugate, binaryPivotSwap, realLeviInput, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem standardGoodLineRealArgument_lowerUnipotent (u : ℝ × ℝ) (Y : ℝ × ℝ) :
    standardGoodLineRealArgument u * lowerPlaneUnipotent Y.1 Y.2 =
      standardGoodLineRealArgument (realRadicalShift Y u) := by
  apply Units.ext
  rw [Units.val_mul, standardGoodLineRealArgument_val, standardGoodLineRealArgument_val]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [lowerPlaneUnipotent, realRadicalShift, Matrix.mul_apply, Fin.sum_univ_three]

theorem realLeviInput_mul (m m' : BinaryRealGL) (u : ℝ × ℝ) :
    realLeviInput m' (realLeviInput m u) = realLeviInput (m * m') u := by
  ext <;> simp [realLeviInput, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem realLeviInput_one (u : ℝ × ℝ) : realLeviInput 1 u = u := by
  ext <;> simp [realLeviInput]

theorem realLeviInput_shift (m : BinaryRealGL) (Y u : ℝ × ℝ) :
    realLeviInput m (realRadicalShift Y u) =
      realRadicalShift (Y.1 * m.val 0 0 + Y.2 * m.val 1 0, Y.1 * m.val 0 1 + Y.2 * m.val 1 1)
        (realLeviInput m u) := by
  ext <;> simp [realLeviInput, realRadicalShift] <;> ring

/-- The real Levi action as a linear equivalence. -/
def realLeviEquiv (m : BinaryRealGL) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun := realLeviInput m
  invFun := realLeviInput m⁻¹
  left_inv u := by rw [realLeviInput_mul, mul_inv_cancel, realLeviInput_one]
  right_inv u := by rw [realLeviInput_mul, inv_mul_cancel, realLeviInput_one]
  map_add' first second := by ext <;> simp [realLeviInput] <;> ring
  map_smul' scalar u := by ext <;> simp [realLeviInput] <;> ring

/-- The matrix of the real Levi action in the coordinates `(u.1, u.2)`. -/
def realLeviMatrixOf (m : BinaryRealGL) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![m.val 1 1, m.val 0 1; m.val 1 0, m.val 0 0]

theorem realLeviMatrixOf_det (m : BinaryRealGL) : (realLeviMatrixOf m).det = m.val.det := by
  rw [realLeviMatrixOf, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  ring

theorem realLeviInput_measurePreserving {m : BinaryRealGL} (unimodular : |m.val.det| = 1) :
    MeasurePreserving (realLeviInput m) ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
  have absolute : |(realLeviMatrixOf m).det| = 1 := by rw [realLeviMatrixOf_det]; exact unimodular
  have nonzero : (realLeviMatrixOf m).det ≠ 0 := by
    intro zero
    rw [zero, abs_zero] at absolute
    exact zero_ne_one absolute
  have linear_preserving : MeasurePreserving (Matrix.toLin' (realLeviMatrixOf m))
      (volume : Measure (Fin 2 → ℝ)) volume := by
    refine ⟨(Matrix.toLin' (realLeviMatrixOf m)).continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi nonzero, abs_inv, absolute, inv_one,
      ENNReal.ofReal_one, one_smul]
  have to_pair := measurePreserving_finTwoArrow (volume : Measure ℝ)
  have to_vector := to_pair.symm MeasurableEquiv.finTwoArrow
  have composed := to_pair.comp (linear_preserving.comp to_vector)
  convert composed using 1
  funext u
  ext <;> simp [realLeviInput, realLeviMatrixOf, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] <;> ring

theorem integral_realLeviInput {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : ℝ × ℝ → E) {m : BinaryRealGL} (unimodular : |m.val.det| = 1) :
    (∫ u : ℝ × ℝ, function (realLeviInput m u) ∂((volume : Measure ℝ).prod volume)) =
      ∫ u : ℝ × ℝ, function u ∂((volume : Measure ℝ).prod volume) :=
  (realLeviInput_measurePreserving unimodular).integral_comp
    (realLeviEquiv m).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding function

theorem integrable_realLeviInput_iff {E : Type*} [NormedAddCommGroup E] (function : ℝ × ℝ → E)
    {m : BinaryRealGL} (unimodular : |m.val.det| = 1) :
    Integrable (fun u => function (realLeviInput m u)) ((volume : Measure ℝ).prod volume) ↔
      Integrable function ((volume : Measure ℝ).prod volume) :=
  (realLeviInput_measurePreserving unimodular).integrable_comp_emb
    (realLeviEquiv m).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

theorem realRadicalShift_measurePreserving (Y : ℝ × ℝ) :
    MeasurePreserving (realRadicalShift Y) ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
  have equality : realRadicalShift Y = fun u => u + (Y.2, Y.1) := by
    funext u
    rfl
  rw [equality]
  exact measurePreserving_add_right _ _

theorem integral_realRadicalShift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : ℝ × ℝ → E) (Y : ℝ × ℝ) :
    (∫ u : ℝ × ℝ, function (realRadicalShift Y u) ∂((volume : Measure ℝ).prod volume)) =
      ∫ u : ℝ × ℝ, function u ∂((volume : Measure ℝ).prod volume) := by
  have equality : realRadicalShift Y = fun u => u + (Y.2, Y.1) := by
    funext u
    rfl
  rw [equality]
  exact integral_add_right_eq_self function _

theorem integrable_realRadicalShift_iff {E : Type*} [NormedAddCommGroup E] (function : ℝ × ℝ → E)
    (Y : ℝ × ℝ) :
    Integrable (fun u => function (realRadicalShift Y u)) ((volume : Measure ℝ).prod volume) ↔
      Integrable function ((volume : Measure ℝ).prod volume) := by
  have equality : realRadicalShift Y = fun u => u + (Y.2, Y.1) := by
    funext u
    rfl
  rw [equality]
  exact (measurePreserving_add_right ((volume : Measure ℝ).prod volume)
    (Y.2, Y.1)).integrable_comp_emb (measurableEmbedding_addRight (Y.2, Y.1))

end TernaryPeriodPolynomials.AnalyticClasses
