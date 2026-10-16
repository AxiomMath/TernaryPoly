module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BinaryGaussian
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.RankOne

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BinaryRowMeasure

open BinaryGaussian

theorem upper_preserving (entry : Adeles) :
    MeasurePreserving (rowAction (binaryUnipotent entry)) radicalMeasure radicalMeasure := by
  have shear := (MeasurePreserving.id adeleMeasure).skew_product
    (g := fun first second : Adeles => first * entry + second)
    (by fun_prop) (Filter.Eventually.of_forall (fun first =>
      (measurePreserving_add_left adeleMeasure (first * entry)).map_eq))
  have map_eq : rowAction (binaryUnipotent entry) =
      fun pair : Adeles × Adeles => (pair.1, pair.1 * entry + pair.2) := by
    funext pair
    exact rowAction_upper entry pair
  rw [map_eq]
  simpa only [radicalMeasure, id_eq] using shear

theorem lower_preserving (entry : Adeles) :
    MeasurePreserving (rowAction (lower entry)) radicalMeasure radicalMeasure := by
  have swap := Measure.measurePreserving_swap (μ := adeleMeasure) (ν := adeleMeasure)
  have shear := swap.comp ((upper_preserving entry).comp swap)
  have map_eq : rowAction (lower entry) =
      fun pair : Adeles × Adeles => (pair.1 + pair.2 * entry, pair.2) := by
    funext pair
    exact rowAction_lower entry pair
  rw [map_eq]
  simpa [radicalMeasure, Function.comp_def, rowAction_upper, Prod.swap, add_comm] using shear

theorem diagonal_scale (first second : Adelesˣ) :
    (adeleNorm first * adeleNorm second) •
        Measure.map (rowAction (diagonal first second)) radicalMeasure = radicalMeasure := by
  have left := addEquivAddHaarChar_smul_map adeleMeasure (ContinuousAddEquiv.mulLeft first)
  have right := addEquivAddHaarChar_smul_map adeleMeasure (ContinuousAddEquiv.mulLeft second)
  change adeleNorm first • Measure.map (fun value => first.val * value) adeleMeasure =
    adeleMeasure at left
  change adeleNorm second • Measure.map (fun value => second.val * value) adeleMeasure =
    adeleMeasure at right
  have product := congrArg₂ (fun a b : Measure Adeles => a.prod b) left right
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] at product
  have mapped := Measure.map_prod_map (f := fun value => first.val * value)
    (g := fun value => second.val * value) adeleMeasure adeleMeasure
    (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  rw [mapped] at product
  have map_eq : rowAction (diagonal first second) =
      fun pair : Adeles × Adeles => (first.val * pair.1, second.val * pair.2) := by
    funext pair
    exact rowAction_diagonal first second pair
  rw [map_eq]
  simpa only [radicalMeasure, Prod.map_def] using product

theorem scale_mul (first second : BinaryAdelicGL)
    (left : adeleNorm (GeneralLinearGroup.det first) •
      Measure.map (rowAction first) radicalMeasure = radicalMeasure)
    (right : adeleNorm (GeneralLinearGroup.det second) •
      Measure.map (rowAction second) radicalMeasure = radicalMeasure) :
    adeleNorm (GeneralLinearGroup.det (first * second)) •
      Measure.map (rowAction (first * second)) radicalMeasure = radicalMeasure := by
  have firstMeasurable : Measurable (rowAction first) := (rowEquiv first).continuous.measurable
  have secondMeasurable : Measurable (rowAction second) := (rowEquiv second).continuous.measurable
  have composition : rowAction (first * second) = rowAction second ∘ rowAction first :=
    funext (rowAction_mul first second)
  rw [map_mul, map_mul, mul_comm (adeleNorm (GeneralLinearGroup.det first)),
    mul_smul, composition, ← Measure.map_map secondMeasurable firstMeasurable,
    ← Measure.map_smul (adeleNorm (GeneralLinearGroup.det first))
      (μ := Measure.map (rowAction first) radicalMeasure) (f := rowAction second), left, right]
  exact secondMeasurable.aemeasurable

theorem row_scale (matrix : BinaryAdelicGL) :
    adeleNorm (GeneralLinearGroup.det matrix) •
      Measure.map (rowAction matrix) radicalMeasure = radicalMeasure := by
  obtain ⟨a, b, c, first, second, decomposition⟩ := adelic_decomposition matrix
  rw [decomposition]
  apply scale_mul
  · apply scale_mul
    · apply scale_mul
      · simpa only [upper_det, map_one, one_smul] using (upper_preserving a).map_eq
      · simpa only [lower_det, map_one, one_smul] using (lower_preserving b).map_eq
    · simpa only [diagonal_det, map_mul] using diagonal_scale first second
  · simpa only [upper_det, map_one, one_smul] using (upper_preserving c).map_eq

theorem integral_row {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (matrix : BinaryAdelicGL) (function : Adeles × Adeles → E) :
    (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) •
      (∫ coordinates, function (rowAction matrix coordinates) ∂radicalMeasure) =
        ∫ coordinates, function coordinates ∂radicalMeasure := by
  have scaled := congrArg (fun measure : Measure (Adeles × Adeles) =>
    ∫ coordinates, function coordinates ∂measure) (row_scale matrix)
  rw [integral_smul_nnreal_measure] at scaled
  have mapped := integral_map_equiv (μ := radicalMeasure)
    (rowEquiv matrix).toHomeomorph.toMeasurableEquiv function
  change (∫ coordinates, function coordinates ∂Measure.map (rowAction matrix) radicalMeasure) =
    ∫ coordinates, function (rowAction matrix coordinates) ∂radicalMeasure at mapped
  rwa [mapped] at scaled

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BinaryRowMeasure
