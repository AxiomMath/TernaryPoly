module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def rightGroupAverage {G : Type*} [Group G] [MeasurableSpace G]
    (measure : Measure G) (function kernel : G → ℂ) (point : G) : ℂ :=
  ∫ shift, function (point * shift) * kernel shift ∂measure

theorem rightGroupAverage_integrable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (measure : Measure G) {function kernel : G → ℂ} (measurable : Measurable function)
    (kernel_integrable : Integrable kernel measure) {bound : ℝ}
    (bounded : ∀ point, ‖function point‖ ≤ bound) (point : G) :
    Integrable (fun shift => function (point * shift) * kernel shift) measure := by
  apply (kernel_integrable.norm.const_mul bound).mono'
    (((measurable.comp (measurable_const.mul measurable_id)).aestronglyMeasurable).mul
      kernel_integrable.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun shift => by
    simp only [Pi.mul_apply, Function.comp_def, norm_mul]
    exact mul_le_mul_of_nonneg_right (bounded _) (norm_nonneg _))

theorem rightGroupAverage_bound {G : Type*} [Group G] [MeasurableSpace G]
    (measure : Measure G) (function : G → ℂ) {kernel : G → ℂ}
    (kernel_integrable : Integrable kernel measure) {bound : ℝ}
    (bounded : ∀ point, ‖function point‖ ≤ bound) (point : G) :
    ‖rightGroupAverage measure function kernel point‖ ≤ bound * ∫ shift, ‖kernel shift‖ ∂measure := by
  have estimate := norm_integral_le_of_norm_le
    (f := fun shift => function (point * shift) * kernel shift) (kernel_integrable.norm.const_mul bound)
    (Filter.Eventually.of_forall (fun shift => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (bounded (point * shift)) (norm_nonneg (kernel shift))))
  simpa only [rightGroupAverage, integral_const_mul] using estimate

theorem rightGroupAverage_measurable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (measure : Measure G) [SFinite measure] {function kernel : G → ℂ}
    (measurable : Measurable function) (kernel_measurable : Measurable kernel) :
    Measurable (rightGroupAverage measure function kernel) :=
  ((measurable.comp (measurable_fst.mul measurable_snd)).mul
    (kernel_measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

theorem rightGroupAverage_left_invariant {G : Type*} [Group G] [MeasurableSpace G]
    (measure : Measure G) (function kernel : G → ℂ) (element : G)
    (invariant : ∀ point, function (element * point) = function point) (point : G) :
    rightGroupAverage measure function kernel (element * point) =
      rightGroupAverage measure function kernel point := by
  unfold rightGroupAverage
  simp only [mul_assoc, invariant]

theorem rightGroupAverage_preserves_zero_average
    {G A : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace A]
    (measure : Measure G) [SFinite measure] (parameterMeasure : Measure A) [IsFiniteMeasure parameterMeasure]
    {function kernel : G → ℂ} (measurable : Measurable function)
    (kernel_integrable : Integrable kernel measure) {bound : ℝ}
    (bounded : ∀ point, ‖function point‖ ≤ bound) (translations : A → G)
    (translations_measurable : Measurable translations)
    (zero : ∀ point, (∫ parameter, function (translations parameter * point) ∂parameterMeasure) = 0)
    (point : G) :
    (∫ parameter, rightGroupAverage measure function kernel (translations parameter * point) ∂parameterMeasure) = 0 := by
  have joint_integrable : Integrable (fun pair : A × G =>
      function ((translations pair.1 * point) * pair.2) * kernel pair.2) (parameterMeasure.prod measure) := by
    apply ((kernel_integrable.norm.const_mul bound).comp_snd parameterMeasure).mono'
      (((measurable.comp (((translations_measurable.comp measurable_fst).mul measurable_const).mul
        measurable_snd)).aestronglyMeasurable).mul
          (kernel_integrable.aestronglyMeasurable.comp_snd (μ := parameterMeasure)))
    exact Filter.Eventually.of_forall (fun pair => by
      simp only [Pi.mul_apply, Function.comp_def, norm_mul]
      exact mul_le_mul_of_nonneg_right (bounded _) (norm_nonneg _))
  unfold rightGroupAverage
  rw [integral_integral_swap joint_integrable]
  simp only [mul_assoc, integral_mul_const, zero, zero_mul, integral_zero]

theorem rightGroupAverage_left_translate_kernel {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] (measure : Measure G) [measure.IsMulLeftInvariant]
    (function kernel : G → ℂ) (translation point : G) :
    rightGroupAverage measure function kernel (translation * point) =
      ∫ shift, function (point * shift) * kernel ((point⁻¹ * translation⁻¹ * point) * shift) ∂measure := by
  have change_variables := integral_mul_left_eq_self (μ := measure)
    (fun shift => function (point * shift) * kernel ((point⁻¹ * translation⁻¹ * point) * shift))
    (point⁻¹ * translation * point)
  have first (shift : G) : point * ((point⁻¹ * translation * point) * shift) = (translation * point) * shift := by group
  have second (shift : G) : (point⁻¹ * translation⁻¹ * point) * ((point⁻¹ * translation * point) * shift) = shift := by group
  simpa only [rightGroupAverage, first, second] using change_variables

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
