module

public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Algebra.Algebra.TransferInstance
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
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Choose.Cast
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
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


open MeasureTheory Filter

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realExp_strip_bound (center radius parameter value : ℝ)
    (near : |parameter - center| ≤ radius) :
    Real.exp (parameter * value) ≤
      Real.exp ((center + radius) * value) + Real.exp ((center - radius) * value) := by
  obtain ⟨lower, upper⟩ := abs_le.mp near
  by_cases positive : 0 ≤ value
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) positive)).trans
      (le_add_of_nonneg_right (Real.exp_nonneg _))
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith) (le_of_not_ge positive))).trans
      (le_add_of_nonneg_left (Real.exp_nonneg _))

theorem weightedExponential_aestronglyMeasurable {α : Type*} [MeasurableSpace α] (measure : Measure α)
    (height : α → ℝ) (value : α → ℂ) (height_measurable : AEMeasurable height measure)
    (value_measurable : AEMeasurable value measure) (parameter : ℂ) :
    AEStronglyMeasurable (fun point => Complex.exp (parameter * (height point : ℂ)) * value point) measure := by
  exact ((Complex.continuous_exp.measurable.comp_aemeasurable
    (height_measurable.complex_ofReal.const_mul parameter)).mul value_measurable).aestronglyMeasurable

theorem weightedExponential_integrable {α : Type*} [MeasurableSpace α] (measure : Measure α)
    (height : α → ℝ) (value : α → ℂ) (height_measurable : AEMeasurable height measure)
    (value_measurable : AEMeasurable value measure) (bound : ℝ) (bounded : ∀ point, ‖value point‖ ≤ bound)
    (parameter : ℂ) (integrable : Integrable (fun point => Real.exp (parameter.re * height point)) measure) :
    Integrable (fun point => Complex.exp (parameter * (height point : ℂ)) * value point) measure := by
  apply (integrable.mul_const bound).mono'
    (weightedExponential_aestronglyMeasurable measure height value height_measurable value_measurable parameter)
  filter_upwards [] with point
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (bounded point) (Real.exp_nonneg _)

theorem weightedExponential_hasDerivAt (height : ℝ) (value parameter : ℂ) :
    HasDerivAt (fun parameter : ℂ => Complex.exp (parameter * (height : ℂ)) * value)
      ((height : ℂ) * (Complex.exp (parameter * (height : ℂ)) * value)) parameter := by
  simpa only [id_eq, one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id parameter).mul_const (height : ℂ)).cexp.mul_const value)

theorem weightedExponentialIntegral_differentiableAt {α : Type*} [MeasurableSpace α] (measure : Measure α)
    (height : α → ℝ) (value : α → ℂ) (height_measurable : AEMeasurable height measure)
    (value_measurable : AEMeasurable value measure) (bound : ℝ) (bounded : ∀ point, ‖value point‖ ≤ bound)
    (threshold : ℝ) (integrable : ∀ exponent : ℝ, threshold < exponent →
      Integrable (fun point => Real.exp (exponent * height point)) measure)
    (parameter : ℂ) (inside : threshold < parameter.re) :
    DifferentiableAt ℂ (fun parameter : ℂ =>
      ∫ point, Complex.exp (parameter * (height point : ℂ)) * value point ∂measure) parameter := by
  let radius := (parameter.re - threshold) / 4
  have radius_positive : 0 < radius := by dsimp [radius]; linarith
  let majorant := fun point => (|height point| * Real.exp ((parameter.re + radius) * height point) +
    |height point| * Real.exp ((parameter.re - radius) * height point)) * bound
  have moment (exponent : ℝ) (lower : threshold < exponent - radius) :
      Integrable (fun point => |height point| * Real.exp (exponent * height point)) measure := by
    have result := ProbabilityTheory.integrable_pow_abs_mul_exp_of_integrable_exp_mul
      (ne_of_gt radius_positive) (integrable (exponent + radius) (by linarith))
      (integrable (exponent - radius) lower) 1
    simpa only [pow_one] using result
  have majorant_integrable : Integrable majorant measure := by
    exact ((moment (parameter.re + radius) (by dsimp [radius]; linarith)).add
      (moment (parameter.re - radius) (by dsimp [radius]; linarith))).mul_const bound
  have derivative := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := measure) (x₀ := parameter) (s := Metric.ball parameter radius)
    (F := fun parameter point => Complex.exp (parameter * (height point : ℂ)) * value point)
    (F' := fun parameter point => (height point : ℂ) *
      (Complex.exp (parameter * (height point : ℂ)) * value point))
    (bound := majorant) (Metric.ball_mem_nhds parameter radius_positive)
    (Eventually.of_forall (weightedExponential_aestronglyMeasurable measure height value height_measurable value_measurable))
    (weightedExponential_integrable measure height value height_measurable value_measurable bound bounded parameter
      (integrable parameter.re inside))
    (height_measurable.complex_ofReal.aestronglyMeasurable.mul
      (weightedExponential_aestronglyMeasurable measure height value height_measurable value_measurable parameter))
    (Eventually.of_forall (fun point other near => ?_)) majorant_integrable
    (Eventually.of_forall (fun point other _ => weightedExponential_hasDerivAt (height point) (value point) other))
  · exact derivative.2.differentiableAt
  · have distance : |other.re - parameter.re| ≤ radius := by
      have estimate := Complex.abs_re_le_norm (other - parameter)
      rw [Complex.sub_re] at estimate
      exact estimate.trans (le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using near))
    have exponential_bound := realExp_strip_bound parameter.re radius other.re (height point) distance
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ |height point| * (Real.exp (other.re * height point) * bound) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (bounded point) (Real.exp_nonneg _)) (abs_nonneg _)
      _ ≤ |height point| * ((Real.exp ((parameter.re + radius) * height point) +
          Real.exp ((parameter.re - radius) * height point)) * bound) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right exponential_bound
          ((norm_nonneg (value point)).trans (bounded point))) (abs_nonneg _)
      _ = majorant point := by dsimp [majorant]; ring

theorem weightedExponentialIntegral_analyticAt {α : Type*} [MeasurableSpace α] (measure : Measure α)
    (height : α → ℝ) (value : α → ℂ) (height_measurable : AEMeasurable height measure)
    (value_measurable : AEMeasurable value measure) (bound : ℝ) (bounded : ∀ point, ‖value point‖ ≤ bound)
    (threshold : ℝ) (integrable : ∀ exponent : ℝ, threshold < exponent →
      Integrable (fun point => Real.exp (exponent * height point)) measure)
    (parameter : ℂ) (inside : threshold < parameter.re) :
    AnalyticAt ℂ (fun parameter : ℂ =>
      ∫ point, Complex.exp (parameter * (height point : ℂ)) * value point ∂measure) parameter := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have near : ∀ᶠ other in nhds parameter, threshold < other.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds inside
  filter_upwards [near] with other other_inside
  exact weightedExponentialIntegral_differentiableAt measure height value height_measurable value_measurable
    bound bounded threshold integrable other other_inside

end TernaryPeriodPolynomials.SphericalDetection.Helpers
