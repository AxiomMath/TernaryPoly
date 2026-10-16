module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Meromorphic.Basic
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
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
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

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PositiveLaplaceIntegral

variable {Space : Type*}

def integrand (amplitude : Space → ℂ) (height : Space → ℝ) (parameter : ℂ) (point : Space) : ℂ :=
  amplitude point * Complex.exp (parameter * (height point : ℂ))

theorem norm_integrand (amplitude : Space → ℂ) (height : Space → ℝ) (parameter : ℂ) (point : Space) :
    ‖integrand amplitude height parameter point‖ = ‖amplitude point‖ * Real.exp (parameter.re * height point) := by
  simp [integrand, Complex.norm_exp, Complex.mul_re]

theorem measurable [MeasurableSpace Space] (amplitude : Space → ℂ) (height : Space → ℝ)
    (amplitudeMeasurable : Measurable amplitude) (heightMeasurable : Measurable height) (parameter : ℂ) :
    Measurable (integrand amplitude height parameter) :=
  amplitudeMeasurable.mul (Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp heightMeasurable)))

theorem integrable [MeasurableSpace Space] (measure : Measure Space) (amplitude : Space → ℂ) (height : Space → ℝ)
    (amplitudeMeasurable : Measurable amplitude) (heightMeasurable : Measurable height)
    (weightedIntegrable : ∀ exponent : ℝ, Integrable (fun point => ‖amplitude point‖ * Real.exp (exponent * height point)) measure)
    (parameter : ℂ) : Integrable (integrand amplitude height parameter) measure := by
  apply (weightedIntegrable parameter.re).mono' (measurable amplitude height amplitudeMeasurable heightMeasurable parameter).aestronglyMeasurable
  exact Eventually.of_forall (fun point => le_of_eq (norm_integrand amplitude height parameter point))

theorem hasDerivAt_integrand (amplitude : Space → ℂ) (height : Space → ℝ) (point : Space) (parameter : ℂ) :
    HasDerivAt (fun parameter => integrand amplitude height parameter point)
      (integrand amplitude height parameter point * (height point : ℂ)) parameter := by
  have derivative := (((hasDerivAt_id parameter).mul_const (height point : ℂ)).cexp).const_mul (amplitude point)
  simpa only [integrand, id_eq, one_mul, mul_assoc] using derivative

theorem derivative_bound (amplitude : Space → ℂ) (height : Space → ℝ) (point : Space)
    (heightNonnegative : 0 ≤ height point) (center parameter : ℂ) (nearby : parameter ∈ Metric.ball center 1) :
    ‖integrand amplitude height parameter point * (height point : ℂ)‖ ≤
      ‖amplitude point‖ * Real.exp ((center.re + 2) * height point) := by
  have realBound : parameter.re ≤ center.re + 1 := by
    have bound := Complex.re_le_norm (parameter - center)
    rw [Metric.mem_ball, dist_eq_norm] at nearby
    simp only [Complex.sub_re] at bound
    linarith
  have heightBound : height point ≤ Real.exp (height point) := by
    linarith [Real.add_one_le_exp (height point)]
  rw [norm_mul, norm_integrand, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg heightNonnegative]
  calc
    _ ≤ (‖amplitude point‖ * Real.exp (parameter.re * height point)) * Real.exp (height point) :=
      mul_le_mul_of_nonneg_left heightBound (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    _ = ‖amplitude point‖ * Real.exp ((parameter.re + 1) * height point) := by
      rw [add_mul, one_mul, Real.exp_add, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by linarith) heightNonnegative)) (norm_nonneg _)

theorem differentiable [MeasurableSpace Space] (measure : Measure Space) (amplitude : Space → ℂ) (height : Space → ℝ)
    (amplitudeMeasurable : Measurable amplitude) (heightMeasurable : Measurable height)
    (heightNonnegative : ∀ᵐ point ∂measure, 0 ≤ height point)
    (weightedIntegrable : ∀ exponent : ℝ, Integrable (fun point => ‖amplitude point‖ * Real.exp (exponent * height point)) measure) :
    Differentiable ℂ (fun parameter => ∫ point, integrand amplitude height parameter point ∂measure) := by
  intro center
  have derivativeMeasurable : AEStronglyMeasurable
      (fun point => integrand amplitude height center point * (height point : ℂ)) measure :=
    ((measurable amplitude height amplitudeMeasurable heightMeasurable center).mul
      (Complex.continuous_ofReal.measurable.comp heightMeasurable)).aestronglyMeasurable
  have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := measure) (F := integrand amplitude height)
    (F' := fun parameter point => integrand amplitude height parameter point * (height point : ℂ))
    (bound := fun point => ‖amplitude point‖ * Real.exp ((center.re + 2) * height point))
    (Metric.ball_mem_nhds center zero_lt_one)
    (Eventually.of_forall (fun parameter => (measurable amplitude height amplitudeMeasurable heightMeasurable parameter).aestronglyMeasurable))
    (integrable measure amplitude height amplitudeMeasurable heightMeasurable weightedIntegrable center)
    derivativeMeasurable
    (heightNonnegative.mono (fun point nonnegative parameter nearby => derivative_bound amplitude height point nonnegative center parameter nearby))
    (weightedIntegrable (center.re + 2))
    (Eventually.of_forall (fun point parameter _ => hasDerivAt_integrand amplitude height point parameter))
  exact result.2.differentiableAt

theorem derivative_bound_two_sided (amplitude : Space → ℂ) (height : Space → ℝ) (point : Space)
    (center parameter : ℂ) (nearby : parameter ∈ Metric.ball center 1) :
    ‖integrand amplitude height parameter point * (height point : ℂ)‖ ≤
      ‖amplitude point‖ * Real.exp ((center.re + 2) * height point) +
        ‖amplitude point‖ * Real.exp ((center.re - 2) * height point) := by
  by_cases nonnegative : 0 ≤ height point
  · exact (derivative_bound amplitude height point nonnegative center parameter nearby).trans
      (le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le))
  · have negativeHeight : 0 ≤ -height point := neg_nonneg.mpr (le_of_not_ge nonnegative)
    have nearbyNegative : -parameter ∈ Metric.ball (-center) 1 := by
      simpa only [Metric.mem_ball, dist_neg_neg] using nearby
    have bounded := derivative_bound amplitude (fun point => -height point) point negativeHeight (-center) (-parameter) nearbyNegative
    have equality : ((-center).re + 2) * -height point = (center.re - 2) * height point := by
      simp only [Complex.neg_re]
      ring
    simp only [integrand, Complex.ofReal_neg, neg_mul, mul_neg, neg_neg, norm_neg, equality] at bounded
    exact bounded.trans (le_add_of_nonneg_left (mul_nonneg (norm_nonneg (amplitude point))
      (Real.exp_pos ((center.re + 2) * height point)).le))

theorem differentiable_two_sided [MeasurableSpace Space] (measure : Measure Space) (amplitude : Space → ℂ) (height : Space → ℝ)
    (amplitudeMeasurable : Measurable amplitude) (heightMeasurable : Measurable height)
    (weightedIntegrable : ∀ exponent : ℝ, Integrable (fun point => ‖amplitude point‖ * Real.exp (exponent * height point)) measure) :
    Differentiable ℂ (fun parameter => ∫ point, integrand amplitude height parameter point ∂measure) := by
  intro center
  have derivativeMeasurable : AEStronglyMeasurable
      (fun point => integrand amplitude height center point * (height point : ℂ)) measure :=
    ((measurable amplitude height amplitudeMeasurable heightMeasurable center).mul
      (Complex.continuous_ofReal.measurable.comp heightMeasurable)).aestronglyMeasurable
  have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := measure) (F := integrand amplitude height)
    (F' := fun parameter point => integrand amplitude height parameter point * (height point : ℂ))
    (bound := fun point => ‖amplitude point‖ * Real.exp ((center.re + 2) * height point) +
      ‖amplitude point‖ * Real.exp ((center.re - 2) * height point))
    (Metric.ball_mem_nhds center zero_lt_one)
    (Eventually.of_forall (fun parameter => (measurable amplitude height amplitudeMeasurable heightMeasurable parameter).aestronglyMeasurable))
    (integrable measure amplitude height amplitudeMeasurable heightMeasurable weightedIntegrable center)
    derivativeMeasurable
    (Eventually.of_forall (fun point parameter nearby => derivative_bound_two_sided amplitude height point center parameter nearby))
    ((weightedIntegrable (center.re + 2)).add (weightedIntegrable (center.re - 2)))
    (Eventually.of_forall (fun point parameter _ => hasDerivAt_integrand amplitude height point parameter))
  exact result.2.differentiableAt

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PositiveLaplaceIntegral
