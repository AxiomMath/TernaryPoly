module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ShellIntegration
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelShells

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ShellDecay

theorem summable_integer (rate : ℝ) (positive : 0 < rate) :
    Summable (fun integer : ℤ => Real.exp (-rate * |(integer : ℝ)|)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  have natural : Summable (fun natural : ℕ => Real.exp (-rate * (natural : ℝ))) := by
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos positive)
  constructor
  · apply natural.congr
    intro value
    simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg value : (0 : ℝ) ≤ value)]
  · apply natural.congr
    intro value
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg value : (0 : ℝ) ≤ value)]

theorem summable_product (scalarRate heightRate : ℝ) (scalarPositive : 0 < scalarRate)
    (heightPositive : 0 < heightRate) :
    Summable (fun index : ℤ × ℕ =>
      Real.exp (-scalarRate * |(index.1 : ℝ)|) * Real.exp (-heightRate * (index.2 : ℝ))) := by
  have natural : Summable (fun natural : ℕ => Real.exp (-heightRate * (natural : ℝ))) := by
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos heightPositive)
  apply (summable_integer scalarRate scalarPositive).mul_of_nonneg natural
  · exact fun _ => (Real.exp_pos _).le
  · exact fun _ => (Real.exp_pos _).le

theorem shifted_bound (scalarRate heightRate : ℝ) (scalarNonnegative : 0 ≤ scalarRate)
    (heightNonnegative : 0 ≤ heightRate) (integer : ℤ) (natural : ℕ)
    (first second : Interval) :
    Real.exp (-scalarRate * |(integer : ℝ) + first.val|) *
        Real.exp (-heightRate * ((natural : ℝ) + second.val)) ≤
      Real.exp scalarRate *
        (Real.exp (-scalarRate * |(integer : ℝ)|) * Real.exp (-heightRate * (natural : ℝ))) := by
  have triangle : |(integer : ℝ)| ≤ |(integer : ℝ) + first.val| + 1 := by
    calc
      _ = |((integer : ℝ) + first.val) + -first.val| := by congr 1; ring
      _ ≤ |(integer : ℝ) + first.val| + |-first.val| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg, abs_of_nonneg first.property.1]; linarith [first.property.2]
  have firstBound : Real.exp (-scalarRate * |(integer : ℝ) + first.val|) ≤
      Real.exp scalarRate * Real.exp (-scalarRate * |(integer : ℝ)|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have secondBound : Real.exp (-heightRate * ((natural : ℝ) + second.val)) ≤
      Real.exp (-heightRate * (natural : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [second.property.1]
  simpa only [mul_assoc] using mul_le_mul firstBound secondBound
    (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)

theorem integrable_region (function : BinaryAdelicGL → ℂ) (measurable : Measurable function)
    (constant scalarRate heightRate : ℝ) (nonnegative : 0 ≤ constant)
    (scalarPositive : 0 < scalarRate) (heightPositive : 0 < heightRate)
    (bounded : ∀ (integer : ℤ) (natural : ℕ) (parameter : Parameter),
      ‖function (parameterize integer natural parameter)‖ ≤ constant *
        (Real.exp (-scalarRate * |(integer : ℝ) + parameter.2.1.val|) *
          Real.exp (-heightRate * ((natural : ℝ) + parameter.2.2.1.val)))) :
    IntegrableOn function AdelicSiegelCover.region BinaryHaar.measure := by
  apply ShellIntegration.integrable_region function measurable
    (fun index => (constant * Real.exp scalarRate) *
      (Real.exp (-scalarRate * |(index.1 : ℝ)|) * Real.exp (-heightRate * (index.2 : ℝ))))
    (fun _ => by positivity)
    ((summable_product scalarRate heightRate scalarPositive heightPositive).mul_left _)
  intro integer natural parameter
  apply (bounded integer natural parameter).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (shifted_bound scalarRate heightRate scalarPositive.le heightPositive.le integer natural parameter.2.1 parameter.2.2.1) nonnegative

theorem integrable_domain (function : BinaryAdelicGL → ℂ) (measurable : Measurable function)
    (invariant : ∀ rational : BinaryRationalGL, ∀ point,
      function (Matrix.GeneralLinearGroup.map rationalAdele rational * point) = function point)
    (constant scalarRate heightRate : ℝ) (nonnegative : 0 ≤ constant)
    (scalarPositive : 0 < scalarRate) (heightPositive : 0 < heightRate)
    (bounded : ∀ (integer : ℤ) (natural : ℕ) (parameter : Parameter),
      ‖function (parameterize integer natural parameter)‖ ≤ constant *
        (Real.exp (-scalarRate * |(integer : ℝ) + parameter.2.1.val|) *
          Real.exp (-heightRate * ((natural : ℝ) + parameter.2.2.1.val)))) :
    IntegrableOn function BinaryFundamentalDomain.domain BinaryHaar.measure :=
  SiegelIntegration.integrableOn function measurable invariant
    (integrable_region function measurable constant scalarRate heightRate nonnegative scalarPositive heightPositive bounded)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ShellDecay
