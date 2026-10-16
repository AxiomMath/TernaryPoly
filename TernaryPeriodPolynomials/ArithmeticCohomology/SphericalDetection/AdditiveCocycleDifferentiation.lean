module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.SmoothIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem additiveCocycle_hasDerivAt (action : ℝ → E →L[ℝ] E) (cycle : ℝ → E)
    (cocycle : ∀ first second, cycle (first + second) = action first (cycle second) + cycle first)
    (tangent : E) (derivative : HasDerivAt cycle tangent 0) (point : ℝ) :
    HasDerivAt cycle (action point tangent) point := by
  have translated : HasDerivAt (fun parameter => cycle (point + parameter)) (action point tangent) 0 := by
    simpa only [cocycle, Function.comp_def] using ((action point).hasFDerivAt.comp_hasDerivAt 0 derivative).add_const (cycle point)
  have shifted := translated.scomp_of_eq point ((hasDerivAt_id point).sub_const point) (sub_self point).symm
  convert shifted using 1 <;> simp [Function.comp_def, sub_eq_add_neg]

theorem additiveCocycle_eq_of_tangent (action : ℝ → E →L[ℝ] E) (first second : ℝ → E)
    (first_cocycle : ∀ x y, first (x + y) = action x (first y) + first x)
    (second_cocycle : ∀ x y, second (x + y) = action x (second y) + second x)
    (tangent : E) (first_derivative : HasDerivAt first tangent 0) (second_derivative : HasDerivAt second tangent 0)
    (origin : first 0 = second 0) : first = second := by
  have derivative (point : ℝ) : HasDerivAt (fun parameter => first parameter - second parameter) 0 point := by
    change HasDerivAt (first - second) 0 point
    simpa only [sub_self] using
      (additiveCocycle_hasDerivAt action first first_cocycle tangent first_derivative point).sub
        (additiveCocycle_hasDerivAt action second second_cocycle tangent second_derivative point)
  have constant := is_const_of_deriv_eq_zero (fun point => (derivative point).differentiableAt)
    (fun point => (derivative point).deriv)
  funext point
  have equality := constant point 0
  rw [origin, sub_self] at equality
  exact sub_eq_zero.mp equality

theorem additiveCocycle_integral [CompleteSpace E] (action : ℝ → E →L[ℝ] E) (cycle : ℝ → E)
    (cocycle : ∀ first second, cycle (first + second) = action first (cycle second) + cycle first)
    (origin : cycle 0 = 0) (tangent : E) (derivative : HasDerivAt cycle tangent 0)
    (point : ℝ) (integrable : IntervalIntegrable (fun parameter => action parameter tangent) volume 0 point) :
    cycle point = ∫ parameter in 0..point, action parameter tangent := by
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun parameter (_ : parameter ∈ Set.uIcc 0 point) =>
      additiveCocycle_hasDerivAt action cycle cocycle tangent derivative parameter) integrable
  simpa only [origin, sub_zero] using integral.symm

def finiteExponentialVector (vectors : ℕ → E) (cutoff : ℕ) (parameter : ℝ) : E :=
  ∑ power ∈ Finset.range cutoff, (parameter ^ power / power.factorial : ℝ) • vectors power

def finiteExponentialPrimitive (vectors : ℕ → E) (cutoff : ℕ) (parameter : ℝ) : E :=
  ∑ power ∈ Finset.range cutoff, (parameter ^ (power + 1) / (power + 1).factorial : ℝ) • vectors power

theorem finiteExponentialVector_differentiable (vectors : ℕ → E) (cutoff : ℕ) :
    Differentiable ℝ (finiteExponentialVector vectors cutoff) := by
  unfold finiteExponentialVector
  fun_prop

theorem finiteExponentialPrimitive_hasDerivAt (vectors : ℕ → E) (cutoff : ℕ) (parameter : ℝ) :
    HasDerivAt (finiteExponentialPrimitive vectors cutoff) (finiteExponentialVector vectors cutoff parameter) parameter := by
  have term (power : ℕ) : HasDerivAt
      (fun sample : ℝ => (sample ^ (power + 1) / (power + 1).factorial) • vectors power)
      ((parameter ^ power / power.factorial) • vectors power) parameter := by
    have coefficient : ((power + 1 : ℕ) : ℝ) * parameter ^ power / ((power + 1).factorial : ℝ) =
        parameter ^ power / (power.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    have derivative := (((hasDerivAt_id parameter).pow (power + 1)).div_const ((power + 1).factorial : ℝ)).smul_const (vectors power)
    simpa only [Nat.add_sub_cancel, Pi.pow_apply, id_eq, mul_one, coefficient] using derivative
  convert HasDerivAt.sum (u := Finset.range cutoff) (fun power _ => term power) using 1
  · funext sample
    simp only [finiteExponentialPrimitive, Finset.sum_apply]
  · rfl

theorem finiteExponentialPrimitive_zero (vectors : ℕ → E) (cutoff : ℕ) :
    finiteExponentialPrimitive vectors cutoff 0 = 0 := by
  simp [finiteExponentialPrimitive]

theorem additiveCocycle_eq_finitePrimitive (action : ℝ → E →L[ℝ] E) (cycle : ℝ → E)
    (cocycle : ∀ first second, cycle (first + second) = action first (cycle second) + cycle first)
    (origin : cycle 0 = 0) (tangent : E) (derivative : HasDerivAt cycle tangent 0)
    (vectors : ℕ → E) (cutoff : ℕ)
    (orbit : ∀ parameter, action parameter tangent = finiteExponentialVector vectors cutoff parameter) :
    cycle = finiteExponentialPrimitive vectors cutoff := by
  have derivative_zero (point : ℝ) :
      HasDerivAt (fun parameter => cycle parameter - finiteExponentialPrimitive vectors cutoff parameter) 0 point := by
    change HasDerivAt (cycle - finiteExponentialPrimitive vectors cutoff) 0 point
    have actual := additiveCocycle_hasDerivAt action cycle cocycle tangent derivative point
    rw [orbit] at actual
    simpa only [sub_self] using actual.sub (finiteExponentialPrimitive_hasDerivAt vectors cutoff point)
  have constant := is_const_of_deriv_eq_zero (fun point => (derivative_zero point).differentiableAt)
    (fun point => (derivative_zero point).deriv)
  funext point
  have equality := constant point 0
  rw [origin, finiteExponentialPrimitive_zero, sub_self] at equality
  exact sub_eq_zero.mp equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
