module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AdditiveCocycleDifferentiation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.ShearExponential

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

attribute [local instance] complexEndRationalAlgebra

theorem nilpotentExponential_real_parameter (operator : Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : operator ^ cutoff = 0) (parameter : ℝ) (vector : E) :
    IsNilpotent.exp ((parameter : ℂ) • operator) vector =
      finiteExponentialVector (fun power => (operator ^ power) vector) cutoff parameter := by
  have scaled : ((parameter : ℂ) • operator) ^ cutoff = 0 := by
    rw [smul_pow, nilpotent, smul_zero]
  rw [IsNilpotent.exp_eq_sum scaled, LinearMap.sum_apply, finiteExponentialVector]
  apply Finset.sum_congr rfl
  intro power _
  rw [rationalEnd_smul_apply, smul_pow, LinearMap.smul_apply, smul_smul,
    ← IsScalarTower.algebraMap_smul ℂ (parameter ^ power / (power.factorial : ℝ))]
  congr 1
  change ((↑((power.factorial : ℚ)⁻¹) : ℂ) * (parameter : ℂ) ^ power) =
    ((parameter ^ power / (power.factorial : ℝ) : ℝ) : ℂ)
  push_cast
  ring

theorem finiteExponentialPrimitive_one_average (operator : Module.End ℂ E) (cutoff : ℕ) (vector : E) :
    finiteExponentialPrimitive (fun power => (operator ^ power) vector) cutoff 1 =
      nilpotentExponentialAverage operator cutoff vector := by
  rw [finiteExponentialPrimitive, nilpotentExponentialAverage, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro power _
  rw [one_pow, one_div, rationalEnd_smul_apply, ← IsScalarTower.algebraMap_smul ℂ (((power + 1).factorial : ℝ)⁻¹)]
  congr 1
  push_cast
  rfl

theorem additiveNilpotentCocycle_formula (operator : Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : operator ^ cutoff = 0) (action : ℝ → E →L[ℝ] E)
    (exponential : ∀ parameter vector, action parameter vector = IsNilpotent.exp ((parameter : ℂ) • operator) vector)
    (cycle : ℝ → E)
    (cocycle : ∀ first second, cycle (first + second) = action first (cycle second) + cycle first)
    (origin : cycle 0 = 0) (tangent : E) (derivative : HasDerivAt cycle tangent 0) :
    cycle = finiteExponentialPrimitive (fun power => (operator ^ power) tangent) cutoff := by
  apply additiveCocycle_eq_finitePrimitive action cycle cocycle origin tangent derivative
  intro parameter
  rw [exponential, nilpotentExponential_real_parameter operator cutoff nilpotent]

theorem additiveNilpotentCocycle_one (operator : Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : operator ^ cutoff = 0) (action : ℝ → E →L[ℝ] E)
    (exponential : ∀ parameter vector, action parameter vector = IsNilpotent.exp ((parameter : ℂ) • operator) vector)
    (cycle : ℝ → E)
    (cocycle : ∀ first second, cycle (first + second) = action first (cycle second) + cycle first)
    (origin : cycle 0 = 0) (tangent : E) (derivative : HasDerivAt cycle tangent 0) :
    cycle 1 = nilpotentExponentialAverage operator cutoff tangent := by
  rw [additiveNilpotentCocycle_formula operator cutoff nilpotent action exponential cycle cocycle origin tangent derivative,
    finiteExponentialPrimitive_one_average]

theorem additiveNilpotentCocycle_tangent (operator : Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : operator ^ (cutoff + 1) = 0) (action : ℝ → E →L[ℝ] E)
    (exponential : ∀ parameter vector, action parameter vector = IsNilpotent.exp ((parameter : ℂ) • operator) vector)
    (cycle : ℝ → E)
    (cocycle : ∀ first second, cycle (first + second) = action first (cycle second) + cycle first)
    (origin : cycle 0 = 0) (tangent : E) (derivative : HasDerivAt cycle tangent 0) :
    tangent = (nilpotentAverageEquiv operator ⟨cutoff + 1, nilpotent⟩ cutoff).symm (cycle 1) := by
  rw [additiveNilpotentCocycle_one operator (cutoff + 1) nilpotent action exponential cycle cocycle origin tangent derivative]
  exact ((nilpotentAverageEquiv operator ⟨cutoff + 1, nilpotent⟩ cutoff).symm_apply_apply tangent).symm

theorem additiveNilpotentCocycle_eq_of_one (operator : Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : operator ^ (cutoff + 1) = 0) (action : ℝ → E →L[ℝ] E)
    (exponential : ∀ parameter vector, action parameter vector = IsNilpotent.exp ((parameter : ℂ) • operator) vector)
    (first second : ℝ → E)
    (first_cocycle : ∀ x y, first (x + y) = action x (first y) + first x)
    (second_cocycle : ∀ x y, second (x + y) = action x (second y) + second x)
    (first_origin : first 0 = 0) (second_origin : second 0 = 0)
    (first_regular : DifferentiableAt ℝ first 0) (second_regular : DifferentiableAt ℝ second 0)
    (one : first 1 = second 1) : first = second := by
  have first_tangent := additiveNilpotentCocycle_tangent operator cutoff nilpotent action exponential
    first first_cocycle first_origin _ first_regular.hasDerivAt
  have second_tangent := additiveNilpotentCocycle_tangent operator cutoff nilpotent action exponential
    second second_cocycle second_origin _ second_regular.hasDerivAt
  have tangent : deriv first 0 = deriv second 0 := by rw [first_tangent, second_tangent, one]
  apply additiveCocycle_eq_of_tangent action first second first_cocycle second_cocycle (deriv first 0)
    first_regular.hasDerivAt
  · rw [tangent]
    exact second_regular.hasDerivAt
  · rw [first_origin, second_origin]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
