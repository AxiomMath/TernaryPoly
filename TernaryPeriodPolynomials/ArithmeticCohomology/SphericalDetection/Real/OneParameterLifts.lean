module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AdditiveTwoCocyclePrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Two.CocycleLiftDifference
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.NilpotentInterpolation

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {G E : Type} [Group G] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem twoCocycleRealLift_exists (representation : Representation ℂ G E)
    (cycle : groupCohomology.cocycles₂ (Rep.of representation)) (unit_zero : cycle (1, 1) = 0)
    (input : Multiplicative ℝ →* G) (operator : Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : operator ^ (cutoff + 1) = 0) (action : ℝ → E →L[ℝ] E)
    (action_eq : ∀ parameter vector, action parameter vector = representation (input (Multiplicative.ofAdd parameter)) vector)
    (exponential : ∀ parameter vector, action parameter vector = IsNilpotent.exp ((parameter : ℂ) • operator) vector)
    (regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : ℝ × ℝ =>
      cycle (input (Multiplicative.ofAdd point.1), input (Multiplicative.ofAdd point.2))))
    (coefficient : E) :
    ∃ lift : Multiplicative ℝ →* TwoCocycleExtension (Rep.of representation) cycle unit_zero,
      (∀ element, (lift element).element = input element) ∧
      (lift (Multiplicative.ofAdd 1)).coefficient = coefficient ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter => (lift (Multiplicative.ofAdd parameter)).coefficient) := by
  let restricted (first second : ℝ) := cycle (input (Multiplicative.ofAdd first), input (Multiplicative.ofAdd second))
  have relation (first second third : ℝ) :
      restricted (first + second) third + restricted first second =
        action first (restricted second third) + restricted first (second + third) := by
    rw [action_eq]
    have equality := twoCocycle_relation (Rep.of representation) cycle
      (input (Multiplicative.ofAdd first)) (input (Multiplicative.ofAdd second)) (input (Multiplicative.ofAdd third))
    rw [← input.map_mul, ← input.map_mul] at equality
    exact equality
  have origin (first : ℝ) : restricted first 0 = 0 := by
    change cycle (input (Multiplicative.ofAdd first), input 1) = 0
    rw [map_one, twoCocycle_one_right, unit_zero, map_zero]
  obtain ⟨primitive, primitive_zero, primitive_smooth, primitive_boundary⟩ :=
    additiveTwoCocycle_exists_smooth_primitive action restricted relation origin regular
  have action_add (first second : ℝ) (vector : E) :
      action (first + second) vector = action first (action second vector) := by
    simp only [action_eq]
    change representation (input (Multiplicative.ofAdd first * Multiplicative.ofAdd second)) vector = _
    rw [map_mul, map_mul, Module.End.mul_apply]
  obtain ⟨correction, correction_zero, correction_one, correction_smooth, correction_cocycle⟩ :=
    additiveNilpotentCocycle_exists_of_one operator cutoff nilpotent action exponential action_add
      (coefficient + primitive 1)
  let coefficients (point : ℝ) := -primitive point + correction point
  have coefficients_zero : coefficients 0 = 0 := by simp [coefficients, primitive_zero, correction_zero]
  have coefficients_mul (first second : ℝ) :
      coefficients (first + second) = coefficients first +
        representation (input (Multiplicative.ofAdd first)) (coefficients second) + restricted first second := by
    have boundary := primitive_boundary first second
    have additive := correction_cocycle first second
    simp only [action_eq] at boundary additive
    simp only [coefficients, map_add, map_neg]
    linear_combination (norm := abel) -boundary + additive
  let lift : Multiplicative ℝ →* TwoCocycleExtension (Rep.of representation) cycle unit_zero :=
    { toFun := fun element => ⟨coefficients element.toAdd, input element⟩
      map_one' := by
        apply TwoCocycleExtension.ext
        · exact coefficients_zero
        · exact input.map_one
      map_mul' := by
        intro first second
        apply TwoCocycleExtension.ext
        · exact coefficients_mul first.toAdd second.toAdd
        · exact input.map_mul first second }
  refine ⟨lift, fun _ => rfl, ?_, ?_⟩
  · change -primitive 1 + correction 1 = coefficient
    rw [correction_one]
    abel
  · exact primitive_smooth.neg.add correction_smooth

end TernaryPeriodPolynomials.SphericalDetection.Helpers
