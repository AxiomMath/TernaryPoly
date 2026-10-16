module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.OneParameterLifts

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {G : Type} [Group G]

theorem twoCocycleExtension_conjugate_element (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0)
    (first second : TwoCocycleExtension representation cycle unit_zero)
    (commute : Commute first.element second.element) :
    (first * second * first⁻¹).element = second.element := by
  change first.element * second.element * first.element⁻¹ = second.element
  rw [commute.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem twoCocycleExtension_conjugate_coefficient (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0)
    (first second : TwoCocycleExtension representation cycle unit_zero)
    (commute : Commute first.element second.element) :
    (first * second * first⁻¹).coefficient =
      first.coefficient + representation.ρ first.element second.coefficient + cycle (first.element, second.element) -
        representation.ρ second.element first.coefficient - cycle (second.element, first.element) := by
  have product : (first * second * first⁻¹) * first = first * second := by simp [mul_assoc]
  have coefficients := congrArg TwoCocycleExtension.coefficient product
  change (first * second * first⁻¹).coefficient +
      representation.ρ (first * second * first⁻¹).element first.coefficient +
        cycle ((first * second * first⁻¹).element, first.element) =
    first.coefficient + representation.ρ first.element second.coefficient + cycle (first.element, second.element) at coefficients
  rw [twoCocycleExtension_conjugate_element representation cycle unit_zero first second commute] at coefficients
  linear_combination (norm := abel) coefficients

theorem twoCocycleRealLift_commute_of_one {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (representation : Representation ℂ G E) (cycle : groupCohomology.cocycles₂ (Rep.of representation))
    (unit_zero : cycle (1, 1) = 0) (input : Multiplicative ℝ →* G)
    (operator : Module.End ℂ E) (cutoff : ℕ) (nilpotent : operator ^ (cutoff + 1) = 0)
    (action : ℝ → E →L[ℝ] E)
    (action_eq : ∀ parameter vector, action parameter vector = representation (input (Multiplicative.ofAdd parameter)) vector)
    (exponential : ∀ parameter vector, action parameter vector = IsNilpotent.exp ((parameter : ℂ) • operator) vector)
    (lift : Multiplicative ℝ →* TwoCocycleExtension (Rep.of representation) cycle unit_zero)
    (projects : ∀ element, (lift element).element = input element)
    (regular : DifferentiableAt ℝ (fun parameter => (lift (Multiplicative.ofAdd parameter)).coefficient) 0)
    (element : TwoCocycleExtension (Rep.of representation) cycle unit_zero)
    (base_commutes : ∀ parameter, Commute element.element (input parameter))
    (continuous : Continuous (representation element.element))
    (left_regular : DifferentiableAt ℝ (fun parameter => cycle (element.element, input (Multiplicative.ofAdd parameter))) 0)
    (right_regular : DifferentiableAt ℝ (fun parameter => cycle (input (Multiplicative.ofAdd parameter), element.element)) 0)
    (commutes : Commute element (lift (Multiplicative.ofAdd 1))) :
    ∀ parameter, Commute element (lift parameter) := by
  let conjugate := (MulAut.conj element).toMonoidHom.comp lift
  have conjugate_projects (parameter : Multiplicative ℝ) : (conjugate parameter).element = input parameter := by
    change (element * lift parameter * element⁻¹).element = input parameter
    rw [twoCocycleExtension_conjugate_element _ _ _ element (lift parameter)
      (by rw [projects]; exact base_commutes parameter), projects]
  have formula (parameter : ℝ) : (conjugate (Multiplicative.ofAdd parameter)).coefficient =
      element.coefficient + representation element.element (lift (Multiplicative.ofAdd parameter)).coefficient +
        cycle (element.element, input (Multiplicative.ofAdd parameter)) -
          representation (input (Multiplicative.ofAdd parameter)) element.coefficient -
            cycle (input (Multiplicative.ofAdd parameter), element.element) := by
    have equality := twoCocycleExtension_conjugate_coefficient (Rep.of representation) cycle unit_zero element
      (lift (Multiplicative.ofAdd parameter)) (by rw [projects]; exact base_commutes _)
    rw [projects] at equality
    exact equality
  have orbit : (fun parameter => representation (input (Multiplicative.ofAdd parameter)) element.coefficient) =
      finiteExponentialVector (fun power => (operator ^ power) element.coefficient) (cutoff + 1) := by
    funext parameter
    rw [← action_eq, exponential, nilpotentExponential_real_parameter operator (cutoff + 1) nilpotent]
  have orbit_regular : DifferentiableAt ℝ
      (fun parameter => representation (input (Multiplicative.ofAdd parameter)) element.coefficient) 0 := by
    rw [orbit]
    exact (finiteExponentialVector_differentiable _ _) 0
  let coefficient_action : E →L[ℝ] E :=
    (⟨representation element.element, continuous⟩ : E →L[ℂ] E).restrictScalars ℝ
  have mapped := coefficient_action.differentiableAt.comp 0 regular
  have conjugate_regular : DifferentiableAt ℝ
      (fun parameter => (conjugate (Multiplicative.ofAdd parameter)).coefficient) 0 := by
    have computed := ((((differentiableAt_const element.coefficient).add mapped).add left_regular).sub orbit_regular).sub right_regular
    convert computed using 1; first | (funext parameter; exact formula parameter)
  have agreement : conjugate (Multiplicative.ofAdd 1) = lift (Multiplicative.ofAdd 1) := by
    change element * lift (Multiplicative.ofAdd 1) * element⁻¹ = _
    rw [commutes.eq, mul_assoc, mul_inv_cancel, mul_one]
  have equality := twoCocycleRealLift_eq_of_one representation cycle unit_zero input operator cutoff nilpotent
    action action_eq exponential conjugate lift conjugate_projects projects conjugate_regular regular agreement
  intro parameter
  have at_parameter := congrArg (fun hom => hom parameter) equality
  change element * lift parameter * element⁻¹ = lift parameter at at_parameter
  have multiplied := congrArg (fun value => value * element) at_parameter
  change element * lift parameter = lift parameter * element
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using multiplied

end TernaryPeriodPolynomials.SphericalDetection.Helpers
