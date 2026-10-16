module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Two.CocycleExtension
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.NilpotentCocycle

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {G H : Type} [Group G] [Group H]

def twoCocycleLiftDifference (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation)
    (unit_zero : cycle (1, 1) = 0) (input : H →* G)
    (first second : H →* TwoCocycleExtension representation cycle unit_zero)
    (first_projects : ∀ element, (first element).element = input element)
    (second_projects : ∀ element, (second element).element = input element) :
    groupCohomology.cocycles₁ (Rep.res input representation) :=
  ⟨fun element => (first element).coefficient - (second element).coefficient, by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro left right
    have first_mul := congrArg TwoCocycleExtension.coefficient (first.map_mul left right)
    have second_mul := congrArg TwoCocycleExtension.coefficient (second.map_mul left right)
    change (first (left * right)).coefficient = (first left).coefficient +
      representation.ρ (first left).element (first right).coefficient +
        cycle ((first left).element, (first right).element) at first_mul
    change (second (left * right)).coefficient = (second left).coefficient +
      representation.ρ (second left).element (second right).coefficient +
        cycle ((second left).element, (second right).element) at second_mul
    rw [first_projects, first_projects] at first_mul
    rw [second_projects, second_projects] at second_mul
    change (first (left * right)).coefficient - (second (left * right)).coefficient =
      representation.ρ (input left) ((first right).coefficient - (second right).coefficient) +
        ((first left).coefficient - (second left).coefficient)
    rw [map_sub]
    linear_combination (norm := abel) first_mul - second_mul⟩

theorem twoCocycleLiftDifference_apply (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation)
    (unit_zero : cycle (1, 1) = 0) (input : H →* G)
    (first second : H →* TwoCocycleExtension representation cycle unit_zero)
    (first_projects : ∀ element, (first element).element = input element)
    (second_projects : ∀ element, (second element).element = input element) (element : H) :
    twoCocycleLiftDifference representation cycle unit_zero input first second first_projects second_projects element =
      (first element).coefficient - (second element).coefficient := rfl

theorem twoCocycleLiftDifference_zero_iff (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation)
    (unit_zero : cycle (1, 1) = 0) (input : H →* G)
    (first second : H →* TwoCocycleExtension representation cycle unit_zero)
    (first_projects : ∀ element, (first element).element = input element)
    (second_projects : ∀ element, (second element).element = input element) :
    twoCocycleLiftDifference representation cycle unit_zero input first second first_projects second_projects = 0 ↔
      first = second := by
  constructor
  · intro zero
    apply MonoidHom.ext
    intro element
    apply TwoCocycleExtension.ext
    · exact sub_eq_zero.mp (congrArg (fun cocycle => cocycle element) zero)
    · rw [first_projects, second_projects]
  · intro equality
    subst second
    apply groupCohomology.cocycles₁_ext
    intro element
    exact sub_self _

theorem twoCocycleRealLift_eq_of_one {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (representation : Representation ℂ G E) (cycle : groupCohomology.cocycles₂ (Rep.of representation))
    (unit_zero : cycle (1, 1) = 0) (input : Multiplicative ℝ →* G)
    (operator : Module.End ℂ E) (cutoff : ℕ) (nilpotent : operator ^ (cutoff + 1) = 0)
    (action : ℝ → E →L[ℝ] E)
    (action_eq : ∀ parameter vector, action parameter vector = representation (input (Multiplicative.ofAdd parameter)) vector)
    (exponential : ∀ parameter vector, action parameter vector = IsNilpotent.exp ((parameter : ℂ) • operator) vector)
    (first second : Multiplicative ℝ →* TwoCocycleExtension (Rep.of representation) cycle unit_zero)
    (first_projects : ∀ element, (first element).element = input element)
    (second_projects : ∀ element, (second element).element = input element)
    (first_regular : DifferentiableAt ℝ (fun parameter => (first (Multiplicative.ofAdd parameter)).coefficient) 0)
    (second_regular : DifferentiableAt ℝ (fun parameter => (second (Multiplicative.ofAdd parameter)).coefficient) 0)
    (agree : first (Multiplicative.ofAdd 1) = second (Multiplicative.ofAdd 1)) : first = second := by
  let difference := twoCocycleLiftDifference (Rep.of representation) cycle unit_zero input first second
    first_projects second_projects
  have additive (left right : ℝ) : difference (Multiplicative.ofAdd (left + right)) =
      action left (difference (Multiplicative.ofAdd right)) + difference (Multiplicative.ofAdd left) := by
    rw [action_eq]
    exact oneCocycle_mul _ difference (Multiplicative.ofAdd left) (Multiplicative.ofAdd right)
  have origin : difference (Multiplicative.ofAdd 0) = 0 := groupCohomology.cocycles₁_map_one difference
  have regular : DifferentiableAt ℝ (fun parameter => difference (Multiplicative.ofAdd parameter)) 0 :=
    first_regular.sub second_regular
  have at_one : difference (Multiplicative.ofAdd 1) = 0 := by
    change (first (Multiplicative.ofAdd 1)).coefficient - (second (Multiplicative.ofAdd 1)).coefficient = 0
    rw [agree, sub_self]
  have equality := additiveNilpotentCocycle_eq_of_one operator cutoff nilpotent action exponential
    (fun parameter => difference (Multiplicative.ofAdd parameter)) (fun _ => 0) additive
    (by intro left right; simp) origin rfl regular (differentiableAt_const 0) at_one
  apply (twoCocycleLiftDifference_zero_iff (Rep.of representation) cycle unit_zero input first second
    first_projects second_projects).mp
  apply groupCohomology.cocycles₁_ext
  intro element
  exact congrFun equality element.toAdd

end TernaryPeriodPolynomials.SphericalDetection.Helpers
