module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.SemidirectPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem cocycle_primitive_of_factorization_correction
    (ambient target : Subgroup G) (inclusion : target ≤ ambient)
    (representation : Representation ℂ G V) (cocycle : cocycles ambient representation)
    (radical levi : target → ambient)
    (factorization : ∀ element, (radical element).val * (levi element).val = element.val)
    (radical_product : ∀ first second,
      (radical (first * second)).val = (radical first).val *
        ((levi first).val * (radical second).val * (levi first).val⁻¹))
    (levi_product : ∀ first second,
      (levi (first * second)).val = (levi first).val * (levi second).val)
    (pure_radical : ∀ first second,
      barValue ambient representation cocycle (radical first).val
        ((levi first).val * (radical second).val * (levi first).val⁻¹) = 0)
    (pure_levi : ∀ first second,
      barValue ambient representation cocycle (levi first).val (levi second).val = 0)
    (radical_values : G → V)
    (radical_relation : ∀ first second,
      radical_values ((radical first).val *
          ((levi first).val * (radical second).val * (levi first).val⁻¹)) =
        radical_values (radical first).val + representation (radical first).val
          (radical_values ((levi first).val * (radical second).val * (levi first).val⁻¹)))
    (correction : target → V)
    (correction_cocycle : ∀ first second,
      correction (first * second) = correction first +
        representation (levi first).val (correction second))
    (mixed_boundary : ∀ first second,
      mixedValue ambient representation cocycle (levi first).val
          ((levi first).val * (radical second).val * (levi first).val⁻¹) +
        representation (levi first).val (radical_values (radical second).val) -
        radical_values ((levi first).val * (radical second).val * (levi first).val⁻¹) =
      correction first - representation
        ((levi first).val * (radical second).val * (levi first).val⁻¹) (correction first)) :
    ∃ primitive : cochains target representation 1, ∀ vertices,
      (differentialOne target representation primitive).val vertices =
        cocycle.val.val vertices := by
  let values : target → V := fun element =>
    -barValue ambient representation cocycle (radical element).val (levi element).val -
      radical_values (radical element).val +
      representation (radical element).val (correction element)
  have bar_eq (first second : target) :
      barValue ambient representation cocycle first.val second.val =
        values first + representation first.val (values second) - values (first * second) := by
    have mixed_eq : mixedValue ambient representation cocycle (levi first).val
        ((levi first).val * (radical second).val * (levi first).val⁻¹) =
      correction first - representation
        ((levi first).val * (radical second).val * (levi first).val⁻¹) (correction first) -
        representation (levi first).val (radical_values (radical second).val) +
        radical_values ((levi first).val * (radical second).val * (levi first).val⁻¹) := by
      have relation := mixed_boundary first second
      apply sub_eq_zero.mp
      convert congrArg (fun v => v -
        (correction first-representation
          ((levi first).val*(radical second).val*(levi first).val⁻¹) (correction first))) relation using 1 <;> abel
    have relation := barValue_factorization ambient representation cocycle
      (radical first) (levi first) (radical second) (levi second)
      (pure_radical first second) (pure_levi first second)
    rw [factorization,factorization,mixed_eq,← radical_product,← levi_product] at relation
    dsimp only [values]
    rw [correction_cocycle,radical_product,radical_relation]
    rw [← factorization first] at relation ⊢
    rw [radical_product] at relation
    simp only [map_add,map_neg,map_sub,← Module.End.mul_apply,← map_mul,
      mul_assoc,inv_mul_cancel,mul_one] at relation ⊢
    apply sub_eq_zero.mp
    convert (sub_eq_zero.mpr relation) using 1
    abel
  obtain ⟨primitive,primitive_eq⟩ := cocycle_coboundary_of_path_values target
    representation (restrictCocycle ambient target inclusion representation cocycle)
    values (by
      intro first second third
      change cocycle.val.val ![first.val,second.val,third.val] = _
      rw [cocycle_eq_barValue ambient representation cocycle ⟨first.val,inclusion first.property⟩]
      have relation := bar_eq (first⁻¹*second) (second⁻¹*third)
      have product_eq : (first⁻¹*second)*(second⁻¹*third) = first⁻¹*third := by group
      rw [product_eq] at relation
      exact congrArg (representation first.val) relation)
  exact ⟨primitive,fun vertices => congrFun (congrArg Subtype.val primitive_eq) vertices⟩

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
