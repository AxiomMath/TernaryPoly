module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.PathDefect
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.MixedCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

section Semidirect

variable {GroupType Coefficient : Type} [Group GroupType]
  [AddCommGroup Coefficient] [Module ℂ Coefficient]

theorem cocycle_eq_barValue (ambient : Subgroup GroupType)
    (representation : Representation ℂ GroupType Coefficient)
    (cocycle : cocycles ambient representation) (first : ambient)
    (second third : GroupType) :
    cocycle.val.val ![first.val, second, third] = representation first.val
      (barValue ambient representation cocycle
        (first.val⁻¹ * second) (second⁻¹ * third)) := by
  have equivariance := cocycle.val.property first
    ![1, first.val⁻¹ * second, first.val⁻¹ * third]
  have vertices_eq :
      (fun index => first.val * ![1, first.val⁻¹ * second,
        first.val⁻¹ * third] index) = ![first.val, second, third] := by
    funext index
    fin_cases index
    · exact mul_one first.val
    · exact mul_inv_cancel_left first.val second
    · exact mul_inv_cancel_left first.val third
  rw [vertices_eq] at equivariance
  simpa only [barValue, mul_assoc, mul_inv_cancel_left] using equivariance

theorem cocycle_primitive_of_zero_bar (ambient target : Subgroup GroupType)
    (inclusion : target ≤ ambient)
    (representation : Representation ℂ GroupType Coefficient)
    (cocycle : cocycles ambient representation)
    (vanishing : ∀ first second : target,
      barValue ambient representation cocycle first.val second.val = 0) :
    ∃ primitive : cochains target representation 1, ∀ vertices,
      (differentialOne target representation primitive).val vertices =
        cocycle.val.val vertices := by
  have subgroup_zero : ∀ vertices : Fin 3 → target,
      (restrictCocycle ambient target inclusion representation cocycle).val.val
        (fun index => (vertices index).val) = 0 := by
    intro vertices
    have vertices_eq : (fun index => (vertices index).val) =
        ![(vertices 0).val, (vertices 1).val, (vertices 2).val] := by
      funext index
      fin_cases index <;> rfl
    change cocycle.val.val (fun index => (vertices index).val) = 0
    rw [vertices_eq, cocycle_eq_barValue ambient representation cocycle
      ⟨(vertices 0).val, inclusion (vertices 0).property⟩]
    have zero_value := vanishing ((vertices 0)⁻¹ * vertices 1)
      ((vertices 1)⁻¹ * vertices 2)
    change barValue ambient representation cocycle
      ((vertices 0).val⁻¹ * (vertices 1).val)
      ((vertices 1).val⁻¹ * (vertices 2).val) = 0 at zero_value
    rw [zero_value, map_zero]
  obtain ⟨primitive, primitive_eq⟩ := coboundary_of_zero_on_subgroup_vertices
    target representation (restrictCocycle ambient target inclusion representation cocycle)
    subgroup_zero
  refine ⟨primitive, ?_⟩
  intro vertices
  exact congrFun (congrArg Subtype.val primitive_eq) vertices

theorem cocycle_primitive_of_pure_factorization
    (ambient target : Subgroup GroupType) (inclusion : target ≤ ambient)
    (representation : Representation ℂ GroupType Coefficient)
    (cocycle : cocycles ambient representation)
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
    (mixed_zero : ∀ first second,
      mixedValue ambient representation cocycle (levi first).val
        ((levi first).val * (radical second).val * (levi first).val⁻¹) = 0) :
    ∃ primitive : cochains target representation 1, ∀ vertices,
      (differentialOne target representation primitive).val vertices =
        cocycle.val.val vertices := by
  let values : target → Coefficient := fun element =>
    -barValue ambient representation cocycle (radical element).val (levi element).val
  have bar_eq (first second : target) :
      barValue ambient representation cocycle first.val second.val =
        values first + representation first.val (values second) - values (first * second) := by
    have relation := barValue_factorization ambient representation cocycle
      (radical first) (levi first) (radical second) (levi second)
      (pure_radical first second) (pure_levi first second)
    rw [factorization, factorization, mixed_zero, map_zero,
      ← radical_product, ← levi_product] at relation
    dsimp only [values]
    rw [map_neg, sub_neg_eq_add]
    apply sub_eq_zero.mp
    convert relation using 1; abel
  obtain ⟨primitive, primitive_eq⟩ := cocycle_coboundary_of_path_values target
    representation (restrictCocycle ambient target inclusion representation cocycle)
    values (by
      intro first second third
      change cocycle.val.val ![first.val, second.val, third.val] = _
      rw [cocycle_eq_barValue ambient representation cocycle
        ⟨first.val, inclusion first.property⟩]
      have relation := bar_eq (first⁻¹ * second) (second⁻¹ * third)
      have product_eq : (first⁻¹ * second) * (second⁻¹ * third) = first⁻¹ * third := by
        group
      rw [product_eq] at relation
      exact congrArg (representation first.val) relation)
  refine ⟨primitive, ?_⟩
  intro vertices
  exact congrFun (congrArg Subtype.val primitive_eq) vertices

theorem cocycle_primitive_of_mixed_coboundary
    (ambient target : Subgroup GroupType) (inclusion : target ≤ ambient)
    (representation : Representation ℂ GroupType Coefficient)
    (cocycle : cocycles ambient representation)
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
    (correction : target → Coefficient)
    (correction_cocycle : ∀ first second,
      correction (first * second) = correction first +
        representation (levi first).val (correction second))
    (mixed_boundary : ∀ first second,
      mixedValue ambient representation cocycle (levi first).val
        ((levi first).val * (radical second).val * (levi first).val⁻¹) =
      correction first - representation
        ((levi first).val * (radical second).val * (levi first).val⁻¹)
        (correction first)) :
    ∃ primitive : cochains target representation 1, ∀ vertices,
      (differentialOne target representation primitive).val vertices =
        cocycle.val.val vertices := by
  let values : target → Coefficient := fun element =>
    -barValue ambient representation cocycle (radical element).val (levi element).val +
      representation (radical element).val (correction element)
  have bar_eq (first second : target) :
      barValue ambient representation cocycle first.val second.val =
        values first + representation first.val (values second) - values (first * second) := by
    have relation := barValue_factorization ambient representation cocycle
      (radical first) (levi first) (radical second) (levi second)
      (pure_radical first second) (pure_levi first second)
    rw [factorization, factorization, mixed_boundary,
      ← radical_product, ← levi_product] at relation
    dsimp only [values]
    rw [correction_cocycle, radical_product]
    rw [← factorization first] at relation ⊢
    rw [radical_product] at relation
    simp only [map_add, map_neg, map_sub, ← Module.End.mul_apply, ← map_mul,
      mul_assoc, inv_mul_cancel, mul_one] at relation ⊢
    have adjusted := congrArg (fun value => value -
      (representation (radical first).val (correction first) -
        representation ((radical first).val *
          ((levi first).val * (radical second).val * (levi first).val⁻¹))
          (correction first))) relation
    simp only [mul_assoc] at adjusted
    apply sub_eq_zero.mp
    convert adjusted using 1 <;> abel
  obtain ⟨primitive, primitive_eq⟩ := cocycle_coboundary_of_path_values target
    representation (restrictCocycle ambient target inclusion representation cocycle)
    values (by
      intro first second third
      change cocycle.val.val ![first.val, second.val, third.val] = _
      rw [cocycle_eq_barValue ambient representation cocycle
        ⟨first.val, inclusion first.property⟩]
      have relation := bar_eq (first⁻¹ * second) (second⁻¹ * third)
      have product_eq : (first⁻¹ * second) * (second⁻¹ * third) = first⁻¹ * third := by
        group
      rw [product_eq] at relation
      exact congrArg (representation first.val) relation)
  refine ⟨primitive, ?_⟩
  intro vertices
  exact congrFun (congrArg Subtype.val primitive_eq) vertices

end Semidirect

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
