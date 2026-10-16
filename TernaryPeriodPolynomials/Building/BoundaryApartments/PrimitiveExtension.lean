module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.CyclicCrossed

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

variable {GroupType Vector : Type}
  [Group GroupType] [AddCommGroup Vector] [Module ℂ Vector]

def cosetRetraction (subgroup : Subgroup GroupType) (matrix : GroupType) : subgroup := by
  let coset : Quotient (QuotientGroup.rightRel subgroup) := Quotient.mk _ matrix
  refine ⟨matrix * coset.out⁻¹, ?_⟩
  apply QuotientGroup.rightRel_apply.mp
  exact Quotient.exact coset.out_eq

theorem cosetRetraction_equivariant (subgroup : Subgroup GroupType)
    (matrix : subgroup) (vertex : GroupType) :
    cosetRetraction subgroup (matrix.val * vertex) = matrix * cosetRetraction subgroup vertex := by
  have coset_eq : (Quotient.mk (QuotientGroup.rightRel subgroup) (matrix.val * vertex)) =
      Quotient.mk (QuotientGroup.rightRel subgroup) vertex := by
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using subgroup.inv_mem matrix.property
  apply Subtype.ext
  change (matrix.val * vertex) *
      (Quotient.mk (QuotientGroup.rightRel subgroup) (matrix.val * vertex)).out⁻¹ =
    matrix.val * (vertex * (Quotient.mk (QuotientGroup.rightRel subgroup) vertex).out⁻¹)
  rw [coset_eq, mul_assoc]

theorem cocycle_retraction_homotopy (subgroup : Subgroup GroupType)
    (representation : Representation ℂ GroupType Vector)
    (cocycle : cocycles subgroup representation) (first second third : GroupType) :
    let retract := fun vertex => (cosetRetraction subgroup vertex).val
    (cocycle.val.val ![retract second, second, third] -
        cocycle.val.val ![retract second, retract third, third]) -
      (cocycle.val.val ![retract first, first, third] -
        cocycle.val.val ![retract first, retract third, third]) +
      (cocycle.val.val ![retract first, first, second] -
        cocycle.val.val ![retract first, retract second, second]) =
      cocycle.val.val ![first, second, third] -
        cocycle.val.val ![retract first, retract second, retract third] := by
  dsimp only
  have first_relation := congrFun cocycle.property
    (![ (cosetRetraction subgroup first).val, first, second, third] : Fin 4 → GroupType)
  have second_relation := congrFun cocycle.property
    (![ (cosetRetraction subgroup first).val, (cosetRetraction subgroup second).val,
        second, third] : Fin 4 → GroupType)
  have third_relation := congrFun cocycle.property
    (![ (cosetRetraction subgroup first).val, (cosetRetraction subgroup second).val,
        (cosetRetraction subgroup third).val, third] : Fin 4 → GroupType)
  change cocycle.val.val ![first, second, third] -
    cocycle.val.val ![(cosetRetraction subgroup first).val, second, third] +
    cocycle.val.val ![(cosetRetraction subgroup first).val, first, third] -
    cocycle.val.val ![(cosetRetraction subgroup first).val, first, second] = 0 at first_relation
  change cocycle.val.val ![(cosetRetraction subgroup second).val, second, third] -
    cocycle.val.val ![(cosetRetraction subgroup first).val, second, third] +
    cocycle.val.val ![(cosetRetraction subgroup first).val, (cosetRetraction subgroup second).val,
      third] - cocycle.val.val ![(cosetRetraction subgroup first).val,
        (cosetRetraction subgroup second).val, second] = 0 at second_relation
  change cocycle.val.val ![(cosetRetraction subgroup second).val,
      (cosetRetraction subgroup third).val, third] -
    cocycle.val.val ![(cosetRetraction subgroup first).val, (cosetRetraction subgroup third).val,
      third] + cocycle.val.val ![(cosetRetraction subgroup first).val,
        (cosetRetraction subgroup second).val, third] -
    cocycle.val.val ![(cosetRetraction subgroup first).val, (cosetRetraction subgroup second).val,
      (cosetRetraction subgroup third).val] = 0 at third_relation
  have combination := congrArg₂ (fun left right : Vector => left + right)
    (congrArg₂ (fun left right : Vector => -left + right) first_relation second_relation)
    (congrArg Neg.neg third_relation)
  apply sub_eq_zero.mp
  convert combination using 1 <;> abel

def extendedPrimitive (subgroup : Subgroup GroupType)
    (representation : Representation ℂ GroupType Vector)
    (cocycle : cocycles subgroup representation) (primitive : subgroup → Vector) :
    cochains subgroup representation 1 := by
  refine ⟨fun vertices =>
    representation (cosetRetraction subgroup (vertices 0)).val
      (primitive ((cosetRetraction subgroup (vertices 0))⁻¹ *
        cosetRetraction subgroup (vertices 1))) +
      cocycle.val.val ![(cosetRetraction subgroup (vertices 0)).val, vertices 0, vertices 1] -
      cocycle.val.val ![(cosetRetraction subgroup (vertices 0)).val,
        (cosetRetraction subgroup (vertices 1)).val, vertices 1], ?_⟩
  intro matrix vertices
  simp only [cosetRetraction_equivariant, Subgroup.coe_mul,
    mul_inv_rev, mul_assoc, inv_mul_cancel_left,
    map_mul, Module.End.mul_apply]
  have first_equivariant := cocycle.val.property matrix
    (![(cosetRetraction subgroup (vertices 0)).val, vertices 0, vertices 1] : Fin 3 → GroupType)
  have second_equivariant := cocycle.val.property matrix
    (![(cosetRetraction subgroup (vertices 0)).val,
      (cosetRetraction subgroup (vertices 1)).val, vertices 1] : Fin 3 → GroupType)
  have translated_triple (first second third : GroupType) :
      (fun index => matrix.val * (![first, second, third] : Fin 3 → GroupType) index) =
        ![matrix.val * first, matrix.val * second, matrix.val * third] := by
    funext index
    fin_cases index <;> rfl
  rw [translated_triple] at first_equivariant second_equivariant
  rw [first_equivariant, second_equivariant, map_sub, map_add]

theorem extendedPrimitive_differential (subgroup : Subgroup GroupType)
    (representation : Representation ℂ GroupType Vector)
    (cocycle : cocycles subgroup representation) (primitive : subgroup → Vector)
    (differential : ∀ first second : subgroup,
      cocycle.val.val ![1, first.val, (first * second).val] =
        representation first.val (primitive second) - primitive (first * second) + primitive first) :
    differentialOne subgroup representation (extendedPrimitive subgroup representation cocycle primitive) =
      cocycle.val := by
  apply Subtype.ext
  funext vertices
  let first := cosetRetraction subgroup (vertices 0)
  let second := cosetRetraction subgroup (vertices 1)
  let third := cosetRetraction subgroup (vertices 2)
  have relation := differential (first⁻¹ * second) (second⁻¹ * third)
  have translated := cocycle.val.property first
    (![1, (first⁻¹ * second).val, ((first⁻¹ * second) * (second⁻¹ * third)).val] : Fin 3 → GroupType)
  rw [relation] at translated
  have translated_vertices :
      (fun index => first.val *
        (![1, (first⁻¹ * second).val, ((first⁻¹ * second) * (second⁻¹ * third)).val] :
          Fin 3 → GroupType) index) = ![first.val, second.val, third.val] := by
    funext index
    fin_cases index <;> simp [mul_assoc]
  rw [translated_vertices] at translated
  simp only [map_add, map_sub, ← Module.End.mul_apply, ← map_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left] at translated
  have homotopy := cocycle_retraction_homotopy subgroup representation cocycle
    (vertices 0) (vertices 1) (vertices 2)
  change (representation second.val (primitive (second⁻¹ * third)) +
      cocycle.val.val ![second.val, vertices 1, vertices 2] -
        cocycle.val.val ![second.val, third.val, vertices 2]) -
    (representation first.val (primitive (first⁻¹ * third)) +
      cocycle.val.val ![first.val, vertices 0, vertices 2] -
        cocycle.val.val ![first.val, third.val, vertices 2]) +
    (representation first.val (primitive (first⁻¹ * second)) +
      cocycle.val.val ![first.val, vertices 0, vertices 1] -
        cocycle.val.val ![first.val, second.val, vertices 1]) =
    cocycle.val.val vertices
  have eta : (![vertices 0, vertices 1, vertices 2] : Fin 3 → GroupType) = vertices := by
    funext index
    fin_cases index <;> rfl
  rw [eta] at homotopy
  change _ = cocycle.val.val vertices - cocycle.val.val ![first.val, second.val, third.val]
    at homotopy
  have combination := congrArg₂ (fun left right : Vector => left + right) translated.symm homotopy
  convert combination using 1 <;> abel

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
