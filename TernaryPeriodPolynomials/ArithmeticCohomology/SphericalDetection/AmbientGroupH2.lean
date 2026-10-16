module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AmbientCochainHomotopy
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Order.Fin.SuccAboveOrderIso

@[expose] public section


open GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def subgroupCoefficientRep (subgroup : Subgroup G) (representation : Representation ℂ G V) : Rep ℂ subgroup :=
  Rep.of (representation.comp subgroup.subtype)

def ambientCocycleToGroup (subgroup : Subgroup G) (representation : Representation ℂ G V) :
    cocycles subgroup representation →ₗ[ℂ] groupCohomology.cocycles₂ (subgroupCoefficientRep subgroup representation) where
  toFun cycle := ⟨fun pair => cycle.val.val ![1, pair.1.val, pair.1.val * pair.2.val], by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro first second third
    have relation := homogeneousTwoCycle_relation subgroup representation cycle
      1 first.val (first.val * second.val) (first.val * second.val * third.val)
    have equivariance := homogeneousTwoCochain_equivariant subgroup representation cycle.val first
      1 second.val (second.val * third.val)
    rw [mul_one] at equivariance
    rw [mul_assoc, equivariance] at relation
    change cycle.val.val ![1, first.val * second.val, first.val * second.val * third.val] +
      cycle.val.val ![1, first.val, first.val * second.val] =
      representation first.val (cycle.val.val ![1, second.val, second.val * third.val]) +
        cycle.val.val ![1, first.val, first.val * (second.val * third.val)]
    rw [mul_assoc]
    linear_combination (norm := abel) -relation⟩
  map_add' first second := by
    apply Subtype.ext
    rfl
  map_smul' scalar cycle := by
    apply Subtype.ext
    rfl

theorem ambientCocycleToGroup_apply (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cycle : cocycles subgroup representation) (first second : subgroup) :
    ambientCocycleToGroup subgroup representation cycle (first, second) =
      cycle.val.val ![1, first.val, first.val * second.val] := rfl

def retractedGroupPrimitive (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (primitive : subgroup → V) : cochains subgroup representation 1 :=
  ⟨fun vertices => representation (subgroupVertexProjection subgroup (vertices 0)).val
    (primitive ((subgroupVertexProjection subgroup (vertices 0))⁻¹ * subgroupVertexProjection subgroup (vertices 1))), by
    intro member vertices
    change representation (subgroupVertexProjection subgroup (member.val * vertices 0)).val
      (primitive ((subgroupVertexProjection subgroup (member.val * vertices 0))⁻¹ *
        subgroupVertexProjection subgroup (member.val * vertices 1))) = _
    rw [subgroupVertexProjection_equivariant, subgroupVertexProjection_equivariant]
    simp only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left, Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩

theorem retractedGroupPrimitive_differential (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cycle : cocycles subgroup representation) (primitive : subgroup → V)
    (boundary : ∀ first second : subgroup,
      representation first.val (primitive second) - primitive (first * second) + primitive first =
        ambientCocycleToGroup subgroup representation cycle (first, second))
    (vertices : Fin 3 → G) :
    (differentialOne subgroup representation (retractedGroupPrimitive subgroup representation primitive)).val vertices =
      cycle.val.val (fun index => (subgroupVertexProjection subgroup (vertices index)).val) := by
  let first := subgroupVertexProjection subgroup (vertices 0)
  let second := subgroupVertexProjection subgroup (vertices 1)
  let third := subgroupVertexProjection subgroup (vertices 2)
  have equation := congrArg (representation first.val) (boundary (first⁻¹ * second) (second⁻¹ * third))
  have equivariance := homogeneousTwoCochain_equivariant subgroup representation cycle.val first
    1 (first⁻¹ * second).val ((first⁻¹ * second).val * (second⁻¹ * third).val)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left,
    mul_one] at equivariance
  rw [ambientCocycleToGroup_apply, map_add, map_sub] at equation
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left] at equation
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at equation
  rw [← equivariance] at equation
  have tuple : ![first.val, second.val, third.val] =
      fun index => (subgroupVertexProjection subgroup (vertices index)).val := by
    funext index
    fin_cases index <;> rfl
  rw [tuple] at equation
  exact equation

theorem ambientCocycle_primitive_of_H2_zero (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cycle : cocycles subgroup representation)
    (zero : groupCohomology.H2π (subgroupCoefficientRep subgroup representation)
      (ambientCocycleToGroup subgroup representation cycle) = 0) :
    ∃ primitive : cochains subgroup representation 1, differentialOne subgroup representation primitive = cycle.val := by
  rw [groupCohomology.H2π_eq_zero_iff] at zero
  obtain ⟨primitive, boundary⟩ := zero
  change subgroup → V at primitive
  have equation (first second : subgroup) :
      representation first.val (primitive second) - primitive (first * second) + primitive first =
        ambientCocycleToGroup subgroup representation cycle (first, second) :=
    congrFun boundary (first, second)
  refine ⟨retractedGroupPrimitive subgroup representation primitive +
    ambientCocycleHomotopy subgroup representation cycle, ?_⟩
  apply Subtype.ext
  funext vertices
  rw [map_add]
  change (differentialOne subgroup representation (retractedGroupPrimitive subgroup representation primitive)).val vertices +
    (differentialOne subgroup representation (ambientCocycleHomotopy subgroup representation cycle)).val vertices = _
  rw [retractedGroupPrimitive_differential subgroup representation cycle primitive equation,
    ambientCocycleHomotopy_differential]
  abel

theorem homogeneousOneCochain_equivariant (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cochain : cochains subgroup representation 1) (member : subgroup) (first second : G) :
    cochain.val ![member.val * first, member.val * second] = representation member.val (cochain.val ![first, second]) := by
  have tuple : (fun index : Fin 2 => member.val * ![first, second] index) =
      ![member.val * first, member.val * second] := by
    funext index
    fin_cases index <;> rfl
  simpa only [tuple] using cochain.property member ![first, second]

theorem ambientCocycle_H2_zero_of_primitive (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cycle : cocycles subgroup representation) (primitive : cochains subgroup representation 1)
    (boundary : differentialOne subgroup representation primitive = cycle.val) :
    groupCohomology.H2π (subgroupCoefficientRep subgroup representation)
      (ambientCocycleToGroup subgroup representation cycle) = 0 := by
  rw [groupCohomology.H2π_eq_zero_iff]
  refine ⟨fun element => primitive.val ![1, element.val], ?_⟩
  funext pair
  have equation := congrArg (fun cochain : cochains subgroup representation 2 =>
    cochain.val ![1, pair.1.val, pair.1.val * pair.2.val]) boundary
  have equivariance := homogeneousOneCochain_equivariant subgroup representation primitive pair.1 1 pair.2.val
  rw [mul_one] at equivariance
  change primitive.val ![pair.1.val, pair.1.val * pair.2.val] -
    primitive.val ![1, pair.1.val * pair.2.val] + primitive.val ![1, pair.1.val] = _ at equation
  rw [equivariance] at equation
  exact equation

theorem ambientCocycle_H2_zero_iff (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cycle : cocycles subgroup representation) :
    groupCohomology.H2π (subgroupCoefficientRep subgroup representation)
        (ambientCocycleToGroup subgroup representation cycle) = 0 ↔
      ∃ primitive : cochains subgroup representation 1, differentialOne subgroup representation primitive = cycle.val := by
  constructor
  · exact ambientCocycle_primitive_of_H2_zero subgroup representation cycle
  · rintro ⟨primitive, boundary⟩
    exact ambientCocycle_H2_zero_of_primitive subgroup representation cycle primitive boundary

end TernaryPeriodPolynomials.SphericalDetection.Helpers
