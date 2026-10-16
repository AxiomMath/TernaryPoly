module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


open GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- A subgroup-equivariant choice of a subgroup vertex for every ambient vertex. -/
def subgroupVertexProjection (subgroup : Subgroup G) (element : G) : subgroup :=
  ⟨element * Quotient.out (QuotientGroup.mk element⁻¹ : G ⧸ subgroup), by
    obtain ⟨member, equality⟩ := QuotientGroup.mk_out_eq_mul subgroup element⁻¹
    rw [equality, mul_inv_cancel_left]
    exact member.property⟩

theorem subgroupVertexProjection_equivariant (subgroup : Subgroup G) (member : subgroup) (element : G) :
    subgroupVertexProjection subgroup (member.val * element) = member * subgroupVertexProjection subgroup element := by
  have same : (QuotientGroup.mk (member.val * element)⁻¹ : G ⧸ subgroup) = QuotientGroup.mk element⁻¹ := by
    rw [QuotientGroup.eq]
    simpa only [inv_inv, mul_assoc, mul_inv_cancel, mul_one] using member.property
  apply Subtype.ext
  change (member.val * element) * Quotient.out (QuotientGroup.mk (member.val * element)⁻¹ : G ⧸ subgroup) =
    member.val * (element * Quotient.out (QuotientGroup.mk element⁻¹ : G ⧸ subgroup))
  rw [same, mul_assoc]

theorem homogeneousTwoCochain_equivariant (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cochain : cochains subgroup representation 2) (member : subgroup) (first second third : G) :
    cochain.val ![member.val * first, member.val * second, member.val * third] =
      representation member.val (cochain.val ![first, second, third]) := by
  have tuple : (fun index : Fin 3 => member.val * ![first, second, third] index) =
      ![member.val * first, member.val * second, member.val * third] := by
    funext index
    fin_cases index <;> rfl
  simpa only [tuple] using cochain.property member ![first, second, third]

theorem homogeneousTwoCycle_relation (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cycle : cocycles subgroup representation) (first second third fourth : G) :
    cycle.val.val ![second, third, fourth] - cycle.val.val ![first, third, fourth] +
      cycle.val.val ![first, second, fourth] - cycle.val.val ![first, second, third] = 0 :=
  congrFun cycle.property ![first, second, third, fourth]

def ambientCocycleHomotopy (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cycle : cocycles subgroup representation) : cochains subgroup representation 1 :=
  ⟨fun vertices =>
    cycle.val.val ![(subgroupVertexProjection subgroup (vertices 0)).val, vertices 0, vertices 1] -
      cycle.val.val ![(subgroupVertexProjection subgroup (vertices 0)).val,
        (subgroupVertexProjection subgroup (vertices 1)).val, vertices 1], by
    intro member vertices
    change cycle.val.val ![(subgroupVertexProjection subgroup (member.val * vertices 0)).val,
        member.val * vertices 0, member.val * vertices 1] -
      cycle.val.val ![(subgroupVertexProjection subgroup (member.val * vertices 0)).val,
        (subgroupVertexProjection subgroup (member.val * vertices 1)).val, member.val * vertices 1] = _
    rw [subgroupVertexProjection_equivariant, subgroupVertexProjection_equivariant]
    simp only [Subgroup.coe_mul, homogeneousTwoCochain_equivariant, map_sub]⟩

/-- The prism identity compares the ambient resolution with its subgroup vertices. -/
theorem ambientCocycleHomotopy_differential (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cycle : cocycles subgroup representation) (vertices : Fin 3 → G) :
    (differentialOne subgroup representation (ambientCocycleHomotopy subgroup representation cycle)).val vertices =
      cycle.val.val vertices - cycle.val.val (fun index => (subgroupVertexProjection subgroup (vertices index)).val) := by
  let first := (subgroupVertexProjection subgroup (vertices 0)).val
  let second := (subgroupVertexProjection subgroup (vertices 1)).val
  let third := (subgroupVertexProjection subgroup (vertices 2)).val
  have relation0 := homogeneousTwoCycle_relation subgroup representation cycle first (vertices 0) (vertices 1) (vertices 2)
  have relation1 := homogeneousTwoCycle_relation subgroup representation cycle first second (vertices 1) (vertices 2)
  have relation2 := homogeneousTwoCycle_relation subgroup representation cycle first second third (vertices 2)
  have tuple : ![vertices 0, vertices 1, vertices 2] = vertices := by
    funext index
    fin_cases index <;> rfl
  have retracted : ![first, second, third] = fun index => (subgroupVertexProjection subgroup (vertices index)).val := by
    funext index
    fin_cases index <;> rfl
  rw [tuple] at relation0
  rw [← retracted]
  change (cycle.val.val ![second, vertices 1, vertices 2] - cycle.val.val ![second, third, vertices 2]) -
      (cycle.val.val ![first, vertices 0, vertices 2] - cycle.val.val ![first, third, vertices 2]) +
      (cycle.val.val ![first, vertices 0, vertices 1] - cycle.val.val ![first, second, vertices 1]) = _
  linear_combination (norm := abel) -relation0 + relation1 - relation2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
