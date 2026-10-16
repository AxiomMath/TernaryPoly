module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Cocycle

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {GroupType Value : Type} [Group GroupType]
  [AddCommGroup Value] [Module ℂ Value]
  (representation : Representation ℂ GroupType Value)

theorem fullOneCochain_coordinate
    (cochain : cochains (⊤ : Subgroup GroupType) representation 1)
    (first second : GroupType) :
    cochain.val ![first, second] =
      representation first (cochain.val ![1, first⁻¹ * second]) := by
  have vertices_eq : (fun index => first * ![1, first⁻¹ * second] index) =
      ![first, second] := by
    funext index
    fin_cases index <;> simp
  simpa only [vertices_eq] using
    cochain.property ⟨first, trivial⟩ ![1, first⁻¹ * second]

theorem fullTwoCochain_coordinate
    (cochain : cochains (⊤ : Subgroup GroupType) representation 2)
    (first second third : GroupType) :
    cochain.val ![first, second, third] =
      representation first (cochain.val ![1, first⁻¹ * second, first⁻¹ * third]) := by
  have vertices_eq : (fun index => first * ![1, first⁻¹ * second, first⁻¹ * third] index) =
      ![first, second, third] := by
    funext index
    fin_cases index <;> simp
  simpa only [vertices_eq] using
    cochain.property ⟨first, trivial⟩ ![1, first⁻¹ * second, first⁻¹ * third]

def fullOneInhomogeneousEquiv :
    cochains (⊤ : Subgroup GroupType) representation 1 ≃ₗ[ℂ] (GroupType → Value) where
  toFun cochain element := cochain.val ![1, element]
  invFun cochain := ⟨fun vertices =>
    representation (vertices 0) (cochain ((vertices 0)⁻¹ * vertices 1)), by
    intro element vertices
    change representation (element.val * vertices 0)
        (cochain ((element.val * vertices 0)⁻¹ * (element.val * vertices 1))) =
      representation element.val
        (representation (vertices 0) (cochain ((vertices 0)⁻¹ * vertices 1)))
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul, Module.End.mul_apply]⟩
  left_inv cochain := by
    apply Subtype.ext
    funext vertices
    have vertices_eq : ![vertices 0, vertices 1] = vertices := by
      funext index
      fin_cases index <;> rfl
    simpa only [vertices_eq] using
      (fullOneCochain_coordinate representation cochain (vertices 0) (vertices 1)).symm
  right_inv cochain := by
    funext element
    change representation 1 (cochain (1⁻¹ * element)) = cochain element
    simp
  map_add' first second := rfl
  map_smul' scalar cochain := rfl

def fullTwoInhomogeneousEquiv :
    cochains (⊤ : Subgroup GroupType) representation 2 ≃ₗ[ℂ]
      (GroupType → GroupType → Value) where
  toFun cochain first second := cochain.val ![1, first, first * second]
  invFun cochain := ⟨fun vertices =>
    representation (vertices 0)
      (cochain ((vertices 0)⁻¹ * vertices 1) ((vertices 1)⁻¹ * vertices 2)), by
    intro element vertices
    change representation (element.val * vertices 0)
        (cochain ((element.val * vertices 0)⁻¹ * (element.val * vertices 1))
          ((element.val * vertices 1)⁻¹ * (element.val * vertices 2))) =
      representation element.val
        (representation (vertices 0)
          (cochain ((vertices 0)⁻¹ * vertices 1) ((vertices 1)⁻¹ * vertices 2)))
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul, Module.End.mul_apply]⟩
  left_inv cochain := by
    apply Subtype.ext
    funext vertices
    have vertices_eq : ![vertices 0, vertices 1, vertices 2] = vertices := by
      funext index
      fin_cases index <;> rfl
    simpa only [mul_assoc, mul_inv_cancel_left, vertices_eq] using
      (fullTwoCochain_coordinate representation cochain
        (vertices 0) (vertices 1) (vertices 2)).symm
  right_inv cochain := by
    funext first second
    change representation 1 (cochain (1⁻¹ * first) (first⁻¹ * (first * second))) =
      cochain first second
    simp
  map_add' first second := rfl
  map_smul' scalar cochain := rfl

def inhomogeneousBoundaryMap :
    (GroupType → Value) →ₗ[ℂ] inhomogeneousTwoCycles representation where
  toFun cochain := ⟨fun first second =>
    representation first (cochain second) - cochain (first * second) + cochain first, by
    intro first second third
    change representation first
        (representation second (cochain third) - cochain (second * third) + cochain second) -
      (representation (first * second) (cochain third) -
        cochain ((first * second) * third) + cochain (first * second)) +
      (representation first (cochain (second * third)) -
        cochain (first * (second * third)) + cochain first) -
      (representation first (cochain second) - cochain (first * second) + cochain first) = 0
    rw [map_add, map_sub, map_mul, Module.End.mul_apply, mul_assoc]
    abel⟩
  map_add' first second := by
    apply Subtype.ext
    funext elementOne elementTwo
    change representation elementOne (first elementTwo + second elementTwo) -
        (first (elementOne * elementTwo) + second (elementOne * elementTwo)) +
        (first elementOne + second elementOne) =
      (representation elementOne (first elementTwo) -
        first (elementOne * elementTwo) + first elementOne) +
      (representation elementOne (second elementTwo) -
        second (elementOne * elementTwo) + second elementOne)
    rw [map_add]
    abel
  map_smul' scalar cochain := by
    apply Subtype.ext
    funext first second
    change representation first (scalar • cochain second) -
        scalar • cochain (first * second) + scalar • cochain first =
      scalar • (representation first (cochain second) - cochain (first * second) + cochain first)
    rw [map_smul, smul_add, smul_sub]

theorem fullTwoInhomogeneousEquiv_differentialOne
    (cochain : cochains (⊤ : Subgroup GroupType) representation 1) :
    fullTwoInhomogeneousEquiv representation
        (differentialOne (⊤ : Subgroup GroupType) representation cochain) =
      (inhomogeneousBoundaryMap representation
        (fullOneInhomogeneousEquiv representation cochain)).val := by
  funext first second
  change cochain.val ![first, first * second] - cochain.val ![1, first * second] +
      cochain.val ![1, first] =
    representation first (cochain.val ![1, second]) - cochain.val ![1, first * second] +
      cochain.val ![1, first]
  rw [fullOneCochain_coordinate representation cochain first (first * second),
    inv_mul_cancel_left]

theorem fullTwoInhomogeneousEquiv_cycle_iff
    (cochain : cochains (⊤ : Subgroup GroupType) representation 2) :
    fullTwoInhomogeneousEquiv representation cochain ∈ inhomogeneousTwoCycles representation ↔
      cochain ∈ cocycles (⊤ : Subgroup GroupType) representation := by
  constructor
  · intro cycle
    change differentialTwo (⊤ : Subgroup GroupType) representation cochain = 0
    funext vertices
    have identity := cycle ((vertices 0)⁻¹ * vertices 1)
      ((vertices 1)⁻¹ * vertices 2) ((vertices 2)⁻¹ * vertices 3)
    have mapped := congrArg (representation (vertices 0)) identity
    change representation (vertices 0)
        (representation ((vertices 0)⁻¹ * vertices 1)
            (cochain.val ![1, (vertices 1)⁻¹ * vertices 2,
              ((vertices 1)⁻¹ * vertices 2) * ((vertices 2)⁻¹ * vertices 3)]) -
          cochain.val ![1, ((vertices 0)⁻¹ * vertices 1) * ((vertices 1)⁻¹ * vertices 2),
            (((vertices 0)⁻¹ * vertices 1) * ((vertices 1)⁻¹ * vertices 2)) *
              ((vertices 2)⁻¹ * vertices 3)] +
          cochain.val ![1, (vertices 0)⁻¹ * vertices 1,
            ((vertices 0)⁻¹ * vertices 1) *
              (((vertices 1)⁻¹ * vertices 2) * ((vertices 2)⁻¹ * vertices 3))] -
          cochain.val ![1, (vertices 0)⁻¹ * vertices 1,
            ((vertices 0)⁻¹ * vertices 1) * ((vertices 1)⁻¹ * vertices 2)]) =
        representation (vertices 0) 0 at mapped
    simp only [map_sub, map_add, map_zero, mul_assoc, mul_inv_cancel_left,
      ← Module.End.mul_apply, ← map_mul] at mapped
    change cochain.val ![vertices 1, vertices 2, vertices 3] -
      cochain.val ![vertices 0, vertices 2, vertices 3] +
      cochain.val ![vertices 0, vertices 1, vertices 3] -
      cochain.val ![vertices 0, vertices 1, vertices 2] = 0
    rw [fullTwoCochain_coordinate representation cochain (vertices 1),
      fullTwoCochain_coordinate representation cochain (vertices 0),
      fullTwoCochain_coordinate representation cochain (vertices 0),
      fullTwoCochain_coordinate representation cochain (vertices 0)]
    exact mapped
  · intro cycle first second third
    change representation first (cochain.val ![1, second, second * third]) -
      cochain.val ![1, first * second, (first * second) * third] +
      cochain.val ![1, first, first * (second * third)] -
      cochain.val ![1, first, first * second] = 0
    have identity := congrFun cycle ![1, first, first * second, (first * second) * third]
    change cochain.val ![first, first * second, (first * second) * third] -
      cochain.val ![1, first * second, (first * second) * third] +
      cochain.val ![1, first, (first * second) * third] -
      cochain.val ![1, first, first * second] = 0 at identity
    rw [fullTwoCochain_coordinate representation cochain first,
      inv_mul_cancel_left] at identity
    simpa only [mul_assoc, inv_mul_cancel_left] using identity

def fullInhomogeneousCycleEquiv :
    cocycles (⊤ : Subgroup GroupType) representation ≃ₗ[ℂ]
      inhomogeneousTwoCycles representation where
  toFun cycle := ⟨fullTwoInhomogeneousEquiv representation cycle.val,
    (fullTwoInhomogeneousEquiv_cycle_iff representation cycle.val).mpr cycle.property⟩
  invFun cycle := ⟨(fullTwoInhomogeneousEquiv representation).symm cycle.val,
    (fullTwoInhomogeneousEquiv_cycle_iff representation _).mp
      (by simpa only [LinearEquiv.apply_symm_apply] using cycle.property)⟩
  left_inv cycle := by
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply _ _
  right_inv cycle := by
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply _ _
  map_add' first second := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' scalar cycle := by
    apply Subtype.ext
    exact map_smul _ _ _

theorem fullInhomogeneousCycleEquiv_boundaryMap
    (cochain : cochains (⊤ : Subgroup GroupType) representation 1) :
    fullInhomogeneousCycleEquiv representation
        (boundaryMap (⊤ : Subgroup GroupType) representation cochain) =
      inhomogeneousBoundaryMap representation
        (fullOneInhomogeneousEquiv representation cochain) := by
  apply Subtype.ext
  exact fullTwoInhomogeneousEquiv_differentialOne representation cochain

def inhomogeneousBoundaries : Submodule ℂ (inhomogeneousTwoCycles representation) :=
  (inhomogeneousBoundaryMap representation).range

abbrev InhomogeneousH2 :=
  inhomogeneousTwoCycles representation ⧸ inhomogeneousBoundaries representation

theorem fullInhomogeneousCycleEquiv_boundaries :
    (boundaryMap (⊤ : Subgroup GroupType) representation).range.map
        (fullInhomogeneousCycleEquiv representation).toLinearMap =
      inhomogeneousBoundaries representation := by
  apply le_antisymm
  · rintro cycle ⟨previous, ⟨cochain, rfl⟩, rfl⟩
    exact ⟨fullOneInhomogeneousEquiv representation cochain,
      (fullInhomogeneousCycleEquiv_boundaryMap representation cochain).symm⟩
  · rintro cycle ⟨cochain, rfl⟩
    refine ⟨boundaryMap (⊤ : Subgroup GroupType) representation
        ((fullOneInhomogeneousEquiv representation).symm cochain), ⟨_, rfl⟩, ?_⟩
    change fullInhomogeneousCycleEquiv representation
        (boundaryMap (⊤ : Subgroup GroupType) representation
          ((fullOneInhomogeneousEquiv representation).symm cochain)) =
      inhomogeneousBoundaryMap representation cochain
    rw [fullInhomogeneousCycleEquiv_boundaryMap, LinearEquiv.apply_symm_apply]

def fullInhomogeneousH2Equiv :
    H2 (⊤ : Subgroup GroupType) representation ≃ₗ[ℂ] InhomogeneousH2 representation :=
  Submodule.Quotient.equiv _ _ (fullInhomogeneousCycleEquiv representation)
    (fullInhomogeneousCycleEquiv_boundaries representation)

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
