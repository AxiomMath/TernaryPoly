module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Helpers

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

variable {GroupType : Type} [Group GroupType]

def normalizedRepresentative (subgroup : Subgroup GroupType) (coset : GroupType ⧸ subgroup) :
    GroupType := by
  classical
  exact if coset = QuotientGroup.mk 1 then 1 else coset.out

theorem normalizedRepresentative_mk (subgroup : Subgroup GroupType)
    (coset : GroupType ⧸ subgroup) :
    QuotientGroup.mk (normalizedRepresentative subgroup coset) = coset := by
  classical
  unfold normalizedRepresentative
  split_ifs with coset_identity
  · exact coset_identity.symm
  · exact QuotientGroup.out_eq' coset

def groupRetraction (subgroup : Subgroup GroupType) (element : GroupType) : subgroup :=
  ⟨element * normalizedRepresentative subgroup (QuotientGroup.mk element⁻¹), by
    have coset_equality := normalizedRepresentative_mk subgroup (QuotientGroup.mk element⁻¹)
    have in_subgroup := (QuotientGroup.eq.mp coset_equality)
    simpa only [mul_inv_rev, inv_inv] using subgroup.inv_mem in_subgroup⟩

theorem groupRetraction_subgroup (subgroup : Subgroup GroupType) (element : subgroup) :
    groupRetraction subgroup element.val = element := by
  classical
  apply Subtype.ext
  have coset_identity : (QuotientGroup.mk element.val⁻¹ : GroupType ⧸ subgroup) =
      QuotientGroup.mk 1 := by
    apply QuotientGroup.eq.mpr
    simp only [inv_inv, mul_one]
    exact element.property
  simp [groupRetraction, normalizedRepresentative, coset_identity]

theorem groupRetraction_equivariant (subgroup : Subgroup GroupType)
    (acting : subgroup) (element : GroupType) :
    groupRetraction subgroup (acting.val * element) = acting * groupRetraction subgroup element := by
  apply Subtype.ext
  have coset_eq : (QuotientGroup.mk (acting.val * element)⁻¹ : GroupType ⧸ subgroup) =
      QuotientGroup.mk element⁻¹ := by
    rw [mul_inv_rev]
    exact QuotientGroup.mk_mul_of_mem _ (subgroup.inv_mem acting.property)
  simp only [groupRetraction, coset_eq, Subgroup.coe_mul, mul_assoc]

variable {Coefficient : Type} [AddCommGroup Coefficient] [Module ℂ Coefficient]

def retractedCochain (subgroup : Subgroup GroupType)
    (representation : Representation ℂ GroupType Coefficient) (degree : ℕ)
    (cochain : cochains subgroup representation degree) : cochains subgroup representation degree :=
  ⟨fun vertices => cochain.val (fun index => (groupRetraction subgroup (vertices index)).val), by
    intro acting vertices
    have vertex_eq :
        (fun index => (groupRetraction subgroup (acting.val * vertices index)).val) =
          (fun index => acting.val * (groupRetraction subgroup (vertices index)).val) := by
      funext index
      rw [groupRetraction_equivariant, Subgroup.coe_mul]
    change cochain.val (fun index => (groupRetraction subgroup (acting.val * vertices index)).val) = _
    rw [vertex_eq]
    exact cochain.property acting _⟩

def cocycleHomotopy (subgroup : Subgroup GroupType)
    (representation : Representation ℂ GroupType Coefficient)
    (cocycle : cocycles subgroup representation) : cochains subgroup representation 1 :=
  ⟨fun vertices =>
    cocycle.val.val ![vertices 0, (groupRetraction subgroup (vertices 0)).val,
      (groupRetraction subgroup (vertices 1)).val] -
    cocycle.val.val ![vertices 0, vertices 1, (groupRetraction subgroup (vertices 1)).val], by
    intro acting vertices
    have translate_triple (first second third : GroupType) :
        cocycle.val.val ![acting.val * first, acting.val * second, acting.val * third] =
          representation acting.val (cocycle.val.val ![first, second, third]) := by
      have vertex_eq : (fun index => acting.val * ![first, second, third] index) =
          ![acting.val * first, acting.val * second, acting.val * third] := by
        funext index
        fin_cases index <;> rfl
      simpa only [vertex_eq] using cocycle.val.property acting ![first, second, third]
    change cocycle.val.val ![acting.val * vertices 0,
        (groupRetraction subgroup (acting.val * vertices 0)).val,
        (groupRetraction subgroup (acting.val * vertices 1)).val] -
      cocycle.val.val ![acting.val * vertices 0, acting.val * vertices 1,
        (groupRetraction subgroup (acting.val * vertices 1)).val] = _
    rw [groupRetraction_equivariant, groupRetraction_equivariant,
      Subgroup.coe_mul, Subgroup.coe_mul, translate_triple, translate_triple, map_sub]⟩

theorem cocycleHomotopy_differential (subgroup : Subgroup GroupType)
    (representation : Representation ℂ GroupType Coefficient)
    (cocycle : cocycles subgroup representation) :
    differentialOne subgroup representation (cocycleHomotopy subgroup representation cocycle) =
      retractedCochain subgroup representation 2 cocycle.val - cocycle.val := by
  apply Subtype.ext
  funext vertices
  have identity (first second third fourth : GroupType) :
      cocycle.val.val ![second, third, fourth] - cocycle.val.val ![first, third, fourth] +
        cocycle.val.val ![first, second, fourth] - cocycle.val.val ![first, second, third] = 0 := by
    have cocycle_zero : differentialTwo subgroup representation cocycle.val = 0 := cocycle.property
    exact congrFun cocycle_zero ![first, second, third, fourth]
  have first_identity := identity (vertices 0) (vertices 1)
    (groupRetraction subgroup (vertices 1)).val (groupRetraction subgroup (vertices 2)).val
  have second_identity := identity (vertices 0) (groupRetraction subgroup (vertices 0)).val
    (groupRetraction subgroup (vertices 1)).val (groupRetraction subgroup (vertices 2)).val
  have third_identity := identity (vertices 0) (vertices 1) (vertices 2)
    (groupRetraction subgroup (vertices 2)).val
  change
    (cocycle.val.val ![vertices 1, (groupRetraction subgroup (vertices 1)).val,
      (groupRetraction subgroup (vertices 2)).val] -
      cocycle.val.val ![vertices 1, vertices 2, (groupRetraction subgroup (vertices 2)).val]) -
    (cocycle.val.val ![vertices 0, (groupRetraction subgroup (vertices 0)).val,
      (groupRetraction subgroup (vertices 2)).val] -
      cocycle.val.val ![vertices 0, vertices 2, (groupRetraction subgroup (vertices 2)).val]) +
    (cocycle.val.val ![vertices 0, (groupRetraction subgroup (vertices 0)).val,
      (groupRetraction subgroup (vertices 1)).val] -
      cocycle.val.val ![vertices 0, vertices 1, (groupRetraction subgroup (vertices 1)).val]) =
    cocycle.val.val (fun index => (groupRetraction subgroup (vertices index)).val) -
      cocycle.val.val vertices
  have retracted_vertices : (fun index => (groupRetraction subgroup (vertices index)).val) =
      ![(groupRetraction subgroup (vertices 0)).val, (groupRetraction subgroup (vertices 1)).val,
        (groupRetraction subgroup (vertices 2)).val] := by
    funext index
    fin_cases index <;> rfl
  have original_vertices : vertices = ![vertices 0, vertices 1, vertices 2] := by
    funext index
    fin_cases index <;> rfl
  rw [retracted_vertices]
  conv_rhs => rw [original_vertices]
  have combined := congrArg₂ (fun first second : Coefficient => first - second)
    (congrArg₂ (fun first second : Coefficient => first - second)
      first_identity second_identity) third_identity
  simp only [sub_zero] at combined
  apply sub_eq_zero.mp
  convert combined using 1; abel_nf; ac_rfl

def pathCochain {degree : ℕ} (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (paths : rationalLevel → EdgeChains) :
    cochains rationalLevel (rationalCoefficientComponent degree trivialCharacter) 2 :=
  ⟨fun vertices =>
    let first := groupRetraction rationalLevel (vertices 0)
    let second := groupRetraction rationalLevel (vertices 1)
    let third := groupRetraction rationalLevel (vertices 2)
    rationalCoefficientComponent degree trivialCharacter first.val
      (functional (pathDefect paths (first⁻¹ * second) (second⁻¹ * third))), by
    intro acting vertices
    simp only [groupRetraction_equivariant, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left, Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩

theorem pathCochain_cocycle {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {paths : rationalLevel → EdgeChains} (paths_good : IsPathFamily paths) :
    differentialTwo rationalLevel (rationalCoefficientComponent degree trivialCharacter)
      (pathCochain functional paths) = 0 := by
  funext vertices
  let first := groupRetraction rationalLevel (vertices 0)
  let second := groupRetraction rationalLevel (vertices 1)
  let third := groupRetraction rationalLevel (vertices 2)
  let fourth := groupRetraction rationalLevel (vertices 3)
  have coefficient := pathDefect_cocycle functional_property paths_good
    (first⁻¹ * second) (second⁻¹ * third) (third⁻¹ * fourth)
  have acted := congrArg (rationalCoefficientComponent degree trivialCharacter first.val) coefficient
  simp only [map_sub, map_add, map_zero, ← Module.End.mul_apply, ← map_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left, mul_assoc,
    ] at acted
  exact acted

def pathCocycle {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {paths : rationalLevel → EdgeChains} (paths_good : IsPathFamily paths) :
    cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter) :=
  ⟨pathCochain functional paths, pathCochain_cocycle functional_property paths_good⟩

theorem pathCocycle_realizes {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {paths : rationalLevel → EdgeChains} (paths_good : IsPathFamily paths) :
    RealizesPathClass functional paths (pathCocycle functional_property paths_good) := by
  intro first second third
  change rationalCoefficientComponent degree trivialCharacter
    (groupRetraction rationalLevel first.val).val
      (functional (pathDefect paths
        ((groupRetraction rationalLevel first.val)⁻¹ * groupRetraction rationalLevel second.val)
        ((groupRetraction rationalLevel second.val)⁻¹ * groupRetraction rationalLevel third.val))) = _
  rw [groupRetraction_subgroup, groupRetraction_subgroup, groupRetraction_subgroup]
  simp only [pathDefect, mul_assoc, mul_inv_cancel_left]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
