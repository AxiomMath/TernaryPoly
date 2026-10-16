module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Cochains

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

variable {GroupType Coefficient : Type} [Group GroupType]
  [AddCommGroup Coefficient] [Module ℂ Coefficient]

theorem classOf_eq_of_differential (subgroup : Subgroup GroupType)
    (representation : Representation ℂ GroupType Coefficient)
    (first second : cocycles subgroup representation)
    (cochain : cochains subgroup representation 1)
    (difference : differentialOne subgroup representation cochain = first.val - second.val) :
    classOf subgroup representation first = classOf subgroup representation second := by
  apply (Submodule.Quotient.eq (LinearMap.range (boundaryMap subgroup representation))).mpr
  refine ⟨cochain, ?_⟩
  apply Subtype.ext
  exact difference

theorem cocycle_class_eq_of_agreement (subgroup : Subgroup GroupType)
    (representation : Representation ℂ GroupType Coefficient)
    (first second : cocycles subgroup representation)
    (agreement : ∀ first_vertex second_vertex third_vertex : subgroup,
      first.val.val ![first_vertex.val, second_vertex.val, third_vertex.val] =
        second.val.val ![first_vertex.val, second_vertex.val, third_vertex.val]) :
    classOf subgroup representation first = classOf subgroup representation second := by
  apply classOf_eq_of_differential subgroup representation first second
    (cocycleHomotopy subgroup representation second -
      cocycleHomotopy subgroup representation first)
  rw [map_sub, cocycleHomotopy_differential, cocycleHomotopy_differential]
  have retracted_eq : retractedCochain subgroup representation 2 first.val =
      retractedCochain subgroup representation 2 second.val := by
    apply Subtype.ext
    funext vertices
    have vertices_eq :
        (fun index => (groupRetraction subgroup (vertices index)).val) =
          ![(groupRetraction subgroup (vertices 0)).val,
            (groupRetraction subgroup (vertices 1)).val,
            (groupRetraction subgroup (vertices 2)).val] := by
      funext index
      fin_cases index <;> rfl
    change first.val.val (fun index => (groupRetraction subgroup (vertices index)).val) =
      second.val.val (fun index => (groupRetraction subgroup (vertices index)).val)
    rw [vertices_eq]
    exact agreement _ _ _
  rw [retracted_eq]
  abel

def pathDifferenceCochain {degree : ℕ}
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (first_paths second_paths : rationalLevel → EdgeChains) :
    cochains rationalLevel (rationalCoefficientComponent degree trivialCharacter) 1 :=
  ⟨fun vertices =>
    let first := groupRetraction rationalLevel (vertices 0)
    let second := groupRetraction rationalLevel (vertices 1)
    rationalCoefficientComponent degree trivialCharacter first.val
      (functional (first_paths (first⁻¹ * second) - second_paths (first⁻¹ * second))), by
    intro acting vertices
    simp only [groupRetraction_equivariant, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left, Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩

theorem pathDifferenceCochain_differential {degree : ℕ}
    {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {first_paths second_paths : rationalLevel → EdgeChains}
    (first_good : IsPathFamily first_paths) (second_good : IsPathFamily second_paths) :
    differentialOne rationalLevel (rationalCoefficientComponent degree trivialCharacter)
      (pathDifferenceCochain functional first_paths second_paths) =
        pathCochain functional first_paths - pathCochain functional second_paths := by
  apply Subtype.ext
  funext vertices
  let first := groupRetraction rationalLevel (vertices 0)
  let second := groupRetraction rationalLevel (vertices 1)
  let third := groupRetraction rationalLevel (vertices 2)
  have equivariance := functional_property.1 (first⁻¹ * second)
    (first_paths (second⁻¹ * third) - second_paths (second⁻¹ * third))
    (path_difference_goodCycle first_good second_good (second⁻¹ * third))
  have translated := congrArg
    (rationalCoefficientComponent degree trivialCharacter first.val) equivariance
  simp only [← Module.End.mul_apply, ← map_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    mul_inv_cancel_left] at translated
  change rationalCoefficientComponent degree trivialCharacter second.val
      (functional (first_paths (second⁻¹ * third) - second_paths (second⁻¹ * third))) -
    rationalCoefficientComponent degree trivialCharacter first.val
      (functional (first_paths (first⁻¹ * third) - second_paths (first⁻¹ * third))) +
    rationalCoefficientComponent degree trivialCharacter first.val
      (functional (first_paths (first⁻¹ * second) - second_paths (first⁻¹ * second))) = _
  rw [← translated]
  change rationalCoefficientComponent degree trivialCharacter first.val
      (functional (translateChain (first⁻¹ * second).val
        (first_paths (second⁻¹ * third) - second_paths (second⁻¹ * third)))) -
    rationalCoefficientComponent degree trivialCharacter first.val
      (functional (first_paths (first⁻¹ * third) - second_paths (first⁻¹ * third))) +
    rationalCoefficientComponent degree trivialCharacter first.val
      (functional (first_paths (first⁻¹ * second) - second_paths (first⁻¹ * second))) =
    rationalCoefficientComponent degree trivialCharacter first.val
      (functional (pathDefect first_paths (first⁻¹ * second) (second⁻¹ * third))) -
    rationalCoefficientComponent degree trivialCharacter first.val
      (functional (pathDefect second_paths (first⁻¹ * second) (second⁻¹ * third)))
  simp only [pathDefect, map_sub, map_add, mul_assoc, mul_inv_cancel_left]
  abel

theorem pathCocycle_class_independent {degree : ℕ}
    {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {first_paths second_paths : rationalLevel → EdgeChains}
    (first_good : IsPathFamily first_paths) (second_good : IsPathFamily second_paths) :
    classOf rationalLevel (rationalCoefficientComponent degree trivialCharacter)
        (pathCocycle functional_property first_good) =
      classOf rationalLevel (rationalCoefficientComponent degree trivialCharacter)
        (pathCocycle functional_property second_good) := by
  exact classOf_eq_of_differential _ _ _ _
    (pathDifferenceCochain functional first_paths second_paths)
    (pathDifferenceCochain_differential functional_property first_good second_good)

theorem realizesPathClass_class_independent {degree : ℕ}
    {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {first_paths second_paths : rationalLevel → EdgeChains}
    (first_good : IsPathFamily first_paths) (second_good : IsPathFamily second_paths)
    {first_cocycle second_cocycle :
      cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (first_realizes : RealizesPathClass functional first_paths first_cocycle)
    (second_realizes : RealizesPathClass functional second_paths second_cocycle) :
    classOf rationalLevel (rationalCoefficientComponent degree trivialCharacter) first_cocycle =
      classOf rationalLevel (rationalCoefficientComponent degree trivialCharacter) second_cocycle := by
  have first_agreement := cocycle_class_eq_of_agreement rationalLevel
    (rationalCoefficientComponent degree trivialCharacter) first_cocycle
    (pathCocycle functional_property first_good) (by
      intro first second third
      rw [first_realizes, pathCocycle_realizes functional_property first_good])
  have second_agreement := cocycle_class_eq_of_agreement rationalLevel
    (rationalCoefficientComponent degree trivialCharacter) second_cocycle
    (pathCocycle functional_property second_good) (by
      intro first second third
      rw [second_realizes, pathCocycle_realizes functional_property second_good])
  exact first_agreement.trans
    ((pathCocycle_class_independent functional_property first_good second_good).trans
      second_agreement.symm)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
