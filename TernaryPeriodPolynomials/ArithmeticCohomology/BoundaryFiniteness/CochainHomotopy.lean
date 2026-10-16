module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


open GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryFiniteness.CochainHomotopy

noncomputable section

variable {G Space : Type} [Group G] [AddCommGroup Space] [Module ℂ Space]

theorem cocycle_on_four (level : Subgroup G) (action : Representation ℂ G Space)
    (cocycle : cocycles level action) (a b c d : G) :
    cocycle.val.val ![b, c, d] - cocycle.val.val ![a, c, d] +
      cocycle.val.val ![a, b, d] - cocycle.val.val ![a, b, c] = 0 :=
  congrFun cocycle.property ![a, b, c, d]

def rightTranslationHomotopy (level : Subgroup G) (action : Representation ℂ G Space)
    (element : G) (cocycle : cocycles level action) : cochains level action 1 :=
  ⟨fun vertices =>
    cocycle.val.val ![vertices 0 * element, vertices 0, vertices 1] -
      cocycle.val.val ![vertices 0 * element, vertices 1 * element, vertices 1], by
    intro subgroup_element vertices
    have equivariance (a b c : G) :
        cocycle.val.val ![subgroup_element.val * a, subgroup_element.val * b,
            subgroup_element.val * c] =
          action subgroup_element.val (cocycle.val.val ![a, b, c]) := by
      have equality : (fun index => subgroup_element.val * ![a, b, c] index) =
          ![subgroup_element.val * a, subgroup_element.val * b, subgroup_element.val * c] := by
        funext index
        fin_cases index <;> rfl
      exact equality ▸ cocycle.val.property subgroup_element ![a, b, c]
    change cocycle.val.val ![(subgroup_element.val * vertices 0) * element,
        subgroup_element.val * vertices 0, subgroup_element.val * vertices 1] -
      cocycle.val.val ![(subgroup_element.val * vertices 0) * element,
        (subgroup_element.val * vertices 1) * element, subgroup_element.val * vertices 1] = _
    rw [mul_assoc, mul_assoc, equivariance, equivariance, map_sub]⟩

theorem rightTranslationHomotopy_formula (level : Subgroup G)
    (action : Representation ℂ G Space) (element : G) (cocycle : cocycles level action)
    (vertices : Fin 3 → G) :
    (differentialOne level action (rightTranslationHomotopy level action element cocycle)).val
        vertices =
      cocycle.val.val vertices - cocycle.val.val (fun index => vertices index * element) := by
  have first := cocycle_on_four level action cocycle
    (vertices 0 * element) (vertices 0) (vertices 1) (vertices 2)
  have second := cocycle_on_four level action cocycle
    (vertices 0 * element) (vertices 1 * element) (vertices 1) (vertices 2)
  have third := cocycle_on_four level action cocycle
    (vertices 0 * element) (vertices 1 * element) (vertices 2 * element) (vertices 2)
  have vertices_eq : ![vertices 0, vertices 1, vertices 2] = vertices := by
    funext index
    fin_cases index <;> rfl
  have translated_eq : ![vertices 0 * element, vertices 1 * element, vertices 2 * element] =
      (fun index => vertices index * element) := by
    funext index
    fin_cases index <;> rfl
  rw [vertices_eq] at first
  rw [translated_eq] at third
  apply sub_eq_zero.mp
  calc
    _ = -((cocycle.val.val vertices -
        cocycle.val.val ![vertices 0 * element, vertices 1, vertices 2] +
        cocycle.val.val ![vertices 0 * element, vertices 0, vertices 2] -
        cocycle.val.val ![vertices 0 * element, vertices 0, vertices 1]) -
      (cocycle.val.val ![vertices 1 * element, vertices 1, vertices 2] -
        cocycle.val.val ![vertices 0 * element, vertices 1, vertices 2] +
        cocycle.val.val ![vertices 0 * element, vertices 1 * element, vertices 2] -
        cocycle.val.val ![vertices 0 * element, vertices 1 * element, vertices 1]) +
      (cocycle.val.val ![vertices 1 * element, vertices 2 * element, vertices 2] -
        cocycle.val.val ![vertices 0 * element, vertices 2 * element, vertices 2] +
        cocycle.val.val ![vertices 0 * element, vertices 1 * element, vertices 2] -
        cocycle.val.val (fun index => vertices index * element))) := by
      change ((cocycle.val.val ![vertices 1 * element, vertices 1, vertices 2] -
          cocycle.val.val ![vertices 1 * element, vertices 2 * element, vertices 2]) -
        (cocycle.val.val ![vertices 0 * element, vertices 0, vertices 2] -
          cocycle.val.val ![vertices 0 * element, vertices 2 * element, vertices 2]) +
        (cocycle.val.val ![vertices 0 * element, vertices 0, vertices 1] -
          cocycle.val.val ![vertices 0 * element, vertices 1 * element, vertices 1])) -
        (cocycle.val.val vertices - cocycle.val.val (fun index => vertices index * element)) = _
      abel
    _ = 0 := by rw [first, second, third]; simp

end

end TernaryPeriodPolynomials.BoundaryFiniteness.CochainHomotopy
