module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Basic
public import TernaryPeriodPolynomials.SymmetricSpace.ChartsAction

@[expose] public section


/-!
# General coercivity: the coordinate form of the group action

The action of `GL₃(ℝ)` on `Space` is carried by the global chart `coordinateChart` to the smooth
map `coordinateAction g` of the open set `positiveCoordinates ⊆ ℝ⁵`.  This file records that the
chart is equivariant, that `coordinateAction` is an action on `positiveCoordinates`, and the
orbit-space projection `coordProj` in coordinates.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Set TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
open TernaryPoly.SymmetricSpaceCovering

theorem coordinateChart_act (g : RealGL) (S : Space) :
    coordinateChart (act g S) = coordinateAction g (coordinateChart S) :=
  chartHomeomorph_act g S

theorem coordinateAction_injOn (g : RealGL) : InjOn (coordinateAction g) positiveCoordinates := by
  intro x hx y hy h
  have := (coordinateActionHomeomorph g).injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext h)
  exact congrArg Subtype.val this

theorem coordinateAction_eq_chart (g : RealGL) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coordinateAction g x = coordinateChart (act g (coordinateChart.symm x)) := by
  rw [coordinateChart_act, coordinateChart.right_inv (by simpa using hx)]

theorem coordinateAction_one {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coordinateAction 1 x = x := by
  rw [coordinateAction_eq_chart 1 hx, act_one, coordinateChart.right_inv (by simpa using hx)]

theorem coordinateAction_mul (g h : RealGL) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coordinateAction (g * h) x = coordinateAction g (coordinateAction h x) := by
  rw [coordinateAction_eq_chart (g * h) hx, coordinateAction_eq_chart g (coordinateAction_mem h x hx),
    coordinateAction_eq_chart h hx, coordinateChart.left_inv (by simp), act_mul]

variable {Γ : Subgroup RealGL}

/-- The orbit-space projection in coordinates. -/
def coordProj (Γ : Subgroup RealGL) (x : Coordinates) : OrbitSpace Γ :=
  proj Γ (coordinateChart.symm x)

theorem coordProj_chart (S : Space) : coordProj Γ (coordinateChart S) = proj Γ S := by
  rw [coordProj, coordinateChart.left_inv (by simp)]

theorem coordProj_action (γ : Γ) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coordProj Γ (coordinateAction (γ : RealGL) x) = coordProj Γ x := by
  rw [coordinateAction_eq_chart (γ : RealGL) hx, coordProj_chart]
  exact proj_smul γ _

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
