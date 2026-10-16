module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cut
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.StabilizerCoordinate

@[expose] public section


/-!
# The Shapiro coordinates of a cut cochain

Formalized by Claude Sonnet 5.5.

The idempotent `cutHom S` of `prodComplex Γ V Z` is a chain map `cutChain S`.  Pulling back along it multiplies the Shapiro coordinate at `z` by the
indicator of `z ∈ S`: the coordinate of a cocycle cut to a `Γ`-invariant set `S` of labels is the coordinate of the cocycle at the points of `S` and
zero at the points outside.
-/

open CategoryTheory Limits
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPoly.EquivariantSingularSmall

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

section CutChain

variable (Γ : Type) [Group Γ] (V Z : Type) [MulAction Γ V] [MulAction Γ Z]
  (S : Set Z) (hS : ∀ (γ : Γ) (z : Z), γ • z ∈ S ↔ z ∈ S)

open Classical in
include hS in
/-- The cut as a chain map of the permutation complex. -/
def cutChain : prodComplex Γ V Z ⟶ prodComplex Γ V Z where
  f k := cutHom Γ V Z S hS k
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    exact (cutHom_comm_d Γ V Z S hS j).symm

end CutChain

section Coord

open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z]
  (S : Set Z) (hS : ∀ (γ : Γ) (z : Z), γ • z ∈ S ↔ z ∈ S)
  (T : Subgroup Γ) (W : Rep.{0} ℚ Γ) (v₀ : V) (z : Z) (hz : ∀ g : T, g • z = z)

open Classical in
/-- **The Shapiro coordinate of a cut cochain**, on cochains. -/
theorem stabCoord_cut (k : ℕ) (c : (prodComplex Γ V Z).X k ⟶ W) :
    ((stabCoord T W v₀ z hz).f k).hom (cutHom Γ V Z S hS k ≫ c) =
      if z ∈ S then ((stabCoord T W v₀ z hz).f k).hom c else 0 := by
  by_cases h : z ∈ S
  · rw [ite_eq_left h]
    apply Rep.free_ext
    intro x
    rw [stabCoord_single, stabCoord_single]
    change c.hom ((cutHom Γ V Z S hS k).hom _) = _
    erw [cutHom_single, ite_eq_left h]
    rfl
  · rw [ite_eq_right h]
    apply Rep.free_ext
    intro x
    rw [stabCoord_single]
    change c.hom ((cutHom Γ V Z S hS k).hom _) = _
    erw [cutHom_single, ite_eq_right h, map_zero]
    rfl


theorem stabCoord_cut_chain_mem (h : z ∈ S) :
    homPullback (cutChain Γ V Z S hS) W ≫ stabCoord T W v₀ z hz = stabCoord T W v₀ z hz := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((stabCoord T W v₀ z hz).f k).hom (cutHom Γ V Z S hS k ≫ c) = _
  erw [stabCoord_cut, ite_eq_left h]

theorem stabCoord_cut_chain_not_mem (h : z ∉ S) :
    homPullback (cutChain Γ V Z S hS) W ≫ stabCoord T W v₀ z hz = 0 := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((stabCoord T W v₀ z hz).f k).hom (cutHom Γ V Z S hS k ≫ c) = _
  erw [stabCoord_cut, ite_eq_right h]
  rfl

theorem faceCoord_eq_homologyMap_stabCoord (n : ℕ) :
    faceCoord T W v₀ z hz n =
      HomologicalComplex.homologyMap (stabCoord T W v₀ z hz) n ≫ (gisoBar (Rep.res T.subtype W) n).inv := by
  unfold faceCoord fixCoordH stabCoord
  rw [HomologicalComplex.homologyMap_comp, Category.assoc]

/-- **The Shapiro coordinate of a cut class** at a point of `S` is the coordinate of the class. -/
theorem faceCoord_cut_mem (h : z ∈ S) (n : ℕ) :
    HomologicalComplex.homologyMap (homPullback (cutChain Γ V Z S hS) W) n ≫ faceCoord T W v₀ z hz n =
      faceCoord T W v₀ z hz n := by
  rw [faceCoord_eq_homologyMap_stabCoord, ← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    stabCoord_cut_chain_mem S hS T W v₀ z hz h]

/-- … and at a point outside `S` it is zero. -/
theorem faceCoord_cut_not_mem (h : z ∉ S) (n : ℕ) :
    HomologicalComplex.homologyMap (homPullback (cutChain Γ V Z S hS) W) n ≫ faceCoord T W v₀ z hz n = 0 := by
  rw [faceCoord_eq_homologyMap_stabCoord, ← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    stabCoord_cut_chain_not_mem S hS T W v₀ z hz h]
  simp

end Coord

end TernaryPeriodPolynomials.Argument.GammaNStokes
