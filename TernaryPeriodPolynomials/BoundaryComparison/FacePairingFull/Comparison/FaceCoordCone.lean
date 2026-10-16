module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Restriction
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.StabilizerRestriction

@[expose] public section


/-!
# Restriction of a class of `Γ(6)` to a face and then to its stabilizer is Mathlib's restriction

For a class `x` of `H^n(Hom_{Γ(6)}(ℚ[V^{•+1}], W))` (the point resolution), its geometric restriction to the
boundary cone has line component the pullback of `x` to the line resolution; the Shapiro coordinate
`faceCoord` of that component at a line `L` (resp. of the plane component at a plane `P`) is the image under
Mathlib's `groupCohomology.map` along `Γ(6)_L ≤ Γ(6)` of the group-cohomology class `fixCoordH x` of `x`
(`faceCoord_line_geoRestriction`, `faceCoord_plane_geoRestriction`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.EquivariantSingularSmall
open TernaryPoly.OrdinaryIncidence (Line Plane)
open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

variable (W : Rep.{0} ℚ Γ6) (n : ℕ)

theorem homologyMap_coneToPt_line :
    homologyMap (homPullback coneToPt W) n ≫ homologyMap (homPullback coneLine W) n =
      homologyMap (homPullback (prodMapHom Γ6 RationalGL3 Line (fun _ => PUnit.unit)
        (fun _ _ => rfl)) W) n := by
  rw [← homologyMap_comp, ← homPullback_comp]
  exact congrArg (fun t => homologyMap (homPullback t W) n) coneLine_coneToPt

theorem homologyMap_coneToPt_plane :
    homologyMap (homPullback coneToPt W) n ≫ homologyMap (homPullback conePlane W) n =
      homologyMap (homPullback (prodMapHom Γ6 RationalGL3 Plane (fun _ => PUnit.unit)
        (fun _ _ => rfl)) W) n := by
  rw [← homologyMap_comp, ← homPullback_comp]
  exact congrArg (fun t => homologyMap (homPullback t W) n) conePlane_coneToPt

/-- **A line's Shapiro coordinate of the geometric restriction is Mathlib's restriction to the stabilizer
of the line.** -/
theorem faceCoord_line_geoRestriction (L : Line) :
    homologyMap (homPullback coneToPt W) n ≫ homologyMap (homPullback coneLine W) n ≫
        faceCoord (MulAction.stabilizer Γ6 L) W (1 : RationalGL3) L (fun g => g.2) n =
      fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) W n ≫
        groupCohomology.map (MulAction.stabilizer Γ6 L).subtype
          (𝟙 (Rep.res (MulAction.stabilizer Γ6 L).subtype W)) n := by
  rw [← Category.assoc, homologyMap_coneToPt_line]
  exact faceCoord_restriction (MulAction.stabilizer Γ6 L) W (1 : RationalGL3) L (fun g => g.2) n

/-- The same for planes. -/
theorem faceCoord_plane_geoRestriction (P : Plane) :
    homologyMap (homPullback coneToPt W) n ≫ homologyMap (homPullback conePlane W) n ≫
        faceCoord (MulAction.stabilizer Γ6 P) W (1 : RationalGL3) P (fun g => g.2) n =
      fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) W n ≫
        groupCohomology.map (MulAction.stabilizer Γ6 P).subtype
          (𝟙 (Rep.res (MulAction.stabilizer Γ6 P).subtype W)) n := by
  rw [← Category.assoc, homologyMap_coneToPt_plane]
  exact faceCoord_restriction (MulAction.stabilizer Γ6 P) W (1 : RationalGL3) P (fun g => g.2) n

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
