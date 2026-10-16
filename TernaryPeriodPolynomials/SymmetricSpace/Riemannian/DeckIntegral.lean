module

public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.DeckVolume

@[expose] public section


/-! Genuine change of variables for real coordinate-density integrals under deck maps. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open MeasureTheory Set SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham
open scoped ContDiff

/-- Every scalar function obeys the actual density-weighted deck change of variables. -/
theorem integral_coordinateDensity_deck (g : DeckGroup) (f : Coordinates → ℝ) :
    ∫ x in positiveCoordinates, coordinateDensity x * f (deckMap g x) =
      ∫ x in positiveCoordinates, coordinateDensity x * f x := by
  have hd (x : Coordinates) (hx : x ∈ positiveCoordinates) :
      HasFDerivWithinAt (deckMap g) (fderiv ℝ (deckMap g) x) positiveCoordinates x :=
    (((deckMap_smooth g x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume
    isOpen_positiveCoordinates.measurableSet hd (deckCoordinates g).injOn
    (fun x => coordinateDensity x * f x)
  have himage : deckMap g '' positiveCoordinates = positiveCoordinates :=
    (deckCoordinates g).image_source_eq_target
  rw [himage] at he
  refine (setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet (fun x hx => ?_)).trans he.symm
  change coordinateDensity x * f (deckMap g x) =
    |(fderiv ℝ (deckMap g) x).det| * (coordinateDensity (deckMap g x) * f (deckMap g x))
  rw [coordinateDensity_deck g x hx, mul_assoc]

end TernaryPoly.SymmetricSpaceRiemannian
