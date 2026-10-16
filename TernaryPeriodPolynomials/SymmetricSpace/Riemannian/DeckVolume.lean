module

public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.CoordinateVolume
public import TernaryPeriodPolynomials.DifferentialForm.Metric.Deck

@[expose] public section


/-! The genuine deck coordinate maps preserve the actual local Riemannian volume. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open MeasureTheory Set SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SmoothCoveringDeRham SymmetricSpaceTraceMetric
open scoped ContDiff ENNReal

/-- The actual deck map as an open partial homeomorphism of the five-dimensional coordinates. -/
def deckCoordinates (g : DeckGroup) : OpenPartialHomeomorph Coordinates Coordinates where
  toFun := deckMap g
  invFun := deckMap g⁻¹
  source := positiveCoordinates
  target := positiveCoordinates
  map_source' := fun _ hx => deckMap_mem g hx
  map_target' := fun _ hx => deckMap_mem g⁻¹ hx
  left_inv' := by
    intro x hx
    rw [← deckMap_mul g⁻¹ g hx, inv_mul_cancel, deckMap_one hx]
  right_inv' := by
    intro x hx
    rw [← deckMap_mul g g⁻¹ hx, mul_inv_cancel, deckMap_one hx]
  open_source := isOpen_positiveCoordinates
  open_target := isOpen_positiveCoordinates
  continuousOn_toFun := (deckMap_smooth g).continuousOn
  continuousOn_invFun := (deckMap_smooth g⁻¹).continuousOn

/-- Absolute-Jacobian law for the actual normalized-congruence deck action. -/
theorem coordinateDensity_deck (g : DeckGroup) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    coordinateDensity x = |(fderiv ℝ (deckMap g) x).toLinearMap.det| * coordinateDensity (deckMap g x) := by
  let L := (fderiv ℝ (deckMap g) x).toLinearMap
  have h : LinearMap.BilinForm.comp (coordinateBilin (deckMap g x)) L L = coordinateBilin x := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact coordinatePair_fderiv_invariant
      (SymmetricSpaceArithmeticProper.realIntegral (deckInclusion g)) x hx v w
  change BilinearVolumeDensity.density (coordinateBilin x) = _
  rw [← h, BilinearVolumeDensity.density_comp]
  rfl

/-- Every measurable positive-coordinate set has the same actual volume after deck translation. -/
theorem coordinateVolume_deck_image (g : DeckGroup) {s : Set Coordinates}
    (hs : MeasurableSet s) (hsub : s ⊆ positiveCoordinates) :
    coordinateVolume (deckMap g '' s) = coordinateVolume s := by
  have hd (x : Coordinates) (hx : x ∈ s) :
      HasFDerivWithinAt (deckMap g) (fderiv ℝ (deckMap g) x) s x :=
    (((deckMap_smooth g).differentiableOn (by simp) x (hsub hx)).differentiableAt
      (isOpen_positiveCoordinates.mem_nhds (hsub hx))).hasFDerivAt.hasFDerivWithinAt
  rw [coordinateVolume_apply, coordinateVolume_apply,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hd ((deckCoordinates g).injOn.mono hsub)]
  apply setLIntegral_congr_fun hs
  intro x hx
  change ENNReal.ofReal |(fderiv ℝ (deckMap g) x).det| * ENNReal.ofReal (coordinateDensity (deckMap g x)) =
    ENNReal.ofReal (coordinateDensity x)
  rw [coordinateDensity_deck g x (hsub hx), ENNReal.ofReal_mul (abs_nonneg _)]

end TernaryPoly.SymmetricSpaceRiemannian
