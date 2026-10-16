module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Cover.Countable
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Cover.Coordinates
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.CoordinateVolume

@[expose] public section


/-!
# General coercivity: the Riemannian volume of the model `Space`

`spaceVolume` is the pullback of the Riemannian coordinate volume `coordinateVolume` (Lebesgue measure
weighted by `coordinateDensity`, the square root of the Gram determinant of the trace metric) along
the global chart `coordinateChart : Space → ℝ⁵`.  Every element of `GL₃(ℝ)` preserves it, because the
trace metric is invariant (`coordinatePair_fderiv_invariant`), so every admissible group acts by
measure-preserving maps.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
open TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SymmetricSpaceTraceMetric
open scoped ContDiff ENNReal

/-- The Borel structure on the model `Space`. -/
instance instMeasurableSpaceSpace : MeasurableSpace Space := borel Space

instance instBorelSpaceSpace : BorelSpace Space := ⟨rfl⟩

instance instMeasurableConstSMulSpace (Γ : Subgroup RealGL) : MeasurableConstSMul Γ Space :=
  ⟨fun γ => (continuous_act (γ : RealGL)).measurable⟩

theorem measurableEmbedding_coordinateChart :
    MeasurableEmbedding (fun S : Space => coordinateChart S) :=
  coordinateEmbedding.measurableEmbedding

/-- The Riemannian volume of the model, pulled back from the coordinates. -/
def spaceVolume : Measure Space :=
  Measure.comap (fun S : Space => coordinateChart S) coordinateVolume

theorem spaceVolume_apply (s : Set Space) :
    spaceVolume s = coordinateVolume (coordinateChart '' s) :=
  measurableEmbedding_coordinateChart.comap_apply _ _

/-- Absolute-Jacobian law for every `GL₃(ℝ)` coordinate action. -/
theorem coordinateDensity_action (g : RealGL) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    coordinateDensity x =
      |(fderiv ℝ (coordinateAction g) x).toLinearMap.det| *
        coordinateDensity (coordinateAction g x) := by
  let L := (fderiv ℝ (coordinateAction g) x).toLinearMap
  have h : LinearMap.BilinForm.comp (coordinateBilin (coordinateAction g x)) L L =
      coordinateBilin x := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact coordinatePair_fderiv_invariant g x hx v w
  change TernaryPoly.BilinearVolumeDensity.density (coordinateBilin x) = _
  rw [← h, TernaryPoly.BilinearVolumeDensity.density_comp]
  rfl

/-- Every measurable positive-coordinate set has the same Riemannian volume after any action. -/
theorem coordinateVolume_action_image (g : RealGL) {s : Set Coordinates}
    (hs : MeasurableSet s) (hsub : s ⊆ positiveCoordinates) :
    coordinateVolume (coordinateAction g '' s) = coordinateVolume s := by
  have hd (x : Coordinates) (hx : x ∈ s) :
      HasFDerivWithinAt (coordinateAction g) (fderiv ℝ (coordinateAction g) x) s x :=
    (((contDiffOn_coordinateAction g).differentiableOn (by simp) x (hsub hx)).differentiableAt
      (isOpen_positiveCoordinates.mem_nhds (hsub hx))).hasFDerivAt.hasFDerivWithinAt
  rw [coordinateVolume_apply, coordinateVolume_apply,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hd
      ((coordinateAction_injOn g).mono hsub)]
  apply setLIntegral_congr_fun hs
  intro x hx
  change ENNReal.ofReal |(fderiv ℝ (coordinateAction g) x).det| *
    ENNReal.ofReal (coordinateDensity (coordinateAction g x)) =
    ENNReal.ofReal (coordinateDensity x)
  rw [coordinateDensity_action g x (hsub hx), ENNReal.ofReal_mul (abs_nonneg _)]

/-- The Riemannian volume of `Space` is preserved by every element of `GL₃(ℝ)`. -/
theorem spaceVolume_act_image (g : RealGL) {s : Set Space} (hs : MeasurableSet s) :
    spaceVolume (act g '' s) = spaceVolume s := by
  rw [spaceVolume_apply, spaceVolume_apply]
  have himg : coordinateChart '' (act g '' s) = coordinateAction g '' (coordinateChart '' s) := by
    rw [image_image, image_image]
    exact image_congr (fun S _ => coordinateChart_act g S)
  rw [himg]
  exact coordinateVolume_action_image g (measurableEmbedding_coordinateChart.measurableSet_image.mpr hs)
    (by rintro _ ⟨S, _, rfl⟩; exact extract_mem S)

theorem spaceVolume_preimage_act (g : RealGL) {s : Set Space} (hs : MeasurableSet s) :
    spaceVolume (act g ⁻¹' s) = spaceVolume s := by
  have : act g ⁻¹' s = act g⁻¹ '' s := by
    ext S
    constructor
    · intro hS
      exact ⟨act g S, hS, by rw [← act_mul, inv_mul_cancel, act_one]⟩
    · rintro ⟨T, hT, rfl⟩
      change act g (act g⁻¹ T) ∈ s
      rwa [← act_mul, mul_inv_cancel, act_one]
  rw [this]
  exact spaceVolume_act_image g⁻¹ hs

instance instSMulInvariantMeasureSpace (Γ : Subgroup RealGL) :
    SMulInvariantMeasure Γ Space spaceVolume :=
  ⟨fun γ _ hs => spaceVolume_preimage_act (γ : RealGL) hs⟩

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
