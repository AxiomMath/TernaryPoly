module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Deck
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalAdjoint

@[expose] public section

/-! Actual coefficient-normalized deck pullback, with zero extension outside the coordinate domain. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric PolynomialCoefficientMetric SymmetricSpaceCharts SymmetricSpaceCovering
open SmoothCoveringDeRham CompactCoordinateIntegration
open Set Filter
open scoped ContDiff Topology

/-- Pull back along the deck map and undo its coefficient action. -/
def deckPull (n k : ℕ) (g : DeckGroup) (w : Coordinates → FormValue n k) :
    Coordinates → FormValue n k :=
  positiveCoordinates.indicator (coefficientRaw (coefficientMap (deckRepresentation n) g⁻¹)
    (pullRaw (deckMap g) w))

theorem deckPull_apply (n k : ℕ) (g : DeckGroup) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    deckPull n k g w x = coefficientFormMap (coefficientMap (deckRepresentation n) g⁻¹) k
      ((w (deckMap g x)).compContinuousLinearMap (fderiv ℝ (deckMap g) x)) :=
  indicator_of_mem hx _

theorem deckPull_of_notMem (n k : ℕ) (g : DeckGroup) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∉ positiveCoordinates) : deckPull n k g w x = 0 :=
  indicator_of_notMem hx _

theorem contDiffOn_deckPull (n k : ℕ) (g : DeckGroup) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) :
    ContDiffOn ℝ ∞ (deckPull n k g w) positiveCoordinates := by
  have h := coefficientRaw_smooth (coefficientMap (deckRepresentation n) g⁻¹)
    (pullRaw_smooth isOpen_positiveCoordinates (deckMap_smooth g) hw (fun _ hx => deckMap_mem g hx))
  exact h.congr (fun x hx => deckPull_apply n k g w hx)

/-- The support transports into the actual inverse image of the original compact support. -/
theorem tsupport_deckPull (n k : ℕ) (g : DeckGroup) (w : Coordinates → FormValue n k)
    (hc : HasCompactSupport w) (hs : tsupport w ⊆ positiveCoordinates) :
    tsupport (deckPull n k g w) ⊆ deckMap g⁻¹ '' tsupport w := by
  have hK := hc.image_of_continuousOn ((deckMap_smooth g⁻¹).continuousOn.mono hs)
  apply closure_minimal _ hK.isClosed
  intro x hx
  have hxp : x ∈ positiveCoordinates := by
    by_contra hn
    exact hx (deckPull_of_notMem n k g w hn)
  have hval : w (deckMap g x) ≠ 0 := by
    intro hzero
    apply hx
    rw [deckPull_apply n k g w hxp, hzero]
    ext v
    simp [coefficientFormMap]
  refine ⟨deckMap g x, subset_tsupport _ hval, ?_⟩
  rw [← deckMap_mul g⁻¹ g hxp, inv_mul_cancel, deckMap_one hxp]

theorem hasCompactSupport_deckPull (n k : ℕ) (g : DeckGroup) (w : Coordinates → FormValue n k)
    (hc : HasCompactSupport w) (hs : tsupport w ⊆ positiveCoordinates) :
    HasCompactSupport (deckPull n k g w) :=
  (hc.image_of_continuousOn ((deckMap_smooth g⁻¹).continuousOn.mono hs)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_deckPull n k g w hc hs)

theorem tsupport_deckPull_positive (n k : ℕ) (g : DeckGroup) (w : Coordinates → FormValue n k)
    (hc : HasCompactSupport w) (hs : tsupport w ⊆ positiveCoordinates) :
    tsupport (deckPull n k g w) ⊆ positiveCoordinates := by
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := tsupport_deckPull n k g w hc hs hx
  exact deckMap_mem g⁻¹ (hs hy)

theorem contDiff_deckPull (n k : ℕ) (g : DeckGroup) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (hc : HasCompactSupport w)
    (hs : tsupport w ⊆ positiveCoordinates) : ContDiff ℝ ∞ (deckPull n k g w) :=
  contDiff_of_tsupport_subset isOpen_positiveCoordinates (contDiffOn_deckPull n k g hw)
    (tsupport_deckPull_positive n k g w hc hs)

end TernaryPoly.PolynomialFormCoordinates
