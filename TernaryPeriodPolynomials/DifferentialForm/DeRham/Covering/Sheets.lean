module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Complex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter SmoothLocalDeRham SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
  SymmetricSpaceQuotientManifold
open scoped ContDiff Topology

/-- The coordinate of the distinguished local lift above the same quotient point. -/
def baseCoordinate (S : Space) (x : Coordinates) : Coordinates :=
  quotientChart S (coordinateProjection x)

theorem baseCoordinate_mem (S : Space) {x : Coordinates}
    (hx : x ∈ liftedDomain (quotientChart S).source) :
    baseCoordinate S x ∈ (quotientChart S).target :=
  (quotientChart S).map_source hx.2

/-- The genuine unique deck element taking the chosen local lift to a covering point. -/
theorem existsUnique_sheetElement (S : Space) {x : Coordinates}
    (hx : x ∈ liftedDomain (quotientChart S).source) :
    ∃! g : DeckGroup, g • localLift S (coordinateProjection x) = coordinateChart.symm x := by
  have hsource : coordinateProjection x ∈ (localLift S).source := by
    simpa only [quotientChart_source, mem_preimage] using hx.2
  have hp : quotientProjection (coordinateChart.symm x) =
      quotientProjection (localLift S (coordinateProjection x)) :=
    (projection_localLift S hsource).symm
  obtain ⟨g, hg⟩ := quotientProjection_quotientCovering.apply_eq_iff_mem_orbit.mp hp
  exact ⟨g, hg, fun h hh => IsCancelSMul.right_cancel h g _ (hh.trans hg.symm)⟩

def sheetElement (S : Space) (x : Coordinates) : DeckGroup := by
  classical
  exact if hx : x ∈ liftedDomain (quotientChart S).source then
    Classical.choose (existsUnique_sheetElement S hx).exists else 1

theorem sheetElement_spec (S : Space) {x : Coordinates}
    (hx : x ∈ liftedDomain (quotientChart S).source) :
    sheetElement S x • localLift S (coordinateProjection x) = coordinateChart.symm x := by
  simp only [sheetElement, dite_eq_left hx]
  exact Classical.choose_spec (existsUnique_sheetElement S hx).exists

theorem sheetElement_unique (S : Space) {x : Coordinates}
    (hx : x ∈ liftedDomain (quotientChart S).source) (g : DeckGroup)
    (hg : g • localLift S (coordinateProjection x) = coordinateChart.symm x) :
    sheetElement S x = g :=
  IsCancelSMul.right_cancel _ _ _ ((sheetElement_spec S hx).trans hg.symm)

/-- The actual sheet label is locally constant, by uniqueness of continuous covering lifts. -/
theorem sheetElement_eventually (S : Space) {x : Coordinates}
    (hx : x ∈ liftedDomain (quotientChart S).source) :
    sheetElement S =ᶠ[𝓝 x] fun _ => sheetElement S x := by
  let g := sheetElement S x
  have hs := liftedDomain_isOpen (quotientChart S).open_source
  have hq : ContinuousAt coordinateProjection x :=
    coordinateProjection_continuousOn.continuousAt (isOpen_positiveCoordinates.mem_nhds hx.1)
  have hl : ContinuousAt (fun y => g • localLift S (coordinateProjection y)) x :=
    (continuous_const_smul g).continuousAt.comp
      (((localLift S).continuousAt (by simpa only [quotientChart_source, mem_preimage] using hx.2)).comp hq)
  have hc : ContinuousAt coordinateChart.symm x := coordinateChart.symm.continuousAt (by simpa using hx.1)
  have he := covering_lifts_eventuallyEq quotientProjection_covering.isLocalHomeomorph
    hl hc (sheetElement_spec S hx) (show (fun y => quotientProjection (g • localLift S (coordinateProjection y)))
      =ᶠ[𝓝 x] (fun y => quotientProjection (coordinateChart.symm y)) from by
        filter_upwards [hs.mem_nhds hx] with y hy
        rw [quotientProjection_quotientCovering.map_smul,
          projection_localLift S (by simpa only [quotientChart_source, mem_preimage] using hy.2)]
        rfl)
  filter_upwards [hs.mem_nhds hx, he] with y hy heq
  exact sheetElement_unique S hy g heq

theorem baseCoordinate_sheet (S : Space) {x : Coordinates}
    (hx : x ∈ liftedDomain (quotientChart S).source) :
    deckMap (sheetElement S x) (baseCoordinate S x) = x := by
  have h := congrArg coordinateChart (sheetElement_spec S hx)
  rw [← deckMap_chart, coordinateChart.right_inv (by simpa using hx.1)] at h
  exact h

theorem baseCoordinate_eq_inverseDeck (S : Space) {x : Coordinates}
    (hx : x ∈ liftedDomain (quotientChart S).source) :
    baseCoordinate S x = deckMap (sheetElement S x)⁻¹ x := by
  have hp := quotientChart_target_subset S (baseCoordinate_mem S hx)
  calc
    baseCoordinate S x = deckMap ((sheetElement S x)⁻¹ * sheetElement S x) (baseCoordinate S x) := by
      rw [inv_mul_cancel, deckMap_one hp]
    _ = deckMap (sheetElement S x)⁻¹ (deckMap (sheetElement S x) (baseCoordinate S x)) := deckMap_mul _ _ hp
    _ = deckMap (sheetElement S x)⁻¹ x := congrArg _ (baseCoordinate_sheet S hx)

theorem baseCoordinate_eventually (S : Space) {x : Coordinates}
    (hx : x ∈ liftedDomain (quotientChart S).source) :
    baseCoordinate S =ᶠ[𝓝 x] deckMap (sheetElement S x)⁻¹ := by
  filter_upwards [(liftedDomain_isOpen (quotientChart S).open_source).mem_nhds hx,
    sheetElement_eventually S hx] with y hy hg
  rw [baseCoordinate_eq_inverseDeck S hy, hg]

/-- The coordinate of the actual quotient lift is smooth on every sheet of the covering. -/
theorem baseCoordinate_smooth (S : Space) :
    ContDiffOn ℝ ∞ (baseCoordinate S) (liftedDomain (quotientChart S).source) := by
  intro x hx
  have h := (deckMap_smooth (sheetElement S x)⁻¹ x hx.1).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx.1)
  exact (h.congr_of_eventuallyEq (baseCoordinate_eventually S hx)).contDiffWithinAt

theorem baseCoordinate_deck (S : Space) (g : DeckGroup) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) : baseCoordinate S (deckMap g x) = baseCoordinate S x := by
  unfold baseCoordinate
  rw [coordinateProjection_deck g hx]

theorem sheetElement_deck (S : Space) (g : DeckGroup) {x : Coordinates}
    (hx : x ∈ liftedDomain (quotientChart S).source) :
    sheetElement S (deckMap g x) = g * sheetElement S x := by
  apply sheetElement_unique S (deckMap_liftedDomain g _ hx)
  rw [coordinateProjection_deck g hx.1, mul_smul, sheetElement_spec S hx,
    deckMap_inverseChart g hx.1]

theorem deckMap_baseCoordinate_eventually (S : Space) {x : Coordinates}
    (hx : x ∈ liftedDomain (quotientChart S).source) :
    (deckMap (sheetElement S x) ∘ baseCoordinate S) =ᶠ[𝓝 x] id := by
  filter_upwards [(liftedDomain_isOpen (quotientChart S).open_source).mem_nhds hx,
    sheetElement_eventually S hx] with y hy hg
  change deckMap (sheetElement S x) (baseCoordinate S y) = y
  rw [← hg]
  exact baseCoordinate_sheet S hy

theorem baseCoordinate_chart (S : Space) {x : Coordinates} (hx : x ∈ (quotientChart S).target) :
    baseCoordinate S x = x := by
  unfold baseCoordinate
  rw [← quotientChart_projection_coordinates S hx]
  exact (quotientChart S).right_inv hx

theorem sheetElement_chart (S : Space) {x : Coordinates} (hx : x ∈ (quotientChart S).target) :
    sheetElement S x = 1 := by
  apply sheetElement_unique S (quotientChart_target_liftedDomain S hx)
  rw [one_smul]
  apply coordinateChart.injOn (by simp) (by simp)
  rw [coordinateChart.right_inv (by simpa using quotientChart_target_subset S hx)]
  exact baseCoordinate_chart S hx

end TernaryPoly.SmoothCoveringDeRham
