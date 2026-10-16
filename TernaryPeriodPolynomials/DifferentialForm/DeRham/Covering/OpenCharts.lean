module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Transitions

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (S : Space) {U : Set OrbitSpace} {n : ℕ}

/-- The ordinary coordinate domain for a quotient open set in an actual lifting chart. -/
def chartDomain (S : Space) (U : Set OrbitSpace) : Set Coordinates :=
  (quotientChart S).target ∩ (quotientChart S).symm ⁻¹' U

theorem chartDomain_isOpen (hU : IsOpen U) : IsOpen (chartDomain S U) :=
  (quotientChart S).isOpen_inter_preimage_symm hU

theorem chartDomain_liftedDomain : chartDomain S U ⊆ liftedDomain U := by
  intro x hx
  refine ⟨quotientChart_target_subset S hx.1, ?_⟩
  change coordinateProjection x ∈ U
  rw [← quotientChart_projection_coordinates S hx.1]
  exact hx.2

/-- The true local representative of a section over any quotient open set. -/
def localRepresentative (n : ℕ) : EquivariantForm ρ U n →ₗ[ℝ]
    Form (F := F) (chartDomain S U) n :=
  (restrictTo (chartDomain_liftedDomain S) n).comp (equivariantSubmodule ρ U n).subtype

@[simp] theorem localRepresentative_apply (w : EquivariantForm ρ U n)
    {x : Coordinates} (hx : x ∈ chartDomain S U) :
    (localRepresentative ρ S n w : RawForm Coordinates F n) x =
      (w.val : RawForm Coordinates F n) x := restrictTo_apply (chartDomain_liftedDomain S) w.val hx

theorem localRepresentative_d (hU : IsOpen U) (w : EquivariantForm ρ U n) :
    localRepresentative ρ S (n + 1) (differential ρ hU n w) =
      d (chartDomain_isOpen S hU) n (localRepresentative ρ S n w) :=
  restrictTo_d (liftedDomain_isOpen hU) (chartDomain_isOpen S hU) (chartDomain_liftedDomain S) w.val

theorem chartOpen_subset_of_chartDomain {V : Set Coordinates} (hV : V ⊆ chartDomain S U) :
    chartOpen S V ⊆ U := by
  intro q hq
  have h := (hV hq.2).2
  simpa only [mem_preimage, (quotientChart S).left_inv hq.1] using h

theorem baseCoordinate_projection {x : Coordinates}
    (hx : x ∈ liftedDomain (quotientChart S).source) :
    coordinateProjection (baseCoordinate S x) = coordinateProjection x := by
  rw [← quotientChart_projection_coordinates S (baseCoordinate_mem S hx)]
  exact (quotientChart S).left_inv hx.2

/-- Reconstruction on each genuine sheet for an arbitrary quotient section. -/
theorem extendRaw_reconstruction (w : EquivariantForm ρ U n) {x : Coordinates}
    (hxU : x ∈ liftedDomain U) (hxS : x ∈ liftedDomain (quotientChart S).source) :
    extendRaw ρ S (w.val : RawForm Coordinates F n) x = (w.val : RawForm Coordinates F n) x := by
  have hs := liftedDomain_isOpen (quotientChart S).open_source
  have hb := baseCoordinate_mem S hxS
  have hbp := quotientChart_target_subset S hb
  have hbU : baseCoordinate S x ∈ liftedDomain U := by
    refine ⟨hbp, ?_⟩
    change coordinateProjection (baseCoordinate S x) ∈ U
    rw [baseCoordinate_projection S hxS]
    exact hxU.2
  have hbd := ((baseCoordinate_smooth S x hxS).contDiffAt (hs.mem_nhds hxS)).differentiableAt (by simp)
  have hgd := ((deckMap_smooth (sheetElement S x) _ hbp).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hbp)).differentiableAt (by simp)
  have he := w.property (sheetElement S x) (baseCoordinate S x) hbU
  calc
    extendRaw ρ S (w.val : RawForm Coordinates F n) x =
        pullRaw (baseCoordinate S) (pullRaw (deckMap (sheetElement S x))
          (w.val : RawForm Coordinates F n)) x := by
      change _ = (pullRaw (deckMap (sheetElement S x)) (w.val : RawForm Coordinates F n)
        (baseCoordinate S x)).compContinuousLinearMap _
      rw [he]
      ext v
      rfl
    _ = (w.val : RawForm Coordinates F n) x := by
      rw [pullRaw_comp _ hgd hbd,
        pullRaw_eventuallyEq _ (deckMap_baseCoordinate_eventually S hxS), pullRaw_id]

theorem chartExtendOn_localRepresentative {V : Set Coordinates} (hV : IsOpen V)
    (hVU : V ⊆ chartDomain S U) (w : EquivariantForm ρ U n) :
    chartExtendOn ρ S hV n (restrictTo hVU n (localRepresentative ρ S n w)) =
      restrictEquivariant ρ (chartOpen_subset_of_chartDomain S hVU) n w := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  have hb := baseCoordinate_mem_chartOpen S hx
  rw [chartExtendOn_apply ρ S hV _ hx, restrictEquivariant_apply ρ _ w hx]
  have he := extendRaw_reconstruction ρ S w
    (liftedDomain_mono (chartOpen_subset_of_chartDomain S hVU) hx)
    (liftedDomain_mono (chartOpen_subset S V) hx)
  rw [← he]
  unfold extendRaw pullRaw
  rw [restrictTo_apply hVU _ hb, localRepresentative_apply ρ S w (hVU hb)]

end TernaryPoly.SmoothCoveringDeRham
