module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Trivialization

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {n : ℕ}

theorem liftedDomain_mono {U V : Set OrbitSpace} (hVU : V ⊆ U) : liftedDomain V ⊆ liftedDomain U :=
  fun _ hx => ⟨hx.1, hVU hx.2⟩

/-- Restriction of local-coefficient forms over actual quotient open subsets. -/
def restrictEquivariant {U V : Set OrbitSpace} (hVU : V ⊆ U) (n : ℕ) :
    EquivariantForm ρ U n →ₗ[ℝ] EquivariantForm ρ V n where
  toFun w := ⟨restrictTo (liftedDomain_mono hVU) n w.val, by
    intro g x hx
    change ((restrictTo _ n w.val : RawForm Coordinates F n) (deckMap g x)).compContinuousLinearMap _ = _
    rw [restrictTo_apply _ _ (deckMap_liftedDomain g V hx), restrictTo_apply _ _ hx]
    exact w.property g x (liftedDomain_mono hVU hx)⟩
  map_add' w z := Subtype.ext (map_add _ w.val z.val)
  map_smul' c w := Subtype.ext (map_smul _ c w.val)

@[simp] theorem restrictEquivariant_apply {U V : Set OrbitSpace} (hVU : V ⊆ U)
    (w : EquivariantForm ρ U n) {x : Coordinates} (hx : x ∈ liftedDomain V) :
    ((restrictEquivariant ρ hVU n w).val : RawForm Coordinates F n) x =
      (w.val : RawForm Coordinates F n) x := restrictTo_apply (liftedDomain_mono hVU) w.val hx

theorem restrictEquivariant_d {U V : Set OrbitSpace} (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (w : EquivariantForm ρ U n) :
    restrictEquivariant ρ hVU (n + 1) (differential ρ hU n w) =
      differential ρ hV n (restrictEquivariant ρ hVU n w) := by
  apply Subtype.ext
  exact restrictTo_d (liftedDomain_isOpen hU) (liftedDomain_isOpen hV) (liftedDomain_mono hVU) w.val

/-- An actual quotient neighborhood cut out inside a lifting chart. -/
def chartOpen (S : Space) (V : Set Coordinates) : Set OrbitSpace :=
  (quotientChart S).source ∩ (quotientChart S) ⁻¹' V

theorem chartOpen_isOpen (S : Space) {V : Set Coordinates} (hV : IsOpen V) :
    IsOpen (chartOpen S V) := (quotientChart S).isOpen_inter_preimage hV

theorem chartOpen_subset (S : Space) (V : Set Coordinates) :
    chartOpen S V ⊆ (quotientChart S).source := inter_subset_left

theorem baseCoordinate_mem_chartOpen (S : Space) {V : Set Coordinates} {x : Coordinates}
    (hx : x ∈ liftedDomain (chartOpen S V)) : baseCoordinate S x ∈ V := hx.2.2

theorem chartOpen_contains (S : Space) {V : Set Coordinates} {x : Coordinates}
    (hx : x ∈ (quotientChart S).target) (hxV : x ∈ V) :
    (quotientChart S).symm x ∈ chartOpen S V :=
  ⟨(quotientChart S).map_target hx, by simpa only [mem_preimage, (quotientChart S).right_inv hx] using hxV⟩

end TernaryPoly.SmoothCoveringDeRham
