module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FormSums

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Filter Function CategoryTheory
open SmoothLocalDeRham SmoothCoveringDeRham SmoothDeRhamGluing SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Topology ContDiff Manifold
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {ι : Type*} (U : ι → Set OrbitSpace)
  (hU : ∀ i, IsOpen (U i))
  (φ : SmoothPartitionOfUnity ι 𝓘(ℝ, Coordinates) OrbitSpace Set.univ)
  (hφ : φ.IsSubordinate U) {V : Set OrbitSpace} (hV : IsOpen V) (n : ℕ)

include hφ in
/-- A subordinate global smooth scalar vanishes near the excluded side of an actual
intersection, exactly as needed for genuine zero extension. -/
theorem partitionScalar_eventually_zero (i : ι) (q : OrbitSpace) (hq : q ∈ V)
    (hn : q ∉ U i ∩ V) : (φ i : OrbitSpace → ℝ) =ᶠ[𝓝 q] 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => hn ⟨hφ i h, hq⟩)

/-- A genuine partition term on an overlap extends smoothly to the whole chosen open. -/
def partitionExtend (i : ι) : EquivariantForm ρ (U i ∩ V) n →ₗ[ℝ] EquivariantForm ρ V n :=
  weightedExtend ((hU i).inter hV) hV inter_subset_right (φ i) (φ i).contMDiff.contMDiffOn
    (partitionScalar_eventually_zero U φ hφ i) n

/-- Actual projected support of each partition extension is controlled by its scalar support. -/
theorem partitionExtend_support (i : ι) (w : EquivariantForm ρ (U i ∩ V) n) :
    projectedFormSupport (partitionExtend U hU φ hφ hV n i w) ⊆ Function.support (φ i) := by
  rintro _ ⟨x, hx, rfl⟩
  change φ i (coordinateProjection x) ≠ 0
  intro hz
  apply hx
  change φ i (coordinateProjection x) • _ = 0
  rw [hz, zero_smul]

/-- The actual partition extensions form a locally finite family on the genuine quotient. -/
theorem partitionExtend_locallyFinite (w : ∀ i, EquivariantForm ρ (U i ∩ V) n) :
    LocallyFinite (fun i => projectedFormSupport (partitionExtend U hU φ hφ hV n i (w i))) :=
  φ.locallyFinite.subset (fun i => partitionExtend_support U hU φ hφ hV n i (w i))

/-- Genuine partition summation of forms on overlaps, with smooth extension and local finiteness
proved for the actual covering representatives. -/
def partitionSum (w : ∀ i, EquivariantForm ρ (U i ∩ V) n) : EquivariantForm ρ V n :=
  locallyFiniteFormSum hV (fun i => partitionExtend U hU φ hφ hV n i (w i))
    (partitionExtend_locallyFinite U hU φ hφ hV n w)

/-- The actual partition sum is literally the pointwise finite weighted sum on the covering. -/
theorem partitionSum_apply (w : ∀ i, EquivariantForm ρ (U i ∩ V) n) (x : Coordinates) :
    ((partitionSum U hU φ hφ hV n w).val : RawForm Coordinates F n) x =
      ∑ᶠ i, φ i (coordinateProjection x) • ((w i).val : RawForm Coordinates F n) x := rfl

/-- Multiplying by a subordinate partition scalar removes the restriction mask on its true overlap. -/
theorem partitionExtend_restrict_apply (i : ι) (w : EquivariantForm ρ V n) (x : Coordinates)
    (hx : x ∈ liftedDomain V) :
    ((partitionExtend U hU φ hφ hV n i (restrictEquivariant ρ inter_subset_right n w)).val :
      RawForm Coordinates F n) x = φ i (coordinateProjection x) • (w.val : RawForm Coordinates F n) x := by
  change φ i (coordinateProjection x) •
    ((restrictEquivariant ρ inter_subset_right n w).val : RawForm Coordinates F n) x = _
  by_cases hxi : coordinateProjection x ∈ U i
  · have hxUV : x ∈ liftedDomain (U i ∩ V) := ⟨hx.1, hxi, hx.2⟩
    rw [restrictEquivariant_apply ρ _ _ hxUV]
  · have hz : φ i (coordinateProjection x) = 0 := by
      by_contra hn
      exact hxi (hφ i (subset_tsupport _ hn))
    rw [hz, zero_smul, zero_smul]

/-- Summing the genuine partition extensions of restrictions recovers the actual original form. -/
theorem partitionSum_restrict (w : EquivariantForm ρ V n) :
    partitionSum U hU φ hφ hV n (fun _ => restrictEquivariant ρ inter_subset_right n w) = w := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change (∑ᶠ i, ((partitionExtend U hU φ hφ hV n i
    (restrictEquivariant ρ inter_subset_right n w)).val : RawForm Coordinates F n) x) = _
  simp_rw [partitionExtend_restrict_apply U hU φ hφ hV n _ w x hx]
  rw [← finsum_smul, φ.sum_eq_one (Set.mem_univ _), one_smul]

end TernaryPoly.SmoothSingularGlobal
