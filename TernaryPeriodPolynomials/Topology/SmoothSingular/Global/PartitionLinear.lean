module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.PartitionSum

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

/-- Actual partition summands have finite nonzero values at every covering point. -/
theorem partitionSummands_finite (w : ∀ i, EquivariantForm ρ (U i ∩ V) n) (x : Coordinates) :
    (Function.support (fun i => φ i (coordinateProjection x) •
      ((w i).val : RawForm Coordinates F n) x)).Finite := by
  exact (φ.locallyFinite.point_finite (coordinateProjection x)).subset (fun i hi => by
    change φ i (coordinateProjection x) ≠ 0
    intro hz
    apply hi
    change φ i (coordinateProjection x) • ((w i).val : RawForm Coordinates F n) x = 0
    rw [hz, zero_smul])

/-- Genuine partition summation is additive. -/
theorem partitionSum_add (w z : ∀ i, EquivariantForm ρ (U i ∩ V) n) :
    partitionSum U hU φ hφ hV n (w + z) =
      partitionSum U hU φ hφ hV n w + partitionSum U hU φ hφ hV n z := by
  apply Subtype.ext
  apply Form.ext
  intro x _
  change (∑ᶠ i, φ i (coordinateProjection x) •
    (((w i).val : RawForm Coordinates F n) x + ((z i).val : RawForm Coordinates F n) x)) = _
  simp_rw [smul_add]
  exact finsum_add_distrib (partitionSummands_finite U φ n w x) (partitionSummands_finite U φ n z x)

/-- Genuine partition summation is linear in the real form coefficients. -/
theorem partitionSum_smul (c : ℝ) (w : ∀ i, EquivariantForm ρ (U i ∩ V) n) :
    partitionSum U hU φ hφ hV n (c • w) = c • partitionSum U hU φ hφ hV n w := by
  apply Subtype.ext
  apply Form.ext
  intro x _
  change (∑ᶠ i, φ i (coordinateProjection x) •
    (c • ((w i).val : RawForm Coordinates F n) x)) = _
  simp_rw [smul_comm (φ _ _) c]
  exact (smul_finsum' c (partitionSummands_finite U φ n w x)).symm

/-- The actual partition summation operator on all overlap forms is a real linear map. -/
def partitionSumLinear : (∀ i, EquivariantForm ρ (U i ∩ V) n) →ₗ[ℝ] EquivariantForm ρ V n where
  toFun := partitionSum U hU φ hφ hV n
  map_add' := partitionSum_add U hU φ hφ hV n
  map_smul' := partitionSum_smul U hU φ hφ hV n

/-- The genuine partition homotopy operator commutes with all actual restrictions of its
unweighted open domain, including the overlaps of a Čech cover. -/
theorem partitionSum_restriction {W : Set OrbitSpace} (hW : IsOpen W) (hWV : W ⊆ V)
    (w : ∀ i, EquivariantForm ρ (U i ∩ V) n) :
    restrictEquivariant ρ hWV n (partitionSum U hU φ hφ hV n w) =
      partitionSum U hU φ hφ hW n
        (fun i => restrictEquivariant ρ (inter_subset_inter_right (U i) hWV) n (w i)) := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rw [restrictEquivariant_apply ρ _ _ hx]
  rw [partitionSum_apply, partitionSum_apply]
  apply finsum_congr
  intro i
  by_cases hxi : coordinateProjection x ∈ U i
  · have hxUW : x ∈ liftedDomain (U i ∩ W) := ⟨hx.1, hxi, hx.2⟩
    rw [restrictEquivariant_apply ρ _ _ hxUW]
  · have hz : φ i (coordinateProjection x) = 0 := by
      by_contra hn
      exact hxi (hφ i (subset_tsupport _ hn))
    rw [hz, zero_smul, zero_smul]

end TernaryPoly.SmoothSingularGlobal
