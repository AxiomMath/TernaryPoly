module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Descent

@[expose] public section

/-! Smooth quotient scalar functions from genuine smooth equivariant forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold PolynomialCoefficientMetric PolynomialCoefficientBundle
open SmoothCoveringDeRham SmoothLocalDeRham Set Filter
open scoped ContDiff Manifold Topology

theorem contMDiffOn_coveringPairing (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k) :
    ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (coveringPairing n k a b)
      (quotientProjection ⁻¹' U) := by
  have h := contDiffOn_formPairing_functions n k (s := liftedDomain U) (fun _ hx => hx.1)
    (Form.smooth a.val) (Form.smooth b.val)
  apply h.contMDiffOn.comp coordinateChart_contMDiff.contMDiffOn
  intro S hS
  refine ⟨extract_mem S, ?_⟩
  simpa only [Set.mem_preimage, coordinateProjection, coordinateChart.left_inv (by simp)] using hS

/-- For a local form the scalar is smooth on its genuine open domain. -/
theorem contMDiffOn_scalarPairing (n k : ℕ) {U : Set OrbitSpace} (hU : IsOpen U)
    (a b : EquivariantForm (deckRepresentation n) U k) :
    ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (scalarPairing n k a b) U := by
  intro q hqU
  let S := chosenLift q
  have hq : q ∈ (localLift S).source := (bundleCore n).mem_baseSet_at q
  have hlU : localLift S q ∈ quotientProjection ⁻¹' U := by
    change quotientProjection (localLift S q) ∈ U
    rw [projection_localLift S hq]
    exact hqU
  have hf := ((contMDiffOn_coveringPairing n k a b) _ hlU).contMDiffAt
    ((hU.preimage quotientProjection_covering.continuous).mem_nhds hlU)
  have h := hf.comp q ((localLift_contMDiffOn S).contMDiffAt ((localLift S).open_source.mem_nhds hq))
  apply ContMDiffAt.contMDiffWithinAt
  apply h.congr_of_eventuallyEq
  filter_upwards [(localLift S).open_source.mem_nhds hq] with r hr
  exact scalarPairing_localLift n k a b S hr

/-- Pairing two global smooth forms gives a genuine smooth function on OrbitSpace. -/
theorem contMDiff_scalarPairing (n k : ℕ)
    (a b : EquivariantForm (deckRepresentation n) Set.univ k) :
    ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (scalarPairing n k a b) :=
  contMDiffOn_univ.mp (contMDiffOn_scalarPairing n k isOpen_univ a b)

theorem continuous_scalarPairing (n k : ℕ)
    (a b : EquivariantForm (deckRepresentation n) Set.univ k) :
    Continuous (scalarPairing n k a b) := (contMDiff_scalarPairing n k a b).continuous

end TernaryPoly.PolynomialFormMetric
