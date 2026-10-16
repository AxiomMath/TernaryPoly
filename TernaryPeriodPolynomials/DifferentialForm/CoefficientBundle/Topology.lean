module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.Quotient

@[expose] public section

/-! The genuine quotient topology agrees with the topology of the smooth glued bundle. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientBundle
open PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
  SymmetricSpaceQuotientManifold SymmetricSpaceCharts
open Set Filter Topology Bundle
open scoped ContDiff Manifold

theorem localLift_projection (S R : Space) (hR : R ∈ (localLift S).target) :
    localLift S (quotientProjection R) = R := by
  rw [← localLift_symm S]
  exact (localLift S).right_inv hR

theorem liftToTotal_chart (n : ℕ) (S R : Space) (p : Coefficients n)
    (hR : R ∈ (localLift S).target) :
    chart n S (liftToTotal n (R,p)) = (quotientProjection R,p) := by
  rw [chart_apply]
  change (quotientProjection R, coefficientAction n
    (deckBetween (chosenLift (quotientProjection R)) (localLift S (quotientProjection R)))
    (coefficientAction n (deckBetween R (chosenLift (quotientProjection R))) p)) = _
  rw [localLift_projection S R hR, ← coefficientAction_mul,
    deckBetween_comp R _ R (chosenLift_projection _) (chosenLift_projection _).symm,
    deckBetween_self, coefficientAction_one]

theorem continuous_liftToTotal (n : ℕ) : Continuous (liftToTotal n) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hm : z.1 ∈ (localLift z.1).target := by
    simpa only [localLift_self] using (localLift z.1).map_source (self_mem_localLift z.1)
  apply (chart n z.1).continuousAt_of_comp_left (f := liftToTotal n) (x := z)
    (quotientProjection_covering.continuous.comp continuous_fst).continuousAt (self_mem_localLift z.1)
  have he : (chart n z.1) ∘ liftToTotal n =ᶠ[𝓝 z]
      (fun w : Space × Coefficients n => (quotientProjection w.1,w.2)) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds ((localLift z.1).open_target.mem_nhds hm)] with w hw
    exact liftToTotal_chart n z.1 w.1 w.2 hw
  exact ((quotientProjection_covering.continuous.comp continuous_fst).prodMk continuous_snd).continuousAt.congr_of_eventuallyEq he

theorem continuous_quotientToTotal (n : ℕ) : Continuous (quotientToTotal n) :=
  (continuous_liftToTotal n).quotient_lift _

theorem totalToQuotient_chart (n : ℕ) (S : Space) (z : Total n)
    (hz : z.proj ∈ (localLift S).source) :
    totalToQuotient n z = orbitClass n (localLift S z.proj) (chart n S z).2 := by
  rw [chart_apply]
  have h := orbitClass_smul n (deckBetween (chosenLift z.proj) (localLift S z.proj)) (chosenLift z.proj) z.snd
  rw [deckBetween_spec _ _ ((projection_localLift S hz).trans (chosenLift_projection z.proj).symm)] at h
  exact h.symm

theorem continuous_totalToQuotient (n : ℕ) : Continuous (totalToQuotient n) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let S := chosenLift z.proj
  have hb : z.proj ∈ (localLift S).source := (bundleCore n).mem_baseSet_at z.proj
  have hz : z ∈ (chart n S).source := hb
  have hp := ((bundleCore n).continuous_proj).continuousAt (x := z)
  have hlocal := ((localLift S).continuousAt hb).comp hp
  have hchart := ((chart n S).continuousAt hz).snd
  have h : ContinuousAt (fun w : Total n => orbitClass n (localLift S w.proj) (chart n S w).2) z :=
    continuous_quotient_mk'.continuousAt.comp (hlocal.prodMk hchart)
  apply h.congr_of_eventuallyEq
  filter_upwards [(chart n S).open_source.mem_nhds hz] with w hw
  exact totalToQuotient_chart n S w hw

/-- The atlas bundle has exactly the topology of the literal diagonal orbit quotient. -/
def associatedHomeomorph (n : ℕ) : Associated n ≃ₜ Total n where
  toEquiv := associatedEquiv n
  continuous_toFun := continuous_quotientToTotal n
  continuous_invFun := continuous_totalToQuotient n

end TernaryPoly.PolynomialCoefficientBundle
