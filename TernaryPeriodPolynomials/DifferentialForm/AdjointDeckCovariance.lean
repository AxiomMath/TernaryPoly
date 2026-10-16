module

public import TernaryPeriodPolynomials.DifferentialForm.Deck.Integration
public import TernaryPeriodPolynomials.DifferentialForm.LocalIntegrationTest
public import TernaryPeriodPolynomials.DifferentialForm.TestPairing

@[expose] public section


/-! The actual local adjoint commutes with coefficient-normalized deck pullback. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
open SmoothCoveringDeRham SmoothLocalDeRham Set MeasureTheory
open scoped ContDiff

/-- Exact naturality of the genuine coordinate adjoint, proved from actual compact form tests. -/
theorem localAdjoint_deckPull (n k : ℕ) (a : DeckGroup) {w : Coordinates → FormValue n (k + 1)}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) :
    EqOn (localAdjoint n k (deckPull n (k + 1) a w))
      (deckPull n k a (localAdjoint n k w)) positiveCoordinates := by
  apply eqOn_of_form_test_integrals n k
    (contDiffOn_localAdjoint n k (contDiffOn_deckPull n (k + 1) a hw))
    (contDiffOn_deckPull n k a (contDiffOn_localAdjoint n k hw))
  intro f hf hc hs
  let t := deckPull n k a⁻¹ f
  have ht : ContDiffOn ℝ ∞ t positiveCoordinates := contDiffOn_deckPull n k a⁻¹ hf.contDiffOn
  have htc : HasCompactSupport t := hasCompactSupport_deckPull n k a⁻¹ f hc hs
  have hts : tsupport t ⊆ positiveCoordinates := tsupport_deckPull_positive n k a⁻¹ f hc hs
  have hf0 (x : Coordinates) (hx : x ∉ positiveCoordinates) : f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh))
  have hdf0 (x : Coordinates) (hx : x ∉ positiveCoordinates) : extDeriv f x = 0 :=
    extDeriv_eq_zero_of_notMem_tsupport n k f (fun hh => hx (hs hh))
  have hdt0 (x : Coordinates) (hx : x ∉ positiveCoordinates) : extDeriv t x = 0 :=
    extDeriv_eq_zero_of_notMem_tsupport n k t (fun hh => hx (hts hh))
  change localIntegral n k f (localAdjoint n k (deckPull n (k + 1) a w)) =
    localIntegral n k f (deckPull n k a (localAdjoint n k w))
  calc
    _ = localIntegral n (k + 1) (extDeriv f) (deckPull n (k + 1) a w) :=
      (integral_extDeriv_localAdjoint_test n k f (deckPull n (k + 1) a w)
        hf.contDiffOn (contDiffOn_deckPull n (k + 1) a hw) hc hs).symm
    _ = localIntegral n (k + 1) (deckPull n (k + 1) a⁻¹ (extDeriv f)) w :=
      localIntegral_deckPull_right n (k + 1) a (extDeriv f) w hdf0
    _ = localIntegral n (k + 1) (extDeriv t) w := by
      apply localIntegral_congr n (k + 1)
      · intro x hx
        exact (extDeriv_deckPull n k a⁻¹ hf.contDiffOn hx).symm
      · intro _ _; rfl
      · intro x hx
        exact deckPull_of_notMem n (k + 1) a⁻¹ (extDeriv f) hx
      · exact hdt0
    _ = localIntegral n k t (localAdjoint n k w) :=
      integral_extDeriv_localAdjoint_test n k t w ht hw htc hts
    _ = _ := (localIntegral_deckPull_right n k a f (localAdjoint n k w) hf0).symm

end TernaryPoly.PolynomialFormCoordinates
