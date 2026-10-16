module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.Transitions

@[expose] public section


/-! The actual smooth vector bundle glued by the arithmetic coefficient transitions. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientBundle
open PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
  SymmetricSpaceQuotientManifold SymmetricSpaceCharts
open Set Filter Topology Bundle
open scoped ContDiff Manifold

def bundleCore (n : ℕ) : VectorBundleCore ℝ OrbitSpace (Coefficients n) Space where
  baseSet S := (localLift S).source
  isOpen_baseSet S := (localLift S).open_source
  indexAt := chosenLift
  mem_baseSet_at b := by
    simpa only [chosenLift_projection] using self_mem_localLift (chosenLift b)
  coordChange := transition n
  coordChange_self S b _hb p := by simp [transition]
  continuousOn_coordChange S T := (transition_smooth n S T).continuousOn
  coordChange_comp S T U b hb p := by
    change coefficientAction n (transitionDeck T U b) (coefficientAction n (transitionDeck S T b) p) = _
    rw [← coefficientAction_mul, transitionDeck_comp S T U hb.1.1 hb.1.2 hb.2]
    rfl

instance bundleCore_smooth (n : ℕ) : (bundleCore n).IsContMDiff 𝓘(ℝ, Coordinates) ∞ where
  contMDiffOn_coordChange := transition_smooth n

abbrev Fiber (n : ℕ) := (bundleCore n).Fiber
abbrev Total (n : ℕ) := (bundleCore n).TotalSpace

def chart (n : ℕ) (S : Space) : Trivialization (Coefficients n) (π (Coefficients n) (Fiber n)) :=
  (bundleCore n).localTriv S

instance chart_linear (n : ℕ) (S : Space) : (chart n S).IsLinear ℝ := by
  unfold chart
  infer_instance

instance chart_memAtlas (n : ℕ) (S : Space) : MemTrivializationAtlas (chart n S) := by
  exact ⟨⟨S,rfl⟩⟩

@[simp] theorem chart_baseSet (n : ℕ) (S : Space) : (chart n S).baseSet = (localLift S).source := rfl

theorem chart_transition (n : ℕ) (S T : Space) {b : OrbitSpace}
    (hS : b ∈ (localLift S).source) (hT : b ∈ (localLift T).source) (p : Coefficients n) :
    (chart n S).coordChangeL ℝ (chart n T) b p = coefficientAction n (transitionDeck S T b) p :=
  (bundleCore n).localTriv_coordChange_eq S T ⟨hS,hT⟩ p

@[simp] theorem chosenLift_localLift (b : OrbitSpace) : localLift (chosenLift b) b = chosenLift b := by
  simpa only [chosenLift_projection] using localLift_self (chosenLift b)

@[simp] theorem chart_apply (n : ℕ) (S : Space) (z : Total n) :
    chart n S z = (z.proj, coefficientAction n (deckBetween (chosenLift z.proj) (localLift S z.proj)) z.snd) := by
  change (z.proj, transition n (chosenLift z.proj) S z.proj z.snd) = _
  simp only [transition, transitionDeck, chosenLift_localLift]

end TernaryPoly.PolynomialCoefficientBundle
