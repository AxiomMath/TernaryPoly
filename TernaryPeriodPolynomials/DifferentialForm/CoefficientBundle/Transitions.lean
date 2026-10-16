module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Admissible
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

@[expose] public section


/-! Genuine locally constant coefficient transitions from the actual covering sections. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientBundle
open PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
  SymmetricSpaceQuotientManifold SymmetricSpaceCharts
open Set Filter Topology
open scoped ContDiff Manifold

def chosenLift (b : OrbitSpace) : Space := Classical.choose (quotientProjection_surjective b)

@[simp] theorem chosenLift_projection (b : OrbitSpace) : quotientProjection (chosenLift b) = b :=
  Classical.choose_spec (quotientProjection_surjective b)

def deckBetween (S T : Space) : DeckGroup := by
  classical
  exact if h : quotientProjection T = quotientProjection S then
    Classical.choose (quotientProjection_quotientCovering.apply_eq_iff_mem_orbit.mp h) else 1

theorem deckBetween_spec (S T : Space) (h : quotientProjection T = quotientProjection S) :
    deckBetween S T • S = T := by
  simp only [deckBetween, dite_eq_left h]
  exact Classical.choose_spec (quotientProjection_quotientCovering.apply_eq_iff_mem_orbit.mp h)

theorem deckBetween_unique (S T : Space) (g : DeckGroup) (hg : g • S = T) : deckBetween S T = g := by
  have h : quotientProjection T = quotientProjection S := by
    rw [← hg, quotientProjection_quotientCovering.map_smul]
  exact IsCancelSMul.right_cancel _ _ _ ((deckBetween_spec S T h).trans hg.symm)

@[simp] theorem deckBetween_self (S : Space) : deckBetween S S = 1 :=
  deckBetween_unique S S 1 (one_smul _ _)

theorem deckBetween_comp (S T U : Space)
    (hT : quotientProjection T = quotientProjection S) (hU : quotientProjection U = quotientProjection T) :
    deckBetween T U * deckBetween S T = deckBetween S U := by
  symm
  apply deckBetween_unique
  rw [mul_smul, deckBetween_spec S T hT, deckBetween_spec T U hU]

def transitionDeck (S T : Space) (b : OrbitSpace) : DeckGroup :=
  deckBetween (localLift S b) (localLift T b)

theorem transitionDeck_spec (S T : Space) {b : OrbitSpace}
    (hS : b ∈ (localLift S).source) (hT : b ∈ (localLift T).source) :
    transitionDeck S T b • localLift S b = localLift T b :=
  deckBetween_spec _ _ ((projection_localLift T hT).trans (projection_localLift S hS).symm)

@[simp] theorem transitionDeck_self (S : Space) (b : OrbitSpace) : transitionDeck S S b = 1 :=
  deckBetween_self _

theorem transitionDeck_comp (S T U : Space) {b : OrbitSpace}
    (hS : b ∈ (localLift S).source) (hT : b ∈ (localLift T).source) (hU : b ∈ (localLift U).source) :
    transitionDeck T U b * transitionDeck S T b = transitionDeck S U b :=
  deckBetween_comp _ _ _ ((projection_localLift T hT).trans (projection_localLift S hS).symm)
    ((projection_localLift U hU).trans (projection_localLift T hT).symm)

theorem transitionDeck_eventually (S T : Space) {b : OrbitSpace}
    (hS : b ∈ (localLift S).source) (hT : b ∈ (localLift T).source) :
    transitionDeck S T =ᶠ[𝓝 b] fun _ => transitionDeck S T b := by
  obtain ⟨g, hg⟩ := localLift_eventually_deck S T b hS hT
  have h0 : transitionDeck S T b = g := deckBetween_unique _ _ g (hg.self_of_nhds.symm)
  filter_upwards [hg] with c hc
  exact (deckBetween_unique _ _ g hc.symm).trans h0.symm

def coefficientAction (n : ℕ) (g : DeckGroup) : Coefficients n →L[ℝ] Coefficients n :=
  (deckRepresentation n g).toContinuousLinearMap

@[simp] theorem coefficientAction_apply (n : ℕ) (g : DeckGroup) (p : Coefficients n) :
    coefficientAction n g p = deckRepresentation n g p := rfl

@[simp] theorem coefficientAction_one (n : ℕ) (p : Coefficients n) : coefficientAction n 1 p = p := by
  simp [coefficientAction]

theorem coefficientAction_mul (n : ℕ) (g h : DeckGroup) (p : Coefficients n) :
    coefficientAction n (g*h) p = coefficientAction n g (coefficientAction n h p) := by
  simp [coefficientAction, Module.End.mul_apply]

def transition (n : ℕ) (S T : Space) (b : OrbitSpace) : Coefficients n →L[ℝ] Coefficients n :=
  coefficientAction n (transitionDeck S T b)

theorem transition_smooth (n : ℕ) (S T : Space) :
    ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n →L[ℝ] Coefficients n) ∞
      (transition n S T) ((localLift S).source ∩ (localLift T).source) := by
  intro b hb
  have he : transition n S T =ᶠ[𝓝 b] fun _ => transition n S T b :=
    (transitionDeck_eventually S T hb.1 hb.2).fun_comp (coefficientAction n)
  exact (contMDiffAt_const.congr_of_eventuallyEq he).contMDiffWithinAt

end TernaryPoly.PolynomialCoefficientBundle
