module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.Descent
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.DeRham

@[expose] public section

/-! Literal pointwise comparisons for quotient classes, local de Rham representatives, and metrics. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientBundle
open PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
  SymmetricSpaceCharts SmoothLocalDeRham SmoothCoveringDeRham
open Set Bundle

theorem sectionFunction_orbitClass (n : ℕ) (s : Section n) (S : Space) :
    orbitClass n S (sectionFunction n s S) = totalToQuotient n (sectionMap n s (quotientProjection S)) := by
  have h := orbitClass_smul n (deckBetween (chosenLift (quotientProjection S)) S)
    (chosenLift (quotientProjection S)) (s (quotientProjection S))
  rw [deckBetween_spec _ _ (chosenLift_projection _).symm] at h
  exact h

theorem sectionFunction_metric (n : ℕ) (s t : Section n) (S : Space) :
    coefficientMetric n S (sectionFunction n s S) (sectionFunction n t S) =
      fiberMetric n (quotientProjection S) (s (quotientProjection S)) (t (quotientProjection S)) := by
  have h := coefficientMetric_deck_invariant n (deckBetween (chosenLift (quotientProjection S)) S)
    (chosenLift (quotientProjection S)) (s (quotientProjection S)) (t (quotientProjection S))
  rw [deckBetween_spec _ _ (chosenLift_projection _).symm] at h
  exact h

theorem sectionToZeroForm_covering_value (n : ℕ) {U : Set OrbitSpace} (hU : IsOpen U)
    (s : SmoothSectionOn n U) (S : Space) :
    zeroFormFunction n (sectionToZeroForm n hU s) S = sectionFunction n s.val S :=
  congrFun (zeroFormFunction_coveringZeroForm n (sectionFunction n s.val) _ _
    (fun _R hR => sectionFunction_outside n s.val s.property.2 hR)) S

/-- In the actual local bundle chart the section is exactly the already-used coefficient
function obtained by evaluating its covering zero-form at the actual quotient coordinate. -/
theorem zeroFormToSection_chart_value (n : ℕ) {U : Set OrbitSpace} (hU : IsOpen U)
    (w : EquivariantForm (deckRepresentation n) U 0) (S : Space) {b : OrbitSpace}
    (hb : b ∈ (localLift S).source) :
    (chart n S (sectionMap n (zeroFormToSection n hU w).val b)).2 =
      toFunction w.val (quotientChart S b) :=
  functionSection_chart n (zeroFormFunction n w) (zeroFormFunction_equivariant n w) S hb

/-- The actual bundle transition is the full tensor scalar extension of the literal
principal-six rational polynomial transition, for every determinant twist. -/
theorem transition_scalarExtension (n : ℕ) (e : ℤ) (S T : Space) (b : OrbitSpace)
    (z : ExtendedCoefficients n) :
    coefficientScalarExtension n ((rationalDeckRepresentation n e (transitionDeck S T b)).baseChange ℝ z) =
      transition n S T b (coefficientScalarExtension n z) :=
  coefficientScalarExtension_equivariant n e (transitionDeck S T b) z

end TernaryPoly.PolynomialCoefficientBundle
