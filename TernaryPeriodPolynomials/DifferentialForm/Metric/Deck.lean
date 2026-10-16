module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Naturality
public import TernaryPeriodPolynomials.DifferentialForm.Metric.Smooth

@[expose] public section


/-! Exact invariance for the actual deck pullback convention of the covering de Rham complex. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open Matrix SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceTraceMetric SymmetricSpaceRiemannian PolynomialCoefficientMetric
open SmoothCoveringDeRham SmoothLocalDeRham

 theorem coordinateGram_deck (g : DeckGroup) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    (LinearMap.toMatrix' (fderiv ℝ (deckMap g) x).toLinearMap).transpose *
      coordinateGram (deckMap g x) *
        LinearMap.toMatrix' (fderiv ℝ (deckMap g) x).toLinearMap = coordinateGram x := by
  let L := (fderiv ℝ (deckMap g) x).toLinearMap
  have h : LinearMap.BilinForm.comp (coordinateBilin (deckMap g x)) L L = coordinateBilin x := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact coordinatePair_fderiv_invariant
      (SymmetricSpaceArithmeticProper.realIntegral (deckInclusion g)) x hx v w
  have hm := congrArg LinearMap.BilinForm.toMatrix' h
  simpa only [LinearMap.BilinForm.toMatrix'_comp, coordinateGram, L] using hm

theorem inverseGram_deck (g : DeckGroup) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    LinearMap.toMatrix' (fderiv ℝ (deckMap g) x).toLinearMap * inverseGram x *
      (LinearMap.toMatrix' (fderiv ℝ (deckMap g) x).toLinearMap).transpose =
        inverseGram (deckMap g x) :=
  inverse_congruence _ _ _ (coordinateGram_posDef x hx) (coordinateGram_deck g x hx)

theorem coordinateCoefficientBilin_deck (n : ℕ) (g : DeckGroup) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (p q : Coefficients n) :
    coordinateCoefficientBilin n (deckMap g x) (deckRepresentation n g p) (deckRepresentation n g q) =
      coordinateCoefficientBilin n x p q := by
  have h := coefficientMetric_deck_invariant n g (coordinateChart.symm x) p q
  rw [← coefficientMetric_coordinates, ← deckMap_chart,
    coordinateChart.right_inv (show x ∈ coordinateChart.target by simpa using hx),
    ← coefficientMetric_coordinates,
    coordinateChart.right_inv (show x ∈ coordinateChart.target by simpa using hx)] at h
  exact h

/-- Pairing is invariant when genuine tangent pullback equals the genuine coefficient action. -/
theorem formPairing_deck (n k : ℕ) (g : DeckGroup) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (a b c d : FormValue n k)
    (ha : a.compContinuousLinearMap (fderiv ℝ (deckMap g) x) =
      coefficientFormMap (coefficientMap (deckRepresentation n) g) k c)
    (hb : b.compContinuousLinearMap (fderiv ℝ (deckMap g) x) =
      coefficientFormMap (coefficientMap (deckRepresentation n) g) k d) :
    formPairing n k (deckMap g x) a b = formPairing n k x c d := by
  unfold formPairing
  apply congrArg ((k.factorial : ℝ)⁻¹ * ·)
  unfold inverseGram
  rw [← contraction_isometry (coordinateCoefficientBilin n (deckMap g x))
    (coordinateGram x) (coordinateGram (deckMap g x)) (coordinateGram_posDef x hx)
    (fderiv ℝ (deckMap g) x) (coordinateGram_deck g x hx) a b, ha, hb]
  unfold matrixContraction
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  apply congrArg (tensorMatrix k (inverseGram x) I J * ·)
  exact coordinateCoefficientBilin_deck n g x hx (formCoordinates c I) (formCoordinates d J)

/-- Actual equivariant covering forms have an invariant scalar pairing. -/
theorem equivariant_formPairing (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k)
    (g : DeckGroup) (x : Coordinates) (hx : x ∈ liftedDomain U) :
    formPairing n k (deckMap g x) (a.val.val (deckMap g x)) (b.val.val (deckMap g x)) =
      formPairing n k x (a.val.val x) (b.val.val x) :=
  formPairing_deck n k g x hx.1 _ _ _ _ (a.property g x hx) (b.property g x hx)

end TernaryPoly.PolynomialFormMetric
