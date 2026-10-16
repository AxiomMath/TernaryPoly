module

public import TernaryPeriodPolynomials.DifferentialForm.Deck.Algebra
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.DeckIntegral

@[expose] public section


/-! Exact invariance of genuine local form integrals under normalized deck pullback. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
open SmoothCoveringDeRham Set MeasureTheory

/-- The literal coordinate-density form integral. -/
def localIntegral (n k : ℕ) (f g : Coordinates → FormValue n k) : ℝ :=
  ∫ x, coordinateDensity x * formPairing n k x (f x) (g x)

theorem localIntegral_eq_setIntegral (n k : ℕ) (f g : Coordinates → FormValue n k)
    (hf : ∀ x ∉ positiveCoordinates, f x = 0) :
    localIntegral n k f g = ∫ x in positiveCoordinates,
      coordinateDensity x * formPairing n k x (f x) (g x) := by
  apply Eq.symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [hf x hx, formPairing_zero_left, mul_zero]

/-- Equality on the true coordinate domain suffices for compactly supported first factors. -/
theorem localIntegral_congr (n k : ℕ) {f g a b : Coordinates → FormValue n k}
    (hfa : EqOn f a positiveCoordinates) (hgb : EqOn g b positiveCoordinates)
    (hf : ∀ x ∉ positiveCoordinates, f x = 0) (ha : ∀ x ∉ positiveCoordinates, a x = 0) :
    localIntegral n k f g = localIntegral n k a b := by
  rw [localIntegral_eq_setIntegral n k f g hf, localIntegral_eq_setIntegral n k a b ha]
  apply setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet
  intro x hx
  dsimp only
  rw [hfa hx, hgb hx]

/-- The genuine weighted integral is unchanged when both forms are pulled back by a deck map. -/
theorem localIntegral_deckPull (n k : ℕ) (a : DeckGroup) (f g : Coordinates → FormValue n k)
    (hf : ∀ x ∉ positiveCoordinates, f x = 0) :
    localIntegral n k (deckPull n k a f) (deckPull n k a g) = localIntegral n k f g := by
  rw [localIntegral_eq_setIntegral n k _ _ (fun x hx => deckPull_of_notMem n k a f hx),
    localIntegral_eq_setIntegral n k f g hf]
  calc
    _ = ∫ x in positiveCoordinates, coordinateDensity x *
        formPairing n k (deckMap a x) (f (deckMap a x)) (g (deckMap a x)) := by
      apply setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet
      intro x hx
      dsimp only
      rw [formPairing_deckPull n k a f g hx]
    _ = _ := integral_coordinateDensity_deck a (fun x => formPairing n k x (f x) (g x))

/-- Move a genuine deck pullback from the second factor to the inverse pullback of the first. -/
theorem localIntegral_deckPull_right (n k : ℕ) (a : DeckGroup) (f g : Coordinates → FormValue n k)
    (hf : ∀ x ∉ positiveCoordinates, f x = 0) :
    localIntegral n k f (deckPull n k a g) = localIntegral n k (deckPull n k a⁻¹ f) g := by
  have he := localIntegral_congr n k (g := deckPull n k a g)
    (fun _ hx => deckPull_inverse n k a f hx) (fun _ _ => rfl)
    (fun _ hx => deckPull_of_notMem n k a (deckPull n k a⁻¹ f) hx) hf
  exact he.symm.trans (localIntegral_deckPull n k a (deckPull n k a⁻¹ f) g
    (fun _ hx => deckPull_of_notMem n k a⁻¹ f hx))

end TernaryPoly.PolynomialFormCoordinates
