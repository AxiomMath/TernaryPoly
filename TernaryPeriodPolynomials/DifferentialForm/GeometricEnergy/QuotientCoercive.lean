module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.QuotientAlgebra

@[expose] public section

/-! Uniform positivity of actual algebraic symmetric energy in the quotient integral. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open PolynomialCoefficientBundle PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormCoordinates
open SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
open SmoothCoveringDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

theorem scalarPairing_symmetric_energy_bound (n : ℕ) (c : ℝ)
    (h : ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ a : FormValue n 2,
      c * formPairing n 2 x a a ≤
        formPairing n 1 x (symmetricContraction n 1 x a) (symmetricContraction n 1 x a) +
        formPairing n 3 x (symmetricExterior n 2 x a) (symmetricExterior n 2 x a))
    (a : CompactSupportForm (deckRepresentation n) univ 2) (q : OrbitSpace) :
    c * scalarPairing n 2 a.val a.val q ≤
      scalarPairing n 1 (compactSymmetricContraction n 1 a).val (compactSymmetricContraction n 1 a).val q +
      scalarPairing n 3 (compactSymmetricExterior n 2 a).val (compactSymmetricExterior n 2 a).val q :=
  (h _ (extract_mem (chosenLift q)) _).trans_eq
    (congrArg₂ (· + ·) (scalarPairing_symmetricContraction_self n 1 a q).symm
      (scalarPairing_symmetricExterior_self n 2 a q).symm)

theorem integral_mono_add_const_mul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (c : ℝ) (f g h : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (he : ∀ x, c * f x ≤ g x + h x) : c * (∫ x, f x ∂μ) ≤ (∫ x, g x ∂μ) + (∫ x, h x ∂μ) := by
  have hi := integral_mono (hf.const_mul c) (hg.add hh) he
  simpa only [Pi.add_apply, integral_const_mul, integral_add hg hh] using hi

/-- The genuine quotient integral of the pointwise squared metric norm. -/
def compactNormSq (n k : ℕ) (a : CompactSupportForm (deckRepresentation n) univ k) : ℝ :=
  ∫ q, scalarPairing n k a.val a.val q ∂orbitVolume

/-- A proved pointwise symmetric-energy bound integrates for genuine compact forms. -/
theorem compactNormSq_bound (n : ℕ) (c : ℝ)
    (h : ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ a : FormValue n 2,
      c * formPairing n 2 x a a ≤
        formPairing n 1 x (symmetricContraction n 1 x a) (symmetricContraction n 1 x a) +
        formPairing n 3 x (symmetricExterior n 2 x a) (symmetricExterior n 2 x a))
    (a : CompactSupportForm (deckRepresentation n) univ 2) :
    c * compactNormSq n 2 a ≤ compactNormSq n 1 (compactSymmetricContraction n 1 a) +
      compactNormSq n 3 (compactSymmetricExterior n 2 a) :=
  integral_mono_add_const_mul orbitVolume c _ _ _
    (integrable_scalarPairing n 2 a a.val)
    (integrable_scalarPairing n 1 (compactSymmetricContraction n 1 a) (compactSymmetricContraction n 1 a).val)
    (integrable_scalarPairing n 3 (compactSymmetricExterior n 2 a) (compactSymmetricExterior n 2 a).val)
    (scalarPairing_symmetric_energy_bound n c h a)

/-- Uniform coercivity integrated against the actual arithmetic quotient volume. -/
theorem integral_symmetric_energy_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : CompactSupportForm (deckRepresentation n) univ 2,
      c * compactNormSq n 2 a ≤ compactNormSq n 1 (compactSymmetricContraction n 1 a) +
        compactNormSq n 3 (compactSymmetricExterior n 2 a) := by
  exact Exists.imp (fun c h => ⟨h.1, compactNormSq_bound n c h.2⟩)
    (symmetric_energy_coercive (n := n) hn)

end TernaryPoly.PolynomialFormGeometricEnergy
