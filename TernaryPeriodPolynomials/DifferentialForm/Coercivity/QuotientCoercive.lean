module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CoerciveTransport

@[expose] public section



/-! Degree-0 specialization of the quotient-integrated coercivity bound, mirroring
`scalarPairing_symmetric_energy_bound`/`integral_mono_add_const_mul`/`compactNormSq_bound`/
`integral_symmetric_energy_coercive`/`norm_symmetric_energy_coercive`. The single new generic
lemma `integral_mono_const_mul` is the single-term analog of the project's
`integral_mono_add_const_mul` (dropping its `.add`/`Pi.add_apply`/`integral_add` pieces, since
degree 0 has only one RHS term, not a sum of two). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- Pointwise bound descends to the scalar pairing, mirroring `scalarPairing_symmetric_energy_bound`. -/
theorem scalarPairing_symmetric_energy_bound_zero (n : ℕ) (c : ℝ)
    (h : ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ a : FormValue n 0,
      c * formPairing n 0 x a a ≤ formPairing n 1 x (symmetricExterior n 0 x a) (symmetricExterior n 0 x a))
    (a : CompactSupportForm (deckRepresentation n) univ 0) (q : OrbitSpace) :
    c * scalarPairing n 0 a.val a.val q ≤
      scalarPairing n 1 (compactSymmetricExterior n 0 a).val (compactSymmetricExterior n 0 a).val q :=
  (h _ (extract_mem (chosenLift q)) _).trans_eq (scalarPairing_symmetricExterior_self n 0 a q).symm

/-- Single-term analog of `integral_mono_add_const_mul`. -/
theorem integral_mono_const_mul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (c : ℝ) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (he : ∀ x, c * f x ≤ g x) : c * (∫ x, f x ∂μ) ≤ (∫ x, g x ∂μ) := by
  have hi := integral_mono (hf.const_mul c) hg he
  simpa only [integral_const_mul] using hi

/-- A proved pointwise bound integrates for genuine compact forms, mirroring `compactNormSq_bound`. -/
theorem compactNormSq_bound_zero (n : ℕ) (c : ℝ)
    (h : ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ a : FormValue n 0,
      c * formPairing n 0 x a a ≤ formPairing n 1 x (symmetricExterior n 0 x a) (symmetricExterior n 0 x a))
    (a : CompactSupportForm (deckRepresentation n) univ 0) :
    c * compactNormSq n 0 a ≤ compactNormSq n 1 (compactSymmetricExterior n 0 a) :=
  integral_mono_const_mul orbitVolume c _ _
    (integrable_scalarPairing n 0 a a.val)
    (integrable_scalarPairing n 1 (compactSymmetricExterior n 0 a) (compactSymmetricExterior n 0 a).val)
    (scalarPairing_symmetric_energy_bound_zero n c h a)

/-- Uniform coercivity integrated against the actual quotient volume, mirroring
`integral_symmetric_energy_coercive`. -/
theorem integral_symmetric_energy_coercive_zero {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : CompactSupportForm (deckRepresentation n) univ 0,
      c * compactNormSq n 0 a ≤ compactNormSq n 1 (compactSymmetricExterior n 0 a) := by
  exact Exists.imp (fun c h => ⟨h.1, compactNormSq_bound_zero n c h.2⟩)
    (symmetric_energy_coercive_zero (n := n) hn)

/-- Hilbert-norm form of the degree-0 coercivity bound, mirroring `norm_symmetric_energy_coercive`. -/
theorem norm_symmetric_energy_coercive_zero {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Core n 0,
      c * ‖inclusion n 0 a‖ ^ 2 ≤ ‖inclusion n 1 (compactSymmetricExterior n 0 a)‖ ^ 2 := by
  apply Exists.imp _ (integral_symmetric_energy_coercive_zero (n := n) hn)
  intro c hc
  refine ⟨hc.1, fun a => ?_⟩
  calc
    _ = c * compactNormSq n 0 a := congrArg (c * ·) (compactNormSq_eq_norm_sq n 0 a).symm
    _ ≤ _ := hc.2 a
    _ = _ := compactNormSq_eq_norm_sq n 1 (compactSymmetricExterior n 0 a)

end TernaryPeriodPolynomials.Argument.Coercivity
