module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CoerciveTransportDegreeFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CancellationDegreeFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.QuotientCoercive

@[expose] public section



/-! Degree-4 quotient-integrated coercivity and final assembly, mirroring `CoercivityThree.lean`
one degree up: the Symmetric pieces are `compactSymmetricExterior n 4` (4 to 5) and
`compactSymmetricContraction n 3` (4 to 3); the final assembly drops the nonnegative sum of the two
Covariant pieces from `compact_energy_identity_degree_four`, closing clause `k = 3` of
Proposition C.1.

Formalized by Claude Sonnet 5.5. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- Pointwise sum-bound descends to the scalar pairing. -/
theorem scalarPairing_symmetric_energy_bound_degree_four (n : ℕ) (c : ℝ)
    (h : ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ w : FormValue n 4,
      c * formPairing n 4 x w w ≤
        formPairing n 5 x (symmetricExterior n 4 x w) (symmetricExterior n 4 x w) +
        formPairing n 3 x (symmetricContraction n 3 x w) (symmetricContraction n 3 x w))
    (a : CompactSupportForm (deckRepresentation n) univ 4) (q : OrbitSpace) :
    c * scalarPairing n 4 a.val a.val q ≤
      scalarPairing n 5 (compactSymmetricExterior n 4 a).val (compactSymmetricExterior n 4 a).val q +
      scalarPairing n 3 (compactSymmetricContraction n 3 a).val (compactSymmetricContraction n 3 a).val q :=
  (h _ (extract_mem (chosenLift q)) _).trans_eq
    (congrArg₂ (· + ·) (scalarPairing_symmetricExterior_self n 4 a q)
      (scalarPairing_symmetricContraction_self n 3 a q)).symm

/-- A proved pointwise sum-bound integrates for genuine compact forms. -/
theorem compactNormSq_bound_degree_four (n : ℕ) (c : ℝ)
    (h : ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ w : FormValue n 4,
      c * formPairing n 4 x w w ≤
        formPairing n 5 x (symmetricExterior n 4 x w) (symmetricExterior n 4 x w) +
        formPairing n 3 x (symmetricContraction n 3 x w) (symmetricContraction n 3 x w))
    (a : CompactSupportForm (deckRepresentation n) univ 4) :
    c * compactNormSq n 4 a ≤
      compactNormSq n 5 (compactSymmetricExterior n 4 a) +
        compactNormSq n 3 (compactSymmetricContraction n 3 a) := by
  have hmono := integral_mono_const_mul orbitVolume c
    (fun q => scalarPairing n 4 a.val a.val q)
    (fun q => scalarPairing n 5 (compactSymmetricExterior n 4 a).val (compactSymmetricExterior n 4 a).val q +
      scalarPairing n 3 (compactSymmetricContraction n 3 a).val (compactSymmetricContraction n 3 a).val q)
    (integrable_scalarPairing n 4 a a.val)
    ((integrable_scalarPairing n 5 (compactSymmetricExterior n 4 a) (compactSymmetricExterior n 4 a).val).add
      (integrable_scalarPairing n 3 (compactSymmetricContraction n 3 a) (compactSymmetricContraction n 3 a).val))
    (scalarPairing_symmetric_energy_bound_degree_four n c h a)
  rwa [integral_add
    (integrable_scalarPairing n 5 (compactSymmetricExterior n 4 a) (compactSymmetricExterior n 4 a).val)
    (integrable_scalarPairing n 3 (compactSymmetricContraction n 3 a) (compactSymmetricContraction n 3 a).val)]
    at hmono

/-- Uniform sum-coercivity integrated against the quotient volume. -/
theorem integral_symmetric_energy_coercive_degree_four {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : CompactSupportForm (deckRepresentation n) univ 4,
      c * compactNormSq n 4 a ≤
        compactNormSq n 5 (compactSymmetricExterior n 4 a) +
          compactNormSq n 3 (compactSymmetricContraction n 3 a) :=
  Exists.imp (fun c h => ⟨h.1, compactNormSq_bound_degree_four n c h.2⟩)
    (symmetric_energy_coercive_degree_four (n := n) hn)

/-- Hilbert-norm form of the degree-4 sum-coercivity bound. -/
theorem norm_symmetric_energy_coercive_degree_four {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Core n 4,
      c * ‖inclusion n 4 a‖ ^ 2 ≤
        ‖inclusion n 5 (compactSymmetricExterior n 4 a)‖ ^ 2 +
          ‖inclusion n 3 (compactSymmetricContraction n 3 a)‖ ^ 2 := by
  apply Exists.imp _ (integral_symmetric_energy_coercive_degree_four (n := n) hn)
  intro c hc
  refine ⟨hc.1, fun a => ?_⟩
  calc
    _ = c * compactNormSq n 4 a := congrArg (c * ·) (compactNormSq_eq_norm_sq n 4 a).symm
    _ ≤ _ := hc.2 a
    _ = _ := congrArg₂ (· + ·) (compactNormSq_eq_norm_sq n 5 (compactSymmetricExterior n 4 a))
                                (compactNormSq_eq_norm_sq n 3 (compactSymmetricContraction n 3 a))

/-- Dropping the nonnegative sum of the two Covariant pieces from the mixed-term-free energy
identity `compact_energy_identity_degree_four`. -/
theorem algebraic_energy_le_flat_degree_four (n : ℕ) (a : Core n 4) :
    ‖inclusion n 5 (compactSymmetricExterior n 4 a)‖ ^ 2 +
      ‖inclusion n 3 (compactSymmetricContraction n 3 a)‖ ^ 2 ≤
    ‖inclusion n 3 (compactAdjoint n 3 a)‖ ^ 2 +
      ‖inclusion n 5 (compactDifferential (deckRepresentation n) isOpen_univ 4 a)‖ ^ 2 := by
  have h := compact_energy_identity_degree_four n a
  linarith [sq_nonneg ‖inclusion n 5 (compactCovariantExterior n 4 a)‖,
    sq_nonneg ‖inclusion n 3 (compactCovariantAdjoint n 3 a)‖]

/-- Final degree-4 differential-energy coercivity, closing clause `k = 3` of Proposition C.1. -/
theorem norm_differential_energy_coercive_degree_four {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Core n 4,
      c * ‖inclusion n 4 a‖ ^ 2 ≤
        ‖inclusion n 3 (compactAdjoint n 3 a)‖ ^ 2 +
          ‖inclusion n 5 (compactDifferential (deckRepresentation n) isOpen_univ 4 a)‖ ^ 2 :=
  Exists.imp (fun _c h => ⟨h.1, fun a => (h.2 a).trans (algebraic_energy_le_flat_degree_four n a)⟩)
    (norm_symmetric_energy_coercive_degree_four (n := n) hn)

end TernaryPeriodPolynomials.Argument.Coercivity
