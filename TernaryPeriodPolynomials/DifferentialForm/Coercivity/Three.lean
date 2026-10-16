module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CoerciveTransportThree
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CancellationThree
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.QuotientCoercive

@[expose] public section



/-! Degree-3 quotient-integrated coercivity and final assembly, mirroring
`QuotientCoerciveFour.lean` + `CoercivityFour.lean` one degree down, but for the SUM of the two
Symmetric pieces (`compactSymmetricExterior n 3` and `compactSymmetricContraction n 2`) rather than
a single boundary piece. The integration chain combines `scalarPairing_symmetricExterior_self` and
`scalarPairing_symmetricContraction_self` via `integral_add`; the final assembly drops the
nonnegative sum of the two Covariant pieces from the already mixed-term-free energy identity
`compact_energy_identity_three` (`CancellationThree.lean`), closing clause `k = 2` of
Proposition C.1. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- Pointwise sum-bound descends to the scalar pairing, mirroring
`scalarPairing_symmetric_energy_bound_four` but combining both Symmetric pieces via
`scalarPairing_symmetricExterior_self`/`scalarPairing_symmetricContraction_self`. -/
theorem scalarPairing_symmetric_energy_bound_three (n : ℕ) (c : ℝ)
    (h : ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ w : FormValue n 3,
      c * formPairing n 3 x w w ≤
        formPairing n 4 x (symmetricExterior n 3 x w) (symmetricExterior n 3 x w) +
        formPairing n 2 x (symmetricContraction n 2 x w) (symmetricContraction n 2 x w))
    (a : CompactSupportForm (deckRepresentation n) univ 3) (q : OrbitSpace) :
    c * scalarPairing n 3 a.val a.val q ≤
      scalarPairing n 4 (compactSymmetricExterior n 3 a).val (compactSymmetricExterior n 3 a).val q +
      scalarPairing n 2 (compactSymmetricContraction n 2 a).val (compactSymmetricContraction n 2 a).val q :=
  (h _ (extract_mem (chosenLift q)) _).trans_eq
    (congrArg₂ (· + ·) (scalarPairing_symmetricExterior_self n 3 a q)
      (scalarPairing_symmetricContraction_self n 2 a q)).symm

/-- A proved pointwise sum-bound integrates for genuine compact forms, mirroring
`compactNormSq_bound_four` but splitting the integral of the sum via `integral_add`. -/
theorem compactNormSq_bound_three (n : ℕ) (c : ℝ)
    (h : ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ w : FormValue n 3,
      c * formPairing n 3 x w w ≤
        formPairing n 4 x (symmetricExterior n 3 x w) (symmetricExterior n 3 x w) +
        formPairing n 2 x (symmetricContraction n 2 x w) (symmetricContraction n 2 x w))
    (a : CompactSupportForm (deckRepresentation n) univ 3) :
    c * compactNormSq n 3 a ≤
      compactNormSq n 4 (compactSymmetricExterior n 3 a) + compactNormSq n 2 (compactSymmetricContraction n 2 a) := by
  have hmono := integral_mono_const_mul orbitVolume c
    (fun q => scalarPairing n 3 a.val a.val q)
    (fun q => scalarPairing n 4 (compactSymmetricExterior n 3 a).val (compactSymmetricExterior n 3 a).val q +
      scalarPairing n 2 (compactSymmetricContraction n 2 a).val (compactSymmetricContraction n 2 a).val q)
    (integrable_scalarPairing n 3 a a.val)
    ((integrable_scalarPairing n 4 (compactSymmetricExterior n 3 a) (compactSymmetricExterior n 3 a).val).add
      (integrable_scalarPairing n 2 (compactSymmetricContraction n 2 a) (compactSymmetricContraction n 2 a).val))
    (scalarPairing_symmetric_energy_bound_three n c h a)
  rwa [integral_add
    (integrable_scalarPairing n 4 (compactSymmetricExterior n 3 a) (compactSymmetricExterior n 3 a).val)
    (integrable_scalarPairing n 2 (compactSymmetricContraction n 2 a) (compactSymmetricContraction n 2 a).val)]
    at hmono

/-- Uniform sum-coercivity integrated against the actual quotient volume, mirroring
`integral_symmetric_energy_coercive_four`. -/
theorem integral_symmetric_energy_coercive_three {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : CompactSupportForm (deckRepresentation n) univ 3,
      c * compactNormSq n 3 a ≤
        compactNormSq n 4 (compactSymmetricExterior n 3 a) + compactNormSq n 2 (compactSymmetricContraction n 2 a) :=
  Exists.imp (fun c h => ⟨h.1, compactNormSq_bound_three n c h.2⟩)
    (symmetric_energy_coercive_three (n := n) hn)

/-- Hilbert-norm form of the degree-3 sum-coercivity bound, mirroring
`norm_symmetric_energy_coercive_four`. -/
theorem norm_symmetric_energy_coercive_three {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Core n 3,
      c * ‖inclusion n 3 a‖ ^ 2 ≤
        ‖inclusion n 4 (compactSymmetricExterior n 3 a)‖ ^ 2 +
          ‖inclusion n 2 (compactSymmetricContraction n 2 a)‖ ^ 2 := by
  apply Exists.imp _ (integral_symmetric_energy_coercive_three (n := n) hn)
  intro c hc
  refine ⟨hc.1, fun a => ?_⟩
  calc
    _ = c * compactNormSq n 3 a := congrArg (c * ·) (compactNormSq_eq_norm_sq n 3 a).symm
    _ ≤ _ := hc.2 a
    _ = _ := congrArg₂ (· + ·) (compactNormSq_eq_norm_sq n 4 (compactSymmetricExterior n 3 a))
                                (compactNormSq_eq_norm_sq n 2 (compactSymmetricContraction n 2 a))

/-- Dropping the nonnegative sum of the two Covariant pieces from the mixed-term-free energy
identity `compact_energy_identity_three`, mirroring `algebraic_energy_le_flat_of_mixedEnergyFour_zero`
one degree down (both Covariant squares, not just one, are dropped together). -/
theorem algebraic_energy_le_flat_three (n : ℕ) (a : Core n 3) :
    ‖inclusion n 4 (compactSymmetricExterior n 3 a)‖ ^ 2 +
      ‖inclusion n 2 (compactSymmetricContraction n 2 a)‖ ^ 2 ≤
    ‖inclusion n 2 (compactAdjoint n 2 a)‖ ^ 2 +
      ‖inclusion n 4 (compactDifferential (deckRepresentation n) isOpen_univ 3 a)‖ ^ 2 := by
  have h := compact_energy_identity_three n a
  linarith [sq_nonneg ‖inclusion n 4 (compactCovariantExterior n 3 a)‖,
    sq_nonneg ‖inclusion n 2 (compactCovariantAdjoint n 2 a)‖]

/-- Final degree-3 differential-energy coercivity, closing clause `k = 2` of Proposition C.1:
`c * ‖a‖² ≤ ‖compactAdjoint n 2 a‖² + ‖compactDifferential ... 3 a‖²`. -/
theorem norm_differential_energy_coercive_three {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Core n 3,
      c * ‖inclusion n 3 a‖ ^ 2 ≤
        ‖inclusion n 2 (compactAdjoint n 2 a)‖ ^ 2 +
          ‖inclusion n 4 (compactDifferential (deckRepresentation n) isOpen_univ 3 a)‖ ^ 2 :=
  Exists.imp (fun _c h => ⟨h.1, fun a => (h.2 a).trans (algebraic_energy_le_flat_three n a)⟩)
    (norm_symmetric_energy_coercive_three (n := n) hn)

end TernaryPeriodPolynomials.Argument.Coercivity
