module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CoerciveTransportFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.QuotientCoercive

@[expose] public section



/-! Degree-4 specialization of the quotient-integrated coercivity bound, mirroring
`QuotientCoercive.lean`'s degree-0 chain `scalarPairing_symmetric_energy_bound_zero`/
`compactNormSq_bound_zero`/`integral_symmetric_energy_coercive_zero`/
`norm_symmetric_energy_coercive_zero`, substituting the degree-4 contraction bound
`symmetric_energy_coercive_four` and the descent lemma `scalarPairing_symmetricContraction_self`
for the degree-0 exterior-derivative versions. Reuses `integral_mono_const_mul`, already proved
generically (over any measure space) in `QuotientCoercive.lean`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- Pointwise bound descends to the scalar pairing, mirroring
`scalarPairing_symmetric_energy_bound_zero`. -/
theorem scalarPairing_symmetric_energy_bound_four (n : ℕ) (c : ℝ)
    (h : ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ w : FormValue n 5,
      c * formPairing n 5 x w w ≤ formPairing n 4 x (symmetricContraction n 4 x w) (symmetricContraction n 4 x w))
    (a : CompactSupportForm (deckRepresentation n) univ 5) (q : OrbitSpace) :
    c * scalarPairing n 5 a.val a.val q ≤
      scalarPairing n 4 (compactSymmetricContraction n 4 a).val (compactSymmetricContraction n 4 a).val q :=
  (h _ (extract_mem (chosenLift q)) _).trans_eq (scalarPairing_symmetricContraction_self n 4 a q).symm

/-- A proved pointwise bound integrates for genuine compact forms, mirroring
`compactNormSq_bound_zero`. -/
theorem compactNormSq_bound_four (n : ℕ) (c : ℝ)
    (h : ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ w : FormValue n 5,
      c * formPairing n 5 x w w ≤ formPairing n 4 x (symmetricContraction n 4 x w) (symmetricContraction n 4 x w))
    (a : CompactSupportForm (deckRepresentation n) univ 5) :
    c * compactNormSq n 5 a ≤ compactNormSq n 4 (compactSymmetricContraction n 4 a) :=
  integral_mono_const_mul orbitVolume c _ _
    (integrable_scalarPairing n 5 a a.val)
    (integrable_scalarPairing n 4 (compactSymmetricContraction n 4 a) (compactSymmetricContraction n 4 a).val)
    (scalarPairing_symmetric_energy_bound_four n c h a)

/-- Uniform coercivity integrated against the actual quotient volume, mirroring
`integral_symmetric_energy_coercive_zero`. -/
theorem integral_symmetric_energy_coercive_four {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : CompactSupportForm (deckRepresentation n) univ 5,
      c * compactNormSq n 5 a ≤ compactNormSq n 4 (compactSymmetricContraction n 4 a) := by
  exact Exists.imp (fun c h => ⟨h.1, compactNormSq_bound_four n c h.2⟩)
    (symmetric_energy_coercive_four (n := n) hn)

/-- Hilbert-norm form of the degree-4 coercivity bound, mirroring
`norm_symmetric_energy_coercive_zero`. -/
theorem norm_symmetric_energy_coercive_four {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Core n 5,
      c * ‖inclusion n 5 a‖ ^ 2 ≤ ‖inclusion n 4 (compactSymmetricContraction n 4 a)‖ ^ 2 := by
  apply Exists.imp _ (integral_symmetric_energy_coercive_four (n := n) hn)
  intro c hc
  refine ⟨hc.1, fun a => ?_⟩
  calc
    _ = c * compactNormSq n 5 a := congrArg (c * ·) (compactNormSq_eq_norm_sq n 5 a).symm
    _ ≤ _ := hc.2 a
    _ = _ := compactNormSq_eq_norm_sq n 4 (compactSymmetricContraction n 4 a)

end TernaryPeriodPolynomials.Argument.Coercivity
