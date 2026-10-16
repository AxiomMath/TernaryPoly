module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.BasepointBridge
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.QuotientCoercive
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.IntegratedAlgebra

@[expose] public section



/-! Degree-1 specialization of the quotient-integrated coercivity bound, mirroring the original
authors' own genuine two-term degree-2 argument
(`TernaryPoly.PolynomialFormGeometricEnergy.scalarPairing_symmetric_energy_bound`/
`compactNormSq_bound`/`integral_symmetric_energy_coercive`/`norm_symmetric_energy_coercive`,
`TernaryPeriodPolynomials/DifferentialForm/GeometricEnergy/QuotientCoercive.lean` and
`TernaryPeriodPolynomials/DifferentialForm/GeometricEnergy/IntegratedAlgebra.lean`) one level down, using the basepoint-transported bound `symmetric_energy_coercive_one`
(`BasepointBridge.lean`) in place of the original authors' `symmetric_energy_coercive`. Unlike
the degree-0 one-term `QuotientCoercive.lean`, this mirrors the two-term
original directly, since degree 1 (like degree 2) keeps both the contraction and the exterior
cross term. All the generic machinery used here (`compactNormSq`, `integral_mono_add_const_mul`,
`integrable_scalarPairing`, `scalarPairing_symmetricContraction_self`,
`scalarPairing_symmetricExterior_self`, `compactNormSq_eq_norm_sq`) is already proved generically
in `k` by the original authors; only the degree-specific wrapper theorems are new. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.CoercivityOne

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- Pointwise bound descends to the scalar pairing, mirroring `scalarPairing_symmetric_energy_bound`
one level down. -/
theorem scalarPairing_symmetric_energy_bound_one (n : ℕ) (c : ℝ)
    (h : ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ a : FormValue n 1,
      c * formPairing n 1 x a a ≤
        formPairing n 0 x (symmetricContraction n 0 x a) (symmetricContraction n 0 x a) +
        formPairing n 2 x (symmetricExterior n 1 x a) (symmetricExterior n 1 x a))
    (a : CompactSupportForm (deckRepresentation n) univ 1) (q : OrbitSpace) :
    c * scalarPairing n 1 a.val a.val q ≤
      scalarPairing n 0 (compactSymmetricContraction n 0 a).val (compactSymmetricContraction n 0 a).val q +
      scalarPairing n 2 (compactSymmetricExterior n 1 a).val (compactSymmetricExterior n 1 a).val q :=
  (h _ (extract_mem (chosenLift q)) _).trans_eq
    (congrArg₂ (· + ·) (scalarPairing_symmetricContraction_self n 0 a q).symm
      (scalarPairing_symmetricExterior_self n 1 a q).symm)

/-- A proved pointwise bound integrates for genuine compact forms, mirroring `compactNormSq_bound`
one level down. -/
theorem compactNormSq_bound_one (n : ℕ) (c : ℝ)
    (h : ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ a : FormValue n 1,
      c * formPairing n 1 x a a ≤
        formPairing n 0 x (symmetricContraction n 0 x a) (symmetricContraction n 0 x a) +
        formPairing n 2 x (symmetricExterior n 1 x a) (symmetricExterior n 1 x a))
    (a : CompactSupportForm (deckRepresentation n) univ 1) :
    c * compactNormSq n 1 a ≤ compactNormSq n 0 (compactSymmetricContraction n 0 a) +
      compactNormSq n 2 (compactSymmetricExterior n 1 a) :=
  integral_mono_add_const_mul orbitVolume c _ _ _
    (integrable_scalarPairing n 1 a a.val)
    (integrable_scalarPairing n 0 (compactSymmetricContraction n 0 a) (compactSymmetricContraction n 0 a).val)
    (integrable_scalarPairing n 2 (compactSymmetricExterior n 1 a) (compactSymmetricExterior n 1 a).val)
    (scalarPairing_symmetric_energy_bound_one n c h a)

/-- Uniform coercivity integrated against the actual quotient volume, mirroring
`integral_symmetric_energy_coercive` one level down. -/
theorem integral_symmetric_energy_coercive_one {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : CompactSupportForm (deckRepresentation n) univ 1,
      c * compactNormSq n 1 a ≤ compactNormSq n 0 (compactSymmetricContraction n 0 a) +
        compactNormSq n 2 (compactSymmetricExterior n 1 a) := by
  exact Exists.imp (fun c h => ⟨h.1, compactNormSq_bound_one n c h.2⟩)
    (symmetric_energy_coercive_one (n := n) hn)

/-- Hilbert-norm form of the degree-1 coercivity bound, mirroring `norm_symmetric_energy_coercive`
one level down. -/
theorem norm_symmetric_energy_coercive_one {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Core n 1,
      c * ‖inclusion n 1 a‖ ^ 2 ≤
        ‖inclusion n 0 (compactSymmetricContraction n 0 a)‖ ^ 2 +
        ‖inclusion n 2 (compactSymmetricExterior n 1 a)‖ ^ 2 := by
  apply Exists.imp _ (integral_symmetric_energy_coercive_one (n := n) hn)
  intro c hc
  refine ⟨hc.1, fun a => ?_⟩
  calc
    _ = c * compactNormSq n 1 a := congrArg (c * ·) (compactNormSq_eq_norm_sq n 1 a).symm
    _ ≤ _ := hc.2 a
    _ = _ := congrArg₂ (· + ·)
      (compactNormSq_eq_norm_sq n 0 (compactSymmetricContraction n 0 a))
      (compactNormSq_eq_norm_sq n 2 (compactSymmetricExterior n 1 a))

end TernaryPeriodPolynomials.Argument.CoercivityOne
