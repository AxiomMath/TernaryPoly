module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.QuotientCoercive
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Basic

@[expose] public section


/-! Actual quotient integrals of the symmetric-connection algebraic energy. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix PolynomialCoefficientBundle PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection PolynomialFormCoordinates
open PolynomialFormHilbert SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
open SmoothCoveringDeRham SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian

theorem inner_symmetricExterior_one (n : ℕ) (a : Core n 1) (b : Core n 2) :
    inner ℝ (inclusion n 2 (compactSymmetricExterior n 1 a)) (inclusion n 2 b) =
      inner ℝ (inclusion n 1 a) (inclusion n 1 (compactSymmetricContraction n 1 b)) := by
  exact (inner_inclusion n 2 (compactSymmetricExterior n 1 a) b).trans
    ((integral_congr_ae (Filter.Eventually.of_forall (scalarPairing_symmetricExterior_one n a b))).trans
      (inner_inclusion n 1 a (compactSymmetricContraction n 1 b)).symm)

theorem inner_symmetricExterior_two (n : ℕ) (a : Core n 2) (b : Core n 3) :
    inner ℝ (inclusion n 3 (compactSymmetricExterior n 2 a)) (inclusion n 3 b) =
      inner ℝ (inclusion n 2 a) (inclusion n 2 (compactSymmetricContraction n 2 b)) := by
  exact (inner_inclusion n 3 (compactSymmetricExterior n 2 a) b).trans
    ((integral_congr_ae (Filter.Eventually.of_forall (scalarPairing_symmetricExterior_two n a b))).trans
      (inner_inclusion n 2 a (compactSymmetricContraction n 2 b)).symm)

theorem compactNormSq_eq_norm_sq (n k : ℕ) (a : Core n k) :
    compactNormSq n k a = ‖inclusion n k a‖ ^ 2 :=
  (inner_inclusion n k a a).symm.trans (real_inner_self_eq_norm_sq _)

/-- Actual Hilbert norms of both zero-order terms control the genuine L² norm of compact forms. -/
theorem norm_symmetric_energy_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Core n 2,
      c * ‖inclusion n 2 a‖ ^ 2 ≤
        ‖inclusion n 1 (compactSymmetricContraction n 1 a)‖ ^ 2 +
        ‖inclusion n 3 (compactSymmetricExterior n 2 a)‖ ^ 2 := by
  apply Exists.imp _ (integral_symmetric_energy_coercive (n := n) hn)
  intro c hc
  refine ⟨hc.1,fun a => ?_⟩
  calc
    _ = c * compactNormSq n 2 a := congrArg (c * ·) (compactNormSq_eq_norm_sq n 2 a).symm
    _ ≤ _ := hc.2 a
    _ = _ := congrArg₂ (· + ·)
      (compactNormSq_eq_norm_sq n 1 (compactSymmetricContraction n 1 a))
      (compactNormSq_eq_norm_sq n 3 (compactSymmetricExterior n 2 a))

end TernaryPoly.PolynomialFormGeometricEnergy
