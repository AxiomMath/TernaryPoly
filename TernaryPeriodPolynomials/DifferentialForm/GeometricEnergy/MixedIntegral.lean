module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.MixedOperator

@[expose] public section


/-! The actual mixed energy is one half of the genuine descended current-divergence integral. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormCoordinates PolynomialFormHilbert
open SymmetricSpaceRiemannian SmoothCoveringDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian

theorem mixedEnergy_eq_inner_compactMixedOperator (n : ℕ) (a : Core n 2) :
    mixedEnergy n a = inner ℝ (inclusion n 2 a) (inclusion n 2 (compactMixedOperator n a)) := by
  have h1 : inner ℝ (inclusion n 3 (compactCovariantExterior n 2 a))
      (inclusion n 3 (compactSymmetricExterior n 2 a)) =
      inner ℝ (inclusion n 2 a) (inclusion n 2 (compactSymmetricContraction n 2 (compactCovariantExterior n 2 a))) :=
    (real_inner_comm _ _).trans (inner_symmetricExterior_two n a (compactCovariantExterior n 2 a))
  have h2 : inner ℝ (inclusion n 1 (compactCovariantAdjoint n 1 a))
      (inclusion n 1 (compactSymmetricContraction n 1 a)) =
      inner ℝ (inclusion n 2 a) (inclusion n 2 (compactCovariantExterior n 1 (compactSymmetricContraction n 1 a))) :=
    (real_inner_comm _ _).trans ((inner_covariantExterior_one n (compactSymmetricContraction n 1 a) a).symm.trans
      (real_inner_comm _ _))
  exact (congrArg₂ (· + ·) h1 h2).trans ((inner_add_right _ _ _).symm.trans
    (congrArg (inner ℝ (inclusion n 2 a)) ((inclusion n 2).map_add _ _).symm))

theorem mixedEnergy_eq_integral (n : ℕ) (a : Core n 2) :
    mixedEnergy n a = ∫ q, scalarPairing n 2 a.val (compactMixedOperator n a).val q ∂orbitVolume :=
  (mixedEnergy_eq_inner_compactMixedOperator n a).trans (inner_inclusion n 2 a (compactMixedOperator n a))

theorem integral_compactCurrentDivergence_eq (n : ℕ) (a : Core n 2) :
    (∫ q, compactCurrentDivergence n a q ∂orbitVolume) = 2 * mixedEnergy n a := by
  exact (integral_const_mul 2 _).trans (congrArg (2 * ·) (mixedEnergy_eq_integral n a).symm)

theorem mixedEnergy_eq_zero_of_integral_current_zero (n : ℕ) (a : Core n 2)
    (h : (∫ q, compactCurrentDivergence n a q ∂orbitVolume) = 0) : mixedEnergy n a = 0 := by
  have hz := (integral_compactCurrentDivergence_eq n a).symm.trans h
  linarith

end TernaryPoly.PolynomialFormGeometricEnergy
