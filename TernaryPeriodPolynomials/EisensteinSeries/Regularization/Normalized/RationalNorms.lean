module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.InducedVectors
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RationalAutomorphy

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalizedCuspVector_parabolic_rational_norm
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (rationalMatrix : RationalGL3)
    (parabolic : rationalMatrix ∈ GeneralEisenstein.parabolic .plane) (matrix : AdelicGL) :
    ‖(normalizedCuspVector induced parameter (rationalGroup rationalMatrix * matrix)).val‖ =
      ‖(normalizedCuspVector induced parameter matrix).val‖ := by
  obtain ⟨first, second, binary, scalar, factorization⟩ :=
    planeParabolic_factorization rationalMatrix parabolic
  rw [factorization, map_mul, mul_assoc]
  change ‖(normalizedCuspVector induced parameter
    (GeneralLinearGroup.map rationalAdele (planeUnipotent first second) *
      (GeneralLinearGroup.map rationalAdele (planeLevi binary scalar) * matrix))).val‖ = _
  rw [map_planeUnipotent, normalizedCuspVector_unipotent, map_planeLevi,
    planeLevi_rankOne_binary, mul_assoc, normalizedCuspVector_rankOne_norm,
    normalizedCuspVector_binary_norm, GeneralLinearGroup.map_det,
    adeleNorm_rational, adeleNorm_rational]
  simp

theorem normalizedCuspVector_norm_of_representative
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (representative : RationalGL3) (matrix : AdelicGL) :
    ‖(normalizedCuspVector induced parameter
      (rationalGroup (Quotient.out (QuotientGroup.mk representative : Flags .plane))⁻¹ * matrix)).val‖ =
      ‖(normalizedCuspVector induced parameter (rationalGroup representative⁻¹ * matrix)).val‖ := by
  obtain ⟨parabolic, equality⟩ :=
    QuotientGroup.mk_out_eq_mul (GeneralEisenstein.parabolic .plane) representative
  rw [equality, _root_.mul_inv_rev, map_mul, mul_assoc]
  exact normalizedCuspVector_parabolic_rational_norm induced parameter parabolic.val⁻¹
    ((GeneralEisenstein.parabolic .plane).inv_mem parabolic.property) _

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
