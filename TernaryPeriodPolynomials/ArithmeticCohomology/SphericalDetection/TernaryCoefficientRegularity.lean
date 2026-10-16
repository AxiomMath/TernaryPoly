module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CoefficientRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LeviPolynomialSubstitution
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.CoefficientDerivatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.LeviLattice

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {domain : Set P} {order : WithTop ℕ∞}

theorem ternary_linearForm_coeff_contDiffOn
    (matrices : P → Matrix (Fin 3) (Fin 3) ℂ)
    (entries : ∀ row column, ContDiffOn ℝ order (fun point => matrices point row column) domain)
    (row : Fin 3) (monomial : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ order (fun point => (linearForm (matrices point) row).coeff monomial) domain := by
  simp only [linearForm, coeff_sum, coeff_C_mul]
  exact ContDiffOn.sum (fun column _ => (entries row column).mul contDiffOn_const)

theorem ternary_substitute_coeff_contDiffOn
    (matrices : P → Matrix (Fin 3) (Fin 3) ℂ)
    (entries : ∀ row column, ContDiffOn ℝ order (fun point => matrices point row column) domain)
    (polynomial : Poly) (monomial : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ order (fun point => (substitute (matrices point) polynomial).coeff monomial) domain := by
  classical
  induction polynomial using MvPolynomial.induction_on generalizing monomial with
  | C scalar =>
    simpa only [substitute, bind₁_C_right] using
      (contDiffOn_const : ContDiffOn ℝ order (fun _ : P => (C scalar).coeff monomial) domain)
  | add first second first_smooth second_smooth =>
    simpa only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using (first_smooth monomial).add (second_smooth monomial)
  | mul_X polynomial generator smooth =>
    simp only [map_mul, substitute_X, coeff_mul]
    exact ContDiffOn.sum (fun indices _ =>
      (smooth indices.1).mul (ternary_linearForm_coeff_contDiffOn matrices entries generator indices.2))

theorem ternary_homogeneousAction_functional_contDiffOn {degree : ℕ}
    (matrices : P → GL3)
    (determinant : ContDiffOn ℝ order (fun point => ((GeneralLinearGroup.det (matrices point)).val)⁻¹) domain)
    (inverse_entries : ∀ row column, ContDiffOn ℝ order (fun point => (matrices point)⁻¹.val row column) domain)
    (polynomial : HomogeneousPoly degree) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    ContDiffOn ℝ order (fun point => functional (homogeneousAction degree (-1) (matrices point) polynomial)) domain := by
  have spanned := ternaryPolynomialDual_mem_span_coefficients functional
  induction spanned using Submodule.span_induction with
  | mem functional membership =>
    rcases membership with ⟨monomial, rfl⟩
    change ContDiffOn ℝ order (fun point => (homogeneousAction degree (-1) (matrices point) polynomial).val.coeff monomial) domain
    simp only [homogeneousAction_coe, action_apply, coeff_smul, determinantCharacter,
      MonoidHom.coe_mk, OneHom.coe_mk, zpow_neg_one, smul_eq_mul]
    exact determinant.mul (ternary_substitute_coeff_contDiffOn
      (fun point => (matrices point)⁻¹.val) inverse_entries polynomial.val monomial)
  | zero => exact contDiffOn_const
  | add first second _ _ first_smooth second_smooth => exact first_smooth.add second_smooth
  | smul scalar functional _ smooth => exact smooth.const_smul scalar

theorem planeLevi_homogeneousAction_functional_contDiffOn {degree : ℕ}
    (matrices : P → Binary.GL2)
    (determinant : ContDiffOn ℝ order (fun point => ((GeneralLinearGroup.det (matrices point)).val)⁻¹) domain)
    (inverse_entries : ∀ row column, ContDiffOn ℝ order (fun point => (matrices point)⁻¹.val row column) domain)
    (polynomial : HomogeneousPoly degree) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    ContDiffOn ℝ order (fun point => functional (homogeneousAction degree (-1) (planeLevi (matrices point) 1) polynomial)) domain := by
  apply ternary_homogeneousAction_functional_contDiffOn
  · simpa only [planeLevi_det, Units.val_mul, Units.val_one, mul_one] using determinant
  · intro row column
    simp only [planeLevi_inverse, inv_one, planeLevi_value]
    fin_cases row <;> fin_cases column <;>
      first | exact contDiffOn_const | exact inverse_entries 0 0 | exact inverse_entries 0 1 |
        exact inverse_entries 1 0 | exact inverse_entries 1 1

theorem realPlaneLeviCoefficient_functional_contDiffOn {degree : ℕ}
    (matrices : P → Matrix (Fin 2) (Fin 2) ℝ)
    (entries : ∀ row column, ContDiffOn ℝ order (fun point => matrices point row column) domain)
    (invertible : ∀ point ∈ domain, (matrices point).det ≠ 0)
    (polynomial : HomogeneousPoly degree) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    ContDiffOn ℝ order (fun point => functional
      (realCoefficientComponent degree trivialCharacter (planeLevi (invertibleMatrix (matrices point)) 1) polynomial)) domain := by
  simp only [realCoefficientComponent_trivial, map_planeLevi_one]
  apply planeLevi_homogeneousAction_functional_contDiffOn
  · have regular := Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((binary_matrix_det_contDiffOn matrices entries).inv invertible)
    apply regular.congr
    intro point member
    simp only [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_map_apply,
      invertibleMatrix_val _ (invertible point member), Complex.coe_algebraMap,
      Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_inv, Pi.inv_apply]
    exact congrArg Inv.inv (Complex.ofRealHom.map_det (matrices point)).symm
  · intro row column
    have regular := Complex.ofRealCLM.contDiff.comp_contDiffOn
      (binary_matrix_inv_contDiffOn matrices entries invertible row column)
    apply regular.congr
    intro point member
    rw [← map_inv, GeneralLinearGroup.val_map_apply, GeneralLinearGroup.coe_inv,
      invertibleMatrix_val _ (invertible point member)]
    rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
