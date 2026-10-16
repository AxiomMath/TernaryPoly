module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Representation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.Smooth
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {domain : Set P} {order : WithTop ℕ∞}

theorem binary_linearForm_coeff_contDiffOn
    (matrices : P → Matrix (Fin 2) (Fin 2) ℂ)
    (entries : ∀ row column, ContDiffOn ℝ order (fun point => matrices point row column) domain)
    (row : Fin 2) (monomial : Fin 2 →₀ ℕ) :
    ContDiffOn ℝ order (fun point => (Binary.linearForm (matrices point) row).coeff monomial) domain := by
  simp only [Binary.linearForm, coeff_sum, coeff_C_mul]
  exact ContDiffOn.sum (fun column _ => (entries row column).mul contDiffOn_const)

theorem binary_substitute_coeff_contDiffOn
    (matrices : P → Matrix (Fin 2) (Fin 2) ℂ)
    (entries : ∀ row column, ContDiffOn ℝ order (fun point => matrices point row column) domain)
    (polynomial : Binary.Poly) (monomial : Fin 2 →₀ ℕ) :
    ContDiffOn ℝ order (fun point => (Binary.substitute (matrices point) polynomial).coeff monomial) domain := by
  classical
  induction polynomial using MvPolynomial.induction_on generalizing monomial with
  | C scalar =>
    simpa only [Binary.substitute, bind₁_C_right] using
      (contDiffOn_const : ContDiffOn ℝ order (fun _ : P => (C scalar).coeff monomial) domain)
  | add first second first_smooth second_smooth =>
    simpa only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using (first_smooth monomial).add (second_smooth monomial)
  | mul_X polynomial generator smooth =>
    simp only [map_mul, Binary.substitute_X, coeff_mul]
    exact ContDiffOn.sum (fun indices _ =>
      (smooth indices.1).mul (binary_linearForm_coeff_contDiffOn matrices entries generator indices.2))

theorem binary_homogeneousAction_functional_contDiffOn {degree : ℕ}
    (matrices : P → Binary.GL2)
    (determinant : ContDiffOn ℝ order
      (fun point => ((Matrix.GeneralLinearGroup.det (matrices point)).val)⁻¹) domain)
    (inverse_entries : ∀ row column, ContDiffOn ℝ order
      (fun point => (matrices point)⁻¹.val row column) domain)
    (polynomial : Binary.HomogeneousPoly (degree + 1))
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    ContDiffOn ℝ order
      (fun point => functional (Binary.homogeneousAction (degree + 1) (-1) (matrices point) polynomial))
      domain := by
  have spanned := binaryPolynomialDual_mem_span_coefficients functional
  induction spanned using Submodule.span_induction with
  | mem functional membership =>
    rcases membership with ⟨monomial, rfl⟩
    change ContDiffOn ℝ order
      (fun point => (Binary.homogeneousAction (degree + 1) (-1) (matrices point) polynomial).val.coeff monomial) domain
    simp only [Binary.homogeneousAction_coe, Binary.action_apply, coeff_smul,
      Binary.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk, zpow_neg_one, smul_eq_mul]
    exact determinant.mul (binary_substitute_coeff_contDiffOn
      (fun point => (matrices point)⁻¹.val) inverse_entries polynomial.val monomial)
  | zero => exact contDiffOn_const
  | add first second _ _ first_smooth second_smooth =>
    exact first_smooth.add second_smooth
  | smul scalar functional _ smooth =>
    exact smooth.const_smul scalar

theorem binary_matrix_det_contDiffOn
    (matrices : P → Matrix (Fin 2) (Fin 2) ℝ)
    (entries : ∀ row column, ContDiffOn ℝ order (fun point => matrices point row column) domain) :
    ContDiffOn ℝ order (fun point => (matrices point).det) domain := by
  simpa only [Matrix.det_fin_two] using
    ((entries 0 0).mul (entries 1 1)).sub ((entries 0 1).mul (entries 1 0))

theorem binary_matrix_inv_contDiffOn
    (matrices : P → Matrix (Fin 2) (Fin 2) ℝ)
    (entries : ∀ row column, ContDiffOn ℝ order (fun point => matrices point row column) domain)
    (invertible : ∀ point ∈ domain, (matrices point).det ≠ 0)
    (row column : Fin 2) :
    ContDiffOn ℝ order (fun point => (matrices point)⁻¹ row column) domain := by
  have determinant := (binary_matrix_det_contDiffOn matrices entries).inv invertible
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_fin_two]
  fin_cases row <;> fin_cases column
  · exact determinant.mul (entries 1 1)
  · exact determinant.mul (entries 0 1).neg
  · exact determinant.mul (entries 1 0).neg
  · exact determinant.mul (entries 0 0)

theorem binaryCoefficient_functional_contDiffOn {degree : ℕ}
    (matrices : P → Matrix (Fin 2) (Fin 2) ℝ)
    (entries : ∀ row column, ContDiffOn ℝ order (fun point => matrices point row column) domain)
    (invertible : ∀ point ∈ domain, (matrices point).det ≠ 0)
    (polynomial : Binary.HomogeneousPoly (degree + 1))
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    ContDiffOn ℝ order
      (fun point => functional (binaryCoefficient degree (invertibleMatrix (matrices point)) polynomial))
      domain := by
  apply binary_homogeneousAction_functional_contDiffOn
  · have regular := Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((binary_matrix_det_contDiffOn matrices entries).inv invertible)
    apply regular.congr
    intro point member
    simp only [Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.val_map_apply,
      invertibleMatrix_val _ (invertible point member), Complex.coe_algebraMap,
      Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_inv, Pi.inv_apply]
    exact congrArg Inv.inv (Complex.ofRealHom.map_det (matrices point)).symm
  · intro row column
    have regular := Complex.ofRealCLM.contDiff.comp_contDiffOn
      (binary_matrix_inv_contDiffOn matrices entries invertible row column)
    apply regular.congr
    intro point member
    rw [← map_inv, Matrix.GeneralLinearGroup.val_map_apply,
      Matrix.GeneralLinearGroup.coe_inv, invertibleMatrix_val _ (invertible point member)]
    rfl

theorem binary_normalizingFactor_contDiffOn
    (matrices : P → Matrix (Fin 2) (Fin 2) ℝ)
    (entries : ∀ row column, ContDiffOn ℝ order (fun point => matrices point row column) domain)
    (invertible : ∀ point ∈ domain, (matrices point).det ≠ 0) (exponent : ℂ) :
    ContDiffOn ℝ order
      (fun point => normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix (matrices point))))
        exponent) domain := by
  have logarithm := (binary_matrix_det_contDiffOn matrices entries).log invertible
  have regular := ((contDiffOn_const (c := exponent)).mul
    (Complex.ofRealCLM.contDiff.comp_contDiffOn logarithm)).cexp
  apply regular.congr
  intro point member
  rw [binary_normalizingFactor_eq, invertibleMatrix_val _ (invertible point member)]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
