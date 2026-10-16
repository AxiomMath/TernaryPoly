module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Lie.Cocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryCoefficientRegularity

theorem determinant_contDiff : ContDiff ℝ ⊤ (fun matrix : BinaryMatrix => matrix.det) := by
  have coordinate (row column : Fin 2) : ContDiff ℝ ⊤ (fun matrix : BinaryMatrix => matrix row column) :=
    contDiff_apply_apply ℝ ℝ row column
  simpa only [Matrix.det_fin_two] using
    ((coordinate 0 0).mul (coordinate 1 1)).sub ((coordinate 0 1).mul (coordinate 1 0))

theorem inverse_entry_contDiffAt (point : BinaryMatrix) (invertibility : point.det ≠ 0) (row column : Fin 2) :
    ContDiffAt ℝ ⊤ (fun matrix : BinaryMatrix => (invertibleMatrix matrix)⁻¹.val row column) point := by
  have inverseDeterminant : ContDiffAt ℝ ⊤ (fun matrix : BinaryMatrix => matrix.det⁻¹) point :=
    determinant_contDiff.contDiffAt.inv invertibility
  have adjugateEntry : ContDiff ℝ ⊤ (fun matrix : BinaryMatrix => matrix.adjugate row column) := by
    rw [show (fun matrix : BinaryMatrix => matrix.adjugate row column) =
      (fun matrix => !![matrix 1 1, -matrix 0 1; -matrix 1 0, matrix 0 0] row column) by
      funext matrix; rw [Matrix.adjugate_fin_two]]
    fin_cases row <;> fin_cases column
    · exact contDiff_apply_apply ℝ ℝ 1 1
    · exact (contDiff_apply_apply ℝ ℝ 0 1).neg
    · exact (contDiff_apply_apply ℝ ℝ 1 0).neg
    · exact contDiff_apply_apply ℝ ℝ 0 0
  apply (inverseDeterminant.mul adjugateEntry.contDiffAt).congr_of_eventuallyEq
  filter_upwards [binaryDomain_isOpen.mem_nhds invertibility] with matrix matrixInvertibility
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, Ring.inverse_eq_inv,
    invertibleMatrix_val matrix matrixInvertibility]
  rfl

theorem determinant_of_invertibleMatrix_contDiffAt (point : BinaryMatrix) (invertibility : point.det ≠ 0) :
    ContDiffAt ℝ ⊤ (fun matrix : BinaryMatrix => (invertibleMatrix matrix).val.det) point := by
  apply determinant_contDiff.contDiffAt.congr_of_eventuallyEq
  filter_upwards [binaryDomain_isOpen.mem_nhds invertibility] with matrix matrixInvertibility
  rw [invertibleMatrix_val matrix matrixInvertibility]

theorem normPower_contDiffAt (exponent : ℂ) (point : BinaryMatrix) (invertibility : point.det ≠ 0) :
    ContDiffAt ℝ ⊤ (fun matrix : BinaryMatrix =>
      normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix matrix))) exponent) point := by
  have logarithm : ContDiffAt ℝ ⊤ (fun matrix : BinaryMatrix => Real.log matrix.det) point :=
    determinant_contDiff.contDiffAt.log invertibility
  have complexLogarithm : ContDiffAt ℝ ⊤ (fun matrix : BinaryMatrix => (Real.log matrix.det : ℂ)) point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point logarithm
  have model : ContDiffAt ℝ ⊤ (fun matrix : BinaryMatrix => Complex.exp (exponent * (Real.log matrix.det : ℂ))) point :=
    (contDiffAt_const.mul complexLogarithm).cexp
  apply model.congr_of_eventuallyEq
  filter_upwards [binaryDomain_isOpen.mem_nhds invertibility] with matrix matrixInvertibility
  rw [normPower, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_atInfinity, invertibleMatrix_val matrix matrixInvertibility,
    Real.log_abs]

section Coefficients

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℝ Source]

theorem coefficient_mul (first second : Source → Binary.Poly) (point : Source)
    (firstRegular : ∀ monomial, ContDiffAt ℝ ⊤ (fun parameter => (first parameter).coeff monomial) point)
    (secondRegular : ∀ monomial, ContDiffAt ℝ ⊤ (fun parameter => (second parameter).coeff monomial) point)
    (monomial : Fin 2 →₀ ℕ) :
    ContDiffAt ℝ ⊤ (fun parameter => (first parameter * second parameter).coeff monomial) point := by
  simp only [MvPolynomial.coeff_mul]
  apply ContDiffAt.sum
  intro pair _
  exact (firstRegular pair.1).mul (secondRegular pair.2)

theorem linearForm_coefficient (family : Source → Matrix (Fin 2) (Fin 2) ℂ) (point : Source)
    (regularity : ∀ row column, ContDiffAt ℝ ⊤ (fun parameter => family parameter row column) point)
    (position : Fin 2) (monomial : Fin 2 →₀ ℕ) :
    ContDiffAt ℝ ⊤ (fun parameter => (Binary.linearForm (family parameter) position).coeff monomial) point := by
  simp only [Binary.linearForm, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  apply ContDiffAt.sum
  intro other _
  exact (regularity position other).mul contDiffAt_const

theorem substitute_coefficient (family : Source → Matrix (Fin 2) (Fin 2) ℂ) (point : Source)
    (regularity : ∀ row column, ContDiffAt ℝ ⊤ (fun parameter => family parameter row column) point)
    (polynomial : Binary.Poly) (monomial : Fin 2 →₀ ℕ) :
    ContDiffAt ℝ ⊤ (fun parameter => (Binary.substitute (family parameter) polynomial).coeff monomial) point := by
  induction polynomial using MvPolynomial.induction_on generalizing monomial with
  | C scalar =>
      simpa only [Binary.substitute, MvPolynomial.bind₁_C_right] using
        (contDiffAt_const : ContDiffAt ℝ ⊤ (fun _ : Source => (MvPolynomial.C scalar).coeff monomial) point)
  | add first second firstInduction secondInduction =>
      simpa only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using (firstInduction monomial).add (secondInduction monomial)
  | mul_X polynomial position inductionHypothesis =>
      simpa only [map_mul, Binary.substitute_X] using
        coefficient_mul (fun parameter => Binary.substitute (family parameter) polynomial)
          (fun parameter => Binary.linearForm (family parameter) position) point inductionHypothesis
          (linearForm_coefficient family point regularity position) monomial

end Coefficients

theorem binaryCoefficient_coefficient_contDiffAt (degree : ℕ) (polynomial : Binary.HomogeneousPoly (degree + 1))
    (monomial : Fin 2 →₀ ℕ) (point : BinaryMatrix) (invertibility : point.det ≠ 0) :
    ContDiffAt ℝ ⊤ (fun matrix : BinaryMatrix =>
      (binaryCoefficient degree (invertibleMatrix matrix) polynomial).val.coeff monomial) point := by
  have determinantRegular : ContDiffAt ℝ ⊤
      (fun matrix : BinaryMatrix => ((invertibleMatrix matrix).val.det : ℂ)) point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point (determinant_of_invertibleMatrix_contDiffAt point invertibility)
  have determinantNonzero : ((invertibleMatrix point).val.det : ℂ) ≠ 0 := by
    exact_mod_cast Matrix.GeneralLinearGroup.det_ne_zero (invertibleMatrix point)
  have inverseEntries (row column : Fin 2) : ContDiffAt ℝ ⊤
      (fun matrix : BinaryMatrix => ((invertibleMatrix matrix)⁻¹.val row column : ℂ)) point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point (inverse_entry_contDiffAt point invertibility row column)
  have substitution := substitute_coefficient
    (fun matrix : BinaryMatrix => fun row column => ((invertibleMatrix matrix)⁻¹.val row column : ℂ))
    point inverseEntries polynomial.val monomial
  have model : ContDiffAt ℝ ⊤ (fun matrix : BinaryMatrix => ((invertibleMatrix matrix).val.det : ℂ)⁻¹ *
      (Binary.substitute
        (fun row column => ((invertibleMatrix matrix)⁻¹.val row column : ℂ)) polynomial.val).coeff monomial) point :=
    (determinantRegular.inv determinantNonzero).mul substitution
  have functionEquality : (fun matrix : BinaryMatrix =>
      (binaryCoefficient degree (invertibleMatrix matrix) polynomial).val.coeff monomial) =
      (fun matrix : BinaryMatrix => ((invertibleMatrix matrix).val.det : ℂ)⁻¹ *
        (Binary.substitute
          (fun row column => ((invertibleMatrix matrix)⁻¹.val row column : ℂ)) polynomial.val).coeff monomial) := by
    funext matrix
    simp only [binaryCoefficient]
    rw [Binary.homogeneousAction_coe, Binary.action_apply, MvPolynomial.coeff_smul]
    change Binary.determinantCharacter (-1)
        (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (invertibleMatrix matrix)) * _ = _
    congr 1
    · change ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)
          (invertibleMatrix matrix))).val ^ (-1 : ℤ)) = _
      have determinantMap : (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)
          (invertibleMatrix matrix))).val = ((invertibleMatrix matrix).val.det : ℂ) :=
        (RingHom.map_det (algebraMap ℝ ℂ) (invertibleMatrix matrix).val).symm
      rw [determinantMap, zpow_neg_one]
  rw [functionEquality]
  exact model

theorem multiplier_contDiffAt (degree : ℕ) (index other : Index (degree + 1))
    (point : BinaryMatrix) (invertibility : point.det ≠ 0) :
    ContDiffAt ℝ ⊤ (fun matrix : BinaryMatrix =>
      normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix matrix))) (((degree : ℂ) + 3) / 2) *
        (binaryCoefficient degree (invertibleMatrix matrix) (basisMonomial other)).val.coeff index.val) point :=
  (normPower_contDiffAt _ point invertibility).mul
    (binaryCoefficient_coefficient_contDiffAt degree (basisMonomial other) index.val point invertibility)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryCoefficientRegularity
