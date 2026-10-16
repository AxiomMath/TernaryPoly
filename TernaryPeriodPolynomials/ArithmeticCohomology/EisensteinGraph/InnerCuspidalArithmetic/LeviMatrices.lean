module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Binary.Mixed

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem map_lineLevi {R S : Type} [CommRing R] [CommRing S]
    (homomorphism : R →+* S) (scalar : Rˣ) (binary : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.map homomorphism (lineLevi scalar binary) =
      lineLevi (Units.map homomorphism.toMonoidHom scalar)
        (GeneralLinearGroup.map homomorphism binary) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map_apply, lineLevi_val]

theorem lineLevi_inverse {R : Type} [CommRing R]
    (scalar : Rˣ) (binary : GeneralLinearGroup (Fin 2) R) :
    (lineLevi scalar binary)⁻¹ = lineLevi scalar⁻¹ binary⁻¹ := by
  change ((lineLeviHom R) (scalar, binary))⁻¹ = (lineLeviHom R) (scalar⁻¹, binary⁻¹)
  rw [← map_inv]
  rfl

theorem lineLevi_determinant {R : Type} [CommRing R]
    (scalar : Rˣ) (binary : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.det (lineLevi scalar binary) = scalar * GeneralLinearGroup.det binary := by
  apply Units.ext
  simp only [Units.val_mul, GeneralLinearGroup.val_det_apply, lineLevi_val,
    Matrix.det_fin_three, Matrix.det_fin_two]
  simp
  ring

theorem substitute_lineLevi_binary (scalar : ℂˣ) (binary : Binary.GL2)
    (polynomial : Binary.Poly) :
    substitute (lineLevi scalar binary).val (binaryPolynomialEmbedding polynomial) =
      binaryPolynomialEmbedding (Binary.substitute binary.val polynomial) := by
  change bind₁ _ ((MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)) polynomial) = _
  rw [bind₁_rename]
  have forms : linearForm (lineLevi scalar binary).val ∘ (Fin.succ : Fin 2 → Fin 3) =
      fun index => binaryPolynomialEmbedding (Binary.linearForm binary.val index) := by
    funext index
    fin_cases index <;>
      simp [linearForm, Binary.linearForm, lineLevi_val, binaryPolynomialEmbedding,
        Fin.sum_univ_three, Fin.sum_univ_two]
  rw [forms]
  have substitution :
      bind₁ (fun index => binaryPolynomialEmbedding (Binary.linearForm binary.val index)) =
        binaryPolynomialEmbedding.comp (Binary.substitute binary.val) := by
    ext index
    simp [Binary.substitute, binaryPolynomialEmbedding]
  rw [substitution]
  rfl

theorem action_lineLevi_binary (scalar : ℂˣ) (binary : Binary.GL2)
    (polynomial : Binary.Poly) :
    action (-1) (lineLevi scalar binary) (binaryPolynomialEmbedding polynomial) =
      ((scalar.val * (GeneralLinearGroup.det binary).val)⁻¹ : ℂ) •
        binaryPolynomialEmbedding (Binary.substitute binary.inv polynomial) := by
  rw [action_apply, lineLevi_inverse, substitute_lineLevi_binary]
  have determinant : determinantCharacter (-1) (lineLevi scalar binary) =
      (scalar.val * (GeneralLinearGroup.det binary).val)⁻¹ := by
    change (GeneralLinearGroup.det (lineLevi scalar binary)).val ^ (-1 : ℤ) = _
    rw [lineLevi_determinant]
    simp only [Units.val_mul, zpow_neg_one]
  rw [determinant]
  rfl

theorem lineLevi_unipotent_conjugation {R : Type} [CommRing R]
    (scalar : Rˣ) (binary : GeneralLinearGroup (Fin 2) R) (first second : R) :
    lineLevi scalar binary * lineUnipotent first second * (lineLevi scalar binary)⁻¹ =
      lineUnipotent
        (scalar.val * (first * binary.inv 0 0 + second * binary.inv 1 0))
        (scalar.val * (first * binary.inv 0 1 + second * binary.inv 1 1)) := by
  apply Units.ext
  ext row column
  have firstIdentity := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) R => matrix 0 0)
    binary.val_inv
  have secondIdentity := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) R => matrix 0 1)
    binary.val_inv
  have thirdIdentity := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) R => matrix 1 0)
    binary.val_inv
  have fourthIdentity := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) R => matrix 1 1)
    binary.val_inv
  simp [Matrix.mul_apply, Fin.sum_univ_two] at firstIdentity secondIdentity thirdIdentity fourthIdentity
  rw [lineLevi_inverse]
  fin_cases row <;> fin_cases column <;>
    simp [lineLevi_val, lineUnipotent, upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three, firstIdentity, secondIdentity,
      thirdIdentity, fourthIdentity, mul_add, mul_assoc]

theorem integralBadLine_conjAct_coordinates (element : ℤˣ × binaryArithmeticLevel)
    (radical : Multiplicative (ℤ × ℤ)) :
    (integralBadLineSplitting.conjAct element radical).toAdd =
      (element.1.val * (radical.toAdd.1 * element.2.val.inv 0 0 +
          radical.toAdd.2 * element.2.val.inv 1 0),
        element.1.val * (radical.toAdd.1 * element.2.val.inv 0 1 +
          radical.toAdd.2 * element.2.val.inv 1 1)) := by
  have equality := integralBadLineExtension.inl_conjAct_comm
    (e := integralBadLineLeviSection element) (n := radical)
  have matrices := congrArg (fun value : integralBadLineStabilizer => value.val) equality
  change (integralBadLineRadicalEmbedding
      (integralBadLineSplitting.conjAct element radical)).val =
    lineLevi element.1 element.2.val *
      lineUnipotent radical.toAdd.1 radical.toAdd.2 * (lineLevi element.1 element.2.val)⁻¹
    at matrices
  rw [lineLevi_unipotent_conjugation] at matrices
  apply Prod.ext
  · exact congrArg (fun value : IntegralGL3 => value.val 0 1) matrices
  · exact congrArg (fun value : IntegralGL3 => value.val 0 2) matrices

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
