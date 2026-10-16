module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CoefficientPathDerivative

@[expose] public section


open GeneralEisenstein Matrix MvPolynomial
open scoped BigOperators

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binaryCoefficientEntry_val (degree : ℕ) (row column : Fin 2)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    (binaryCoefficientEntry degree row column polynomial).val = X column * pderiv row polynomial.val := rfl

noncomputable def binaryCoefficientDerivedOperator (degree : ℕ)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    Module.End ℂ (Binary.HomogeneousPoly (degree + 1)) :=
  -∑ row, ∑ column, (direction row column : ℂ) • binaryCoefficientEntry degree row column

theorem binaryCoefficientDerivedOperator_val (degree : ℕ)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    (binaryCoefficientDerivedOperator degree direction polynomial).val =
      binarySubstitutionDifferential 1 (fun row column => -(direction row column : ℂ)) polynomial.val := by
  simp only [binaryCoefficientDerivedOperator, LinearMap.neg_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Submodule.coe_neg, Submodule.coe_add, Submodule.coe_smul,
    binarySubstitutionDifferential, Binary.substitute_one, AlgHom.id_apply, Binary.linearForm,
    Fin.sum_univ_two, binaryCoefficientEntry_val]
  simp only [Algebra.smul_def, map_neg, algebraMap_eq]
  ring

theorem binaryCoefficientDerivedOperator_split (degree : ℕ) :
    binaryCoefficientDerivedOperator degree binarySplitDirection = binaryCoefficientSplit degree := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  rw [binaryCoefficientDerivedOperator_val]
  change _ = binaryPolynomialSplit polynomial.val
  simp [binarySubstitutionDifferential, binarySplitDirection, Binary.linearForm,
    Binary.substitute_one, binaryPolynomialSplit, binaryPolynomialEntry, Fin.sum_univ_two]

theorem binaryCoefficientDerivedOperator_symmetric (degree : ℕ) :
    binaryCoefficientDerivedOperator degree binarySymmetricDirection = binaryCoefficientSymmetric degree := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  rw [binaryCoefficientDerivedOperator_val]
  change _ = binaryPolynomialSymmetric polynomial.val
  simp [binarySubstitutionDifferential, binarySymmetricDirection, Binary.linearForm,
    Binary.substitute_one, binaryPolynomialSymmetric, binaryPolynomialEntry, Fin.sum_univ_two,
    sub_eq_add_neg]

theorem binaryCoefficientDerivedOperator_rotation (degree : ℕ) :
    binaryCoefficientDerivedOperator degree binaryRotationDirection = binaryCoefficientRotation degree := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  rw [binaryCoefficientDerivedOperator_val]
  change _ = binaryPolynomialRotation polynomial.val
  simp [binarySubstitutionDifferential, binaryRotationDirection, Binary.linearForm,
    Binary.substitute_one, binaryPolynomialRotation, binaryPolynomialEntry, Fin.sum_univ_two]

theorem binary_twistedCoefficient_derived_hasDerivAt
    (degree : ℕ) (path : ℝ → BinaryRealGL) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : path point = 1)
    (derivative : ∀ row column, HasDerivAt (fun t => (path t).val row column) (tangent row column) point)
    (traceless : Matrix.trace tangent = 0)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) (monomial : Fin 2 →₀ ℕ) :
    HasDerivAt (fun t => (normPower (GeneralLinearGroup.det (Adelic.atInfinity (path t))) (((degree : ℂ) + 3) / 2) •
        binaryCoefficient degree (path t) polynomial).val.coeff monomial)
      ((binaryCoefficientDerivedOperator degree tangent polynomial).val.coeff monomial) point := by
  rw [binaryCoefficientDerivedOperator_val]
  exact binary_twistedCoefficient_hasDerivAt_traceless degree path tangent point identity derivative traceless polynomial monomial

theorem binaryCoefficientDerivedOperator_casimir (degree : ℕ) :
    binaryCoefficientDerivedOperator degree binarySplitDirection *
        binaryCoefficientDerivedOperator degree binarySplitDirection +
      binaryCoefficientDerivedOperator degree binarySymmetricDirection *
        binaryCoefficientDerivedOperator degree binarySymmetricDirection -
      binaryCoefficientDerivedOperator degree binaryRotationDirection *
        binaryCoefficientDerivedOperator degree binaryRotationDirection =
      (((degree : ℂ) + 1) * ((degree : ℂ) + 3)) •
        (1 : Module.End ℂ (Binary.HomogeneousPoly (degree + 1))) := by
  rw [binaryCoefficientDerivedOperator_split, binaryCoefficientDerivedOperator_symmetric,
    binaryCoefficientDerivedOperator_rotation]
  exact binaryCoefficient_casimir degree

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
