module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeightBasis
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeOperators

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryCoefficientLowering (degree : ℕ) : Module.End ℂ (Binary.HomogeneousPoly (degree + 1)) :=
  binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative 1) -
    Complex.I • binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative Complex.I) +
      (1 / 2 : ℂ) • binaryInfinitesimalCoefficient degree binaryInfinitesimalRotation

def binaryCoefficientRaising (degree : ℕ) : Module.End ℂ (Binary.HomogeneousPoly (degree + 1)) :=
  binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative 1) +
    Complex.I • binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative Complex.I) +
      (1 / 2 : ℂ) • binaryInfinitesimalCoefficient degree binaryInfinitesimalRotation

theorem binaryCoefficientLowering_coe (degree : ℕ) (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    (binaryCoefficientLowering degree polynomial).val = binaryPolynomialLowering polynomial.val := by
  change binaryInfinitesimalSubstitution (binaryAffineInverseDerivative 1) polynomial.val -
      Complex.I • binaryInfinitesimalSubstitution (binaryAffineInverseDerivative Complex.I) polynomial.val +
      (1 / 2 : ℂ) • binaryInfinitesimalSubstitution binaryInfinitesimalRotation polynomial.val = _
  simp only [← binaryInfinitesimalDerivation_apply]
  rfl

theorem binaryCoefficientRaising_coe (degree : ℕ) (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    (binaryCoefficientRaising degree polynomial).val = binaryPolynomialRaising polynomial.val := by
  change binaryInfinitesimalSubstitution (binaryAffineInverseDerivative 1) polynomial.val +
      Complex.I • binaryInfinitesimalSubstitution (binaryAffineInverseDerivative Complex.I) polynomial.val +
      (1 / 2 : ℂ) • binaryInfinitesimalSubstitution binaryInfinitesimalRotation polynomial.val = _
  simp only [← binaryInfinitesimalDerivation_apply]
  rfl

theorem binaryCoefficientLowering_basis (degree : ℕ) (position : Fin (degree + 1)) :
    binaryCoefficientLowering degree (binaryWeightBasis (degree + 1) position.castSucc) =
      (Complex.I * ((degree + 1 - position.val : ℕ) : ℂ)) • binaryWeightBasis (degree + 1) position.succ := by
  apply Subtype.ext
  rw [binaryCoefficientLowering_coe, Submodule.coe_smul]
  exact binaryWeightBasis_lowering_interior _ _

theorem binaryCoefficientRaising_basis (degree : ℕ) (position : Fin (degree + 1)) :
    binaryCoefficientRaising degree (binaryWeightBasis (degree + 1) position.succ) =
      (-Complex.I * ((position.val + 1 : ℕ) : ℂ)) • binaryWeightBasis (degree + 1) position.castSucc := by
  apply Subtype.ext
  rw [binaryCoefficientRaising_coe, Submodule.coe_smul]
  exact binaryWeightBasis_raising_interior _ _

theorem binaryCoefficientLowering_last (degree : ℕ) :
    binaryCoefficientLowering degree (binaryWeightBasis (degree + 1) (Fin.last (degree + 1))) = 0 := by
  apply Subtype.ext
  rw [binaryCoefficientLowering_coe, binaryWeightBasis_lowering_last]
  rfl

theorem binaryCoefficientRaising_zero (degree : ℕ) :
    binaryCoefficientRaising degree (binaryWeightBasis (degree + 1) 0) = 0 := by
  apply Subtype.ext
  rw [binaryCoefficientRaising_coe, binaryWeightBasis_raising_zero]
  rfl

theorem binaryCoefficientRotation_basis (degree : ℕ) (position : Fin (degree + 2)) :
    binaryInfinitesimalCoefficient degree binaryInfinitesimalRotation (binaryWeightBasis (degree + 1) position) =
      (Complex.I * ((degree + 1 : ℕ) - 2 * (position.val : ℂ))) • binaryWeightBasis (degree + 1) position := by
  apply Subtype.ext
  exact binaryWeightBasis_rotation _ _

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem binaryCoefficientLowering_tensor_succ (degree : ℕ) (vectors : Fin (degree + 2) → H)
    (position : Fin (degree + 1)) :
    finiteTensorOperator (binaryWeightBasis (degree + 1)) (binaryCoefficientLowering degree) vectors position.succ =
      (Complex.I * ((degree + 1 - position.val : ℕ) : ℂ)) • vectors position.castSucc := by
  rw [finiteTensorOperator_apply, Fin.sum_univ_castSucc]
  simp only [binaryCoefficientLowering_basis, binaryCoefficientLowering_last, map_zero, zero_smul, add_zero,
    map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Fin.succ_inj, smul_eq_mul]
  simp

theorem binaryCoefficientLowering_tensor_zero (degree : ℕ) (vectors : Fin (degree + 2) → H) :
    finiteTensorOperator (binaryWeightBasis (degree + 1)) (binaryCoefficientLowering degree) vectors 0 = 0 := by
  rw [finiteTensorOperator_apply, Fin.sum_univ_castSucc]
  simp [binaryCoefficientLowering_basis, binaryCoefficientLowering_last, Module.Basis.coord_apply,
    Fin.succ_ne_zero]

theorem binaryCoefficientRaising_tensor_castSucc (degree : ℕ) (vectors : Fin (degree + 2) → H)
    (position : Fin (degree + 1)) :
    finiteTensorOperator (binaryWeightBasis (degree + 1)) (binaryCoefficientRaising degree) vectors position.castSucc =
      (-Complex.I * ((position.val + 1 : ℕ) : ℂ)) • vectors position.succ := by
  rw [finiteTensorOperator_apply, Fin.sum_univ_succ]
  simp only [binaryCoefficientRaising_basis, binaryCoefficientRaising_zero, map_zero, zero_smul, zero_add,
    map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Fin.castSucc_inj, smul_eq_mul]
  simp

theorem binaryCoefficientRaising_tensor_last (degree : ℕ) (vectors : Fin (degree + 2) → H) :
    finiteTensorOperator (binaryWeightBasis (degree + 1)) (binaryCoefficientRaising degree) vectors (Fin.last (degree + 1)) = 0 := by
  rw [finiteTensorOperator_apply, Fin.sum_univ_succ]
  simp [binaryCoefficientRaising_basis, binaryCoefficientRaising_zero, Module.Basis.coord_apply,
    Fin.castSucc_ne_last]

theorem binaryCoefficientRotation_tensor (degree : ℕ) (vectors : Fin (degree + 2) → H)
    (position : Fin (degree + 2)) :
    finiteTensorOperator (binaryWeightBasis (degree + 1))
        (binaryInfinitesimalCoefficient degree binaryInfinitesimalRotation) vectors position =
      (Complex.I * ((degree + 1 : ℕ) - 2 * (position.val : ℂ))) • vectors position := by
  simp [finiteTensorOperator_apply, binaryCoefficientRotation_basis, Module.Basis.coord_apply,
    Finsupp.single_apply]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
