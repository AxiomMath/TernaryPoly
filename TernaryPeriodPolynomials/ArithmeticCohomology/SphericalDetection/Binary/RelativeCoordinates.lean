module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderCoefficients
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderNorms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryUnitaryWeight (degree : ℕ) (weight : ℤ) (position : Fin (degree + 2)) : ℤ :=
  weight - (degree + 1 : ℕ) + 2 * (position.val : ℤ)

theorem binaryRelativeLowering_split (cusp : CuspidalRepresentation) (degree : ℕ) (weight : ℤ)
    (vector : binarySmoothValues cusp (Fin (degree + 2))) (position : Fin (degree + 2)) :
    binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) weight vector position =
      finiteTensorOperator (binaryWeightBasis (degree + 1)) (binaryCoefficientLowering degree) vector position +
        cuspLoweringOperator cusp (binaryUnitaryWeight degree weight position) (vector position) := by
  have coefficient :
      finiteTensorOperator (binaryWeightBasis (degree + 1)) (binaryCoefficientLowering degree) vector position =
        finiteTensorOperator (binaryWeightBasis (degree + 1))
            (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative 1)) vector position -
          Complex.I • finiteTensorOperator (binaryWeightBasis (degree + 1))
            (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative Complex.I)) vector position +
          (1 / 2 : ℂ) • ((Complex.I * ((degree + 1 : ℕ) - 2 * (position.val : ℂ))) • vector position) := by
    rw [binaryCoefficientLowering, finiteTensorOperator_add, finiteTensorOperator_sub,
      finiteTensorOperator_smul, finiteTensorOperator_smul]
    simp only [_root_.add_apply, _root_.sub_apply, _root_.smul_apply, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, binaryCoefficientRotation_tensor]
  rw [coefficient]
  simp only [binaryRelativeLowering, binaryTensorDifferential, cuspLoweringOperator,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.piMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    ContinuousLinearMap.coe_coe, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    binaryUnitaryWeight, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Int.cast_ofNat, Nat.cast_add, Nat.cast_one, Int.cast_one]
  module

theorem binaryRelativeRaising_split (cusp : CuspidalRepresentation) (degree : ℕ) (weight : ℤ)
    (vector : binarySmoothValues cusp (Fin (degree + 2))) (position : Fin (degree + 2)) :
    binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) weight vector position =
      finiteTensorOperator (binaryWeightBasis (degree + 1)) (binaryCoefficientRaising degree) vector position +
        cuspRaisingOperator cusp (binaryUnitaryWeight degree weight position) (vector position) := by
  have coefficient :
      finiteTensorOperator (binaryWeightBasis (degree + 1)) (binaryCoefficientRaising degree) vector position =
        finiteTensorOperator (binaryWeightBasis (degree + 1))
            (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative 1)) vector position +
          Complex.I • finiteTensorOperator (binaryWeightBasis (degree + 1))
            (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative Complex.I)) vector position +
          (1 / 2 : ℂ) • ((Complex.I * ((degree + 1 : ℕ) - 2 * (position.val : ℂ))) • vector position) := by
    rw [binaryCoefficientRaising, finiteTensorOperator_add, finiteTensorOperator_add,
      finiteTensorOperator_smul, finiteTensorOperator_smul]
    simp only [_root_.add_apply, _root_.smul_apply, Pi.add_apply, Pi.smul_apply, binaryCoefficientRotation_tensor]
  rw [coefficient]
  simp only [binaryRelativeRaising, binaryTensorDifferential, cuspRaisingOperator,
    LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.piMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    ContinuousLinearMap.coe_coe, Pi.add_apply, Pi.smul_apply,
    binaryUnitaryWeight, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Int.cast_ofNat, Nat.cast_add, Nat.cast_one, Int.cast_one]
  module

theorem binaryRelativeLowering_zero (cusp : CuspidalRepresentation) (degree : ℕ) (weight : ℤ)
    (vector : binarySmoothValues cusp (Fin (degree + 2))) :
    binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) weight vector 0 =
      cuspLoweringOperator cusp (weight - (degree + 1 : ℕ)) (vector 0) := by
  rw [binaryRelativeLowering_split, binaryCoefficientLowering_tensor_zero, zero_add]
  simp only [binaryUnitaryWeight, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero]

theorem binaryRelativeLowering_succ (cusp : CuspidalRepresentation) (degree : ℕ) (weight : ℤ)
    (vector : binarySmoothValues cusp (Fin (degree + 2))) (position : Fin (degree + 1)) :
    binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) weight vector position.succ =
      (Complex.I * ((degree + 1 - position.val : ℕ) : ℂ)) • vector position.castSucc +
        cuspLoweringOperator cusp (binaryUnitaryWeight degree weight position.succ) (vector position.succ) := by
  rw [binaryRelativeLowering_split, binaryCoefficientLowering_tensor_succ]

theorem binaryRelativeRaising_castSucc (cusp : CuspidalRepresentation) (degree : ℕ) (weight : ℤ)
    (vector : binarySmoothValues cusp (Fin (degree + 2))) (position : Fin (degree + 1)) :
    binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) weight vector position.castSucc =
      (-Complex.I * ((position.val + 1 : ℕ) : ℂ)) • vector position.succ +
        cuspRaisingOperator cusp (binaryUnitaryWeight degree weight position.castSucc) (vector position.castSucc) := by
  rw [binaryRelativeRaising_split, binaryCoefficientRaising_tensor_castSucc]

theorem binaryRelativeRaising_last (cusp : CuspidalRepresentation) (degree : ℕ) (weight : ℤ)
    (vector : binarySmoothValues cusp (Fin (degree + 2))) :
    binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) weight vector (Fin.last (degree + 1)) =
      cuspRaisingOperator cusp (weight + (degree + 1 : ℕ)) (vector (Fin.last (degree + 1))) := by
  rw [binaryRelativeRaising_split, binaryCoefficientRaising_tensor_last, zero_add]
  have arithmetic : binaryUnitaryWeight degree weight (Fin.last (degree + 1)) = weight + (degree + 1 : ℕ) := by
    simp only [binaryUnitaryWeight, Fin.val_last]
    omega
  rw [arithmetic]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
