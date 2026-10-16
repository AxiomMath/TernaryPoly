module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CoefficientDerivedOperator
public import Mathlib.RingTheory.Derivation.Lie

@[expose] public section


open GeneralEisenstein MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binary_pderiv_commute (first second : Fin 2) (polynomial : Binary.Poly) :
    pderiv first (pderiv second polynomial) = pderiv second (pderiv first polynomial) := by
  have commutator : ⁅pderiv (R := ℂ) first, pderiv (R := ℂ) second⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro index
    simp only [Derivation.commutator_apply, pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  have applied := congrArg (fun derivation : Derivation ℂ Binary.Poly Binary.Poly => derivation polynomial) commutator
  simpa only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] using applied

theorem binaryCoefficient_rotation_split_bracket (degree : ℕ) :
    binaryCoefficientRotation degree * binaryCoefficientSplit degree -
      binaryCoefficientSplit degree * binaryCoefficientRotation degree =
      -(2 • binaryCoefficientSymmetric degree) := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  change binaryPolynomialRotation (binaryPolynomialSplit polynomial.val) -
    binaryPolynomialSplit (binaryPolynomialRotation polynomial.val) = -(2 • binaryPolynomialSymmetric polynomial.val)
  simp only [binaryPolynomialSplit, binaryPolynomialSymmetric, binaryPolynomialRotation, binaryPolynomialEntry,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, map_neg, pderiv_mul, pderiv_X, Pi.single_apply]
  norm_num
  rw [binary_pderiv_commute 1 0]
  ring

theorem binaryCoefficient_rotation_symmetric_bracket (degree : ℕ) :
    binaryCoefficientRotation degree * binaryCoefficientSymmetric degree -
      binaryCoefficientSymmetric degree * binaryCoefficientRotation degree =
      2 • binaryCoefficientSplit degree := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  change binaryPolynomialRotation (binaryPolynomialSymmetric polynomial.val) -
    binaryPolynomialSymmetric (binaryPolynomialRotation polynomial.val) = 2 • binaryPolynomialSplit polynomial.val
  simp only [binaryPolynomialSplit, binaryPolynomialSymmetric, binaryPolynomialRotation, binaryPolynomialEntry,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, map_sub, map_neg, pderiv_mul, pderiv_X, Pi.single_apply]
  norm_num
  rw [binary_pderiv_commute 1 0]
  ring

theorem binaryCoefficient_split_symmetric_bracket (degree : ℕ) :
    binaryCoefficientSplit degree * binaryCoefficientSymmetric degree -
      binaryCoefficientSymmetric degree * binaryCoefficientSplit degree =
      2 • binaryCoefficientRotation degree := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  change binaryPolynomialSplit (binaryPolynomialSymmetric polynomial.val) -
    binaryPolynomialSymmetric (binaryPolynomialSplit polynomial.val) = 2 • binaryPolynomialRotation polynomial.val
  simp only [binaryPolynomialSplit, binaryPolynomialSymmetric, binaryPolynomialRotation, binaryPolynomialEntry,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, map_sub, map_neg, pderiv_mul, pderiv_X, Pi.single_apply]
  norm_num
  rw [binary_pderiv_commute 1 0]
  ring

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
