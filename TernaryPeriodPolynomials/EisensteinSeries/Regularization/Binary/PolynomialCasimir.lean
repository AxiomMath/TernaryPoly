module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.HomogeneousCoordinates

@[expose] public section


open GeneralEisenstein MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def binaryPolynomialEntry (row column : Fin 2) : Module.End ℂ Binary.Poly :=
  (LinearMap.mulLeft ℂ (X column)).comp (pderiv row).toLinearMap

noncomputable def binaryPolynomialEuler : Module.End ℂ Binary.Poly :=
  binaryPolynomialEntry 0 0 + binaryPolynomialEntry 1 1

noncomputable def binaryPolynomialSplit : Module.End ℂ Binary.Poly :=
  -binaryPolynomialEntry 0 0 + binaryPolynomialEntry 1 1

noncomputable def binaryPolynomialSymmetric : Module.End ℂ Binary.Poly :=
  -binaryPolynomialEntry 0 1 - binaryPolynomialEntry 1 0

noncomputable def binaryPolynomialRotation : Module.End ℂ Binary.Poly :=
  -binaryPolynomialEntry 0 1 + binaryPolynomialEntry 1 0

theorem binaryPolynomialCasimir_euler (polynomial : Binary.Poly) :
    binaryPolynomialSplit (binaryPolynomialSplit polynomial) +
      binaryPolynomialSymmetric (binaryPolynomialSymmetric polynomial) -
        binaryPolynomialRotation (binaryPolynomialRotation polynomial) =
      binaryPolynomialEuler (binaryPolynomialEuler polynomial) + 2 • binaryPolynomialEuler polynomial := by
  simp only [binaryPolynomialSplit, binaryPolynomialSymmetric, binaryPolynomialRotation,
    binaryPolynomialEuler, binaryPolynomialEntry, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    map_add, map_sub, map_neg, pderiv_mul, pderiv_X, Pi.single_apply]
  norm_num
  ring

theorem binaryPolynomialEuler_homogeneous {degree : ℕ} (polynomial : Binary.HomogeneousPoly degree) :
    binaryPolynomialEuler polynomial.val = degree • polynomial.val := by
  simpa only [binaryPolynomialEuler, binaryPolynomialEntry, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, Fin.sum_univ_two]
    using polynomial.property.sum_X_mul_pderiv

theorem binaryPolynomialCasimir_homogeneous {degree : ℕ} (polynomial : Binary.HomogeneousPoly degree) :
    binaryPolynomialSplit (binaryPolynomialSplit polynomial.val) +
      binaryPolynomialSymmetric (binaryPolynomialSymmetric polynomial.val) -
        binaryPolynomialRotation (binaryPolynomialRotation polynomial.val) =
      (degree * (degree + 2)) • polynomial.val := by
  rw [binaryPolynomialCasimir_euler, binaryPolynomialEuler_homogeneous, map_nsmul,
    binaryPolynomialEuler_homogeneous, smul_smul, smul_smul, ← add_smul]
  congr 1
  ring

theorem binaryPolynomialEntry_homogeneous (degree : ℕ) (row column : Fin 2)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    binaryPolynomialEntry row column polynomial.val ∈ Binary.HomogeneousPoly (degree + 1) := by
  have homogeneous := (isHomogeneous_X (R := ℂ) column).mul (polynomial.property.pderiv (i := row))
  change (X column * pderiv row polynomial.val).IsHomogeneous (degree + 1)
  simpa only [Nat.add_sub_cancel, Nat.add_comm] using homogeneous

noncomputable def binaryCoefficientEntry (degree : ℕ) (row column : Fin 2) :
    Module.End ℂ (Binary.HomogeneousPoly (degree + 1)) :=
  ((binaryPolynomialEntry row column).comp (Binary.HomogeneousPoly (degree + 1)).subtype).codRestrict
    (Binary.HomogeneousPoly (degree + 1)) (binaryPolynomialEntry_homogeneous degree row column)

noncomputable def binaryCoefficientSplit (degree : ℕ) : Module.End ℂ (Binary.HomogeneousPoly (degree + 1)) :=
  -binaryCoefficientEntry degree 0 0 + binaryCoefficientEntry degree 1 1

noncomputable def binaryCoefficientSymmetric (degree : ℕ) : Module.End ℂ (Binary.HomogeneousPoly (degree + 1)) :=
  -binaryCoefficientEntry degree 0 1 - binaryCoefficientEntry degree 1 0

noncomputable def binaryCoefficientRotation (degree : ℕ) : Module.End ℂ (Binary.HomogeneousPoly (degree + 1)) :=
  -binaryCoefficientEntry degree 0 1 + binaryCoefficientEntry degree 1 0

theorem binaryCoefficient_casimir (degree : ℕ) :
    binaryCoefficientSplit degree * binaryCoefficientSplit degree +
      binaryCoefficientSymmetric degree * binaryCoefficientSymmetric degree -
        binaryCoefficientRotation degree * binaryCoefficientRotation degree =
      (((degree : ℂ) + 1) * ((degree : ℂ) + 3)) • (1 : Module.End ℂ (Binary.HomogeneousPoly (degree + 1))) := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  change binaryPolynomialSplit (binaryPolynomialSplit polynomial.val) +
    binaryPolynomialSymmetric (binaryPolynomialSymmetric polynomial.val) -
      binaryPolynomialRotation (binaryPolynomialRotation polynomial.val) =
    (((degree : ℂ) + 1) * ((degree : ℂ) + 3)) • polynomial.val
  rw [binaryPolynomialCasimir_homogeneous, ← Nat.cast_smul_eq_nsmul ℂ]
  congr 1
  push_cast
  ring

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
