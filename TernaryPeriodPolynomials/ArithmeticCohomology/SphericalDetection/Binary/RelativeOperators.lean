module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.TensorDifferential
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.TangentCoboundary

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

abbrev binarySmoothValues (cusp : CuspidalRepresentation) (index : Type) := index → cuspAffineSmoothValues cusp

def binarySmoothValues_val (cusp : CuspidalRepresentation) :
    binarySmoothValues cusp index →ₗ[ℂ] (index → cusp.H) :=
  LinearMap.piMap (fun _ => (cuspAffineSmoothValues cusp).subtype)

omit [Fintype index] in
theorem binarySmoothValues_val_apply (cusp : CuspidalRepresentation)
    (vector : binarySmoothValues cusp index) (position : index) :
    binarySmoothValues_val cusp vector position = (vector position).val := rfl

omit [Fintype index] in
theorem binarySmoothValues_val_injective (cusp : CuspidalRepresentation) :
    Function.Injective (binarySmoothValues_val (index := index) cusp) := by
  intro first second equality
  funext position
  exact Subtype.ext (congrFun equality position)

theorem binaryAffineOrbitVector_contDiffOn_of_coordinates (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (vector : index → cusp.H) {order : WithTop ℕ∞}
    (regular : ∀ position, ContDiffOn ℝ order (cuspAffineOrbitVector cusp (vector position)) UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffOn ℝ order (binaryAffineOrbitVector cusp basis vector) UpperHalfPlane.upperHalfPlaneSet := by
  have entries (row column : Fin 2) : ContDiffOn ℝ order
      (fun point => binaryUpperSectionMatrix point row column) UpperHalfPlane.upperHalfPlaneSet :=
    contDiffOn_pi.mp (contDiffOn_pi.mp binaryUpperSectionMatrix_contDiffOn row) column
  have coordinate_regular : ContDiffOn ℝ order
      (fun point position => cuspAffineOrbitVector cusp (vector position) point) UpperHalfPlane.upperHalfPlaneSet :=
    contDiffOn_pi.mpr regular
  have coefficient_regular := binaryHilbertCoefficient_contDiffOn cusp basis binaryUpperSectionMatrix entries
    binaryUpperSectionMatrix_invertible _ coordinate_regular
  apply coefficient_regular.congr
  intro point positive
  rw [binaryAffineOrbitVector, binaryHilbertOperator_factor, binaryAffineSection_normalizingFactor _ positive, one_smul]
  rfl

theorem binarySmoothValues_regular (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (vector : binarySmoothValues cusp index) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp vector))
      UpperHalfPlane.upperHalfPlaneSet :=
  binaryAffineOrbitVector_contDiffOn_of_coordinates cusp basis _ (fun position => (vector position).property)

def binaryTensorDifferential (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) (direction : ℂ) :
    Module.End ℂ (binarySmoothValues cusp index) :=
  (finiteTensorOperator (H := cuspAffineSmoothValues cusp) basis
    (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative direction))).toLinearMap +
      LinearMap.piMap (fun _ => cuspAffineDifferential cusp direction)

theorem binaryTensorDifferential_actual (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) (direction : ℂ)
    (vector : binarySmoothValues cusp index) :
    binarySmoothValues_val cusp (binaryTensorDifferential cusp basis direction vector) =
      fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp vector)) Complex.I direction := by
  rw [binaryAffineOrbitVector_fderiv cusp basis _ (binarySmoothValues_regular cusp basis vector)]
  funext position
  change (finiteTensorOperator basis (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative direction)) vector position).val +
    (cuspAffineDifferential cusp direction (vector position)).val = _
  simp only [finiteTensorOperator_apply, Submodule.coe_sum, Submodule.coe_smul, cuspAffineDifferential_apply,
    Pi.add_apply, binarySmoothValues_val_apply]

def binaryRelativeLowering (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) (weight : ℤ) :
    Module.End ℂ (binarySmoothValues cusp index) :=
  binaryTensorDifferential cusp basis 1 - Complex.I • binaryTensorDifferential cusp basis Complex.I +
    (Complex.I * (weight : ℂ) / 2) • 1

def binaryRelativeRaising (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) (weight : ℤ) :
    Module.End ℂ (binarySmoothValues cusp index) :=
  binaryTensorDifferential cusp basis 1 + Complex.I • binaryTensorDifferential cusp basis Complex.I +
    (Complex.I * (weight : ℂ) / 2) • 1

theorem binaryRelativeLowering_actual (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) (weight : ℤ)
    (vector : binarySmoothValues cusp index) :
    binarySmoothValues_val cusp (binaryRelativeLowering cusp basis weight vector) =
      fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp vector)) Complex.I 1 -
        Complex.I • fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp vector)) Complex.I Complex.I +
        (Complex.I * (weight : ℂ) / 2) • binarySmoothValues_val cusp vector := by
  simp only [binaryRelativeLowering, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_add, map_sub, map_smul, binaryTensorDifferential_actual]

theorem binaryRelativeRaising_actual (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) (weight : ℤ)
    (vector : binarySmoothValues cusp index) :
    binarySmoothValues_val cusp (binaryRelativeRaising cusp basis weight vector) =
      fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp vector)) Complex.I 1 +
        Complex.I • fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp vector)) Complex.I Complex.I +
        (Complex.I * (weight : ℂ) / 2) • binarySmoothValues_val cusp vector := by
  simp only [binaryRelativeRaising, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_add, map_smul, binaryTensorDifferential_actual]

theorem binaryRelative_cocycle_iff (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (first second : binarySmoothValues cusp index) :
    binaryRelativeRaising cusp basis (-2) (first - Complex.I • second) =
      binaryRelativeLowering cusp basis 2 (first + Complex.I • second) ↔
        binaryTensorDifferential cusp basis Complex.I first - binaryTensorDifferential cusp basis 1 second = first := by
  have difference :
      binaryRelativeRaising cusp basis (-2) (first - Complex.I • second) -
          binaryRelativeLowering cusp basis 2 (first + Complex.I • second) =
        (2 * Complex.I) • (binaryTensorDifferential cusp basis Complex.I first -
          binaryTensorDifferential cusp basis 1 second - first) := by
    simp only [binaryRelativeRaising, binaryRelativeLowering, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_add, map_sub, map_smul, Int.cast_neg, Int.cast_ofNat]
    module
  rw [← sub_eq_zero, difference, smul_eq_zero]
  simp only [mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) Complex.I_ne_zero, false_or, sub_eq_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
