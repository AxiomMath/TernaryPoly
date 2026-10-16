module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.PolynomialLadders
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeOperators
public import Mathlib.RingTheory.Derivation.Lie

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryInfinitesimalDerivation_affine_commutator :
    ⁅binaryInfinitesimalDerivation (binaryAffineInverseDerivative Complex.I),
      binaryInfinitesimalDerivation (binaryAffineInverseDerivative 1)⁆ =
        binaryInfinitesimalDerivation (binaryAffineInverseDerivative 1) := by
  apply MvPolynomial.derivation_ext
  intro position
  fin_cases position <;>
    simp [Derivation.commutator_apply, binaryInfinitesimalDerivation,
      binaryAffineInverseDerivative, Binary.linearForm, Fin.sum_univ_two,
      Derivation.leibniz]
  simp only [neg_div, one_div, map_neg]
  linear_combination -(X 1) * binary_half_constant

theorem binaryInfinitesimalCoefficient_affine_commutator (degree : ℕ) :
    binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative Complex.I) *
        binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative 1) -
      binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative 1) *
        binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative Complex.I) =
      binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative 1) := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  change binaryInfinitesimalSubstitution (binaryAffineInverseDerivative Complex.I)
      (binaryInfinitesimalSubstitution (binaryAffineInverseDerivative 1) polynomial.val) -
    binaryInfinitesimalSubstitution (binaryAffineInverseDerivative 1)
      (binaryInfinitesimalSubstitution (binaryAffineInverseDerivative Complex.I) polynomial.val) =
    binaryInfinitesimalSubstitution (binaryAffineInverseDerivative 1) polynomial.val
  have equality := congrArg (fun derivation : Derivation ℂ Binary.Poly Binary.Poly => derivation polynomial.val)
    binaryInfinitesimalDerivation_affine_commutator
  simpa only [Derivation.commutator_apply, binaryInfinitesimalDerivation_apply] using equality

theorem finiteTensorOperator_commutes_linear {index V H : Type} [Fintype index]
    [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (basis : Module.Basis index ℂ V) (operator : Module.End ℂ V)
    (action : Module.End ℂ H) (vectors : index → H) :
    finiteTensorOperator basis operator (fun position => action (vectors position)) =
      fun position => action (finiteTensorOperator basis operator vectors position) := by
  funext position
  simp only [finiteTensorOperator_apply, map_sum, map_smul]

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryTensorDifferential_commutator (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    binaryTensorDifferential cusp basis Complex.I * binaryTensorDifferential cusp basis 1 -
      binaryTensorDifferential cusp basis 1 * binaryTensorDifferential cusp basis Complex.I =
        binaryTensorDifferential cusp basis 1 := by
  let coefficient (direction : ℂ) :=
    finiteTensorOperator (H := cuspAffineSmoothValues cusp) basis
      (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative direction))
  have coefficient_commutator (vector : binarySmoothValues cusp index) :
      coefficient Complex.I (coefficient 1 vector) - coefficient 1 (coefficient Complex.I vector) = coefficient 1 vector := by
    have equality := congrArg (fun operator => finiteTensorOperator (H := cuspAffineSmoothValues cusp) basis operator vector)
      (binaryInfinitesimalCoefficient_affine_commutator degree)
    simpa only [finiteTensorOperator_sub, finiteTensorOperator_mul,
      _root_.sub_apply, ContinuousLinearMap.comp_apply] using equality
  apply LinearMap.ext
  intro vector
  have first_commutes := finiteTensorOperator_commutes_linear basis
    (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative Complex.I))
    (cuspAffineDifferential cusp 1) vector
  have second_commutes := finiteTensorOperator_commutes_linear basis
    (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative 1))
    (cuspAffineDifferential cusp Complex.I) vector
  funext position
  have coefficients := congrFun (coefficient_commutator vector) position
  have first := congrFun first_commutes position
  have second := congrFun second_commutes position
  have unitary := LinearMap.congr_fun (cuspAffineDifferential_commutator cusp) (vector position)
  have pi_function (direction : ℂ) :
      (LinearMap.pi fun i : index => cuspAffineDifferential cusp direction ∘ₗ LinearMap.proj i) vector =
        fun position => cuspAffineDifferential cusp direction (vector position) := rfl
  simp only [binaryTensorDifferential, LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.piMap, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, ContinuousLinearMap.coe_coe, map_add, Pi.add_apply, Pi.sub_apply]
  dsimp only [coefficient, Pi.sub_apply] at coefficients
  rw [pi_function, pi_function, first, second]
  change cuspAffineDifferential cusp Complex.I (cuspAffineDifferential cusp 1 (vector position)) -
    cuspAffineDifferential cusp 1 (cuspAffineDifferential cusp Complex.I (vector position)) =
      cuspAffineDifferential cusp 1 (vector position) at unitary
  have total := congrArg₂ (fun first second => first + second) coefficients unitary
  convert total using 1
  abel

theorem binaryRelativeLadder_commutator (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) (weight : ℤ) :
    binaryRelativeRaising cusp basis (weight - 2) * binaryRelativeLowering cusp basis weight -
      binaryRelativeLowering cusp basis (weight + 2) * binaryRelativeRaising cusp basis weight =
        (weight : ℂ) • 1 := by
  apply LinearMap.ext
  intro vector
  have commutator := LinearMap.congr_fun (binaryTensorDifferential_commutator cusp basis) vector
  change binaryTensorDifferential cusp basis Complex.I (binaryTensorDifferential cusp basis 1 vector) -
    binaryTensorDifferential cusp basis 1 (binaryTensorDifferential cusp basis Complex.I vector) =
      binaryTensorDifferential cusp basis 1 vector at commutator
  change binaryRelativeRaising cusp basis (weight - 2) (binaryRelativeLowering cusp basis weight vector) -
    binaryRelativeLowering cusp basis (weight + 2) (binaryRelativeRaising cusp basis weight vector) = (weight : ℂ) • vector
  calc
    _ = (2 * Complex.I) •
        (binaryTensorDifferential cusp basis Complex.I (binaryTensorDifferential cusp basis 1 vector) -
          binaryTensorDifferential cusp basis 1 (binaryTensorDifferential cusp basis Complex.I vector) -
            binaryTensorDifferential cusp basis 1 vector) + (-(Complex.I ^ 2 * (weight : ℂ))) • vector := by
      simp only [binaryRelativeRaising, binaryRelativeLowering, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, map_add, map_sub, map_smul,
        Int.cast_sub, Int.cast_add, Int.cast_ofNat]
      module
    _ = _ := by rw [commutator]; simp

theorem binaryRelativeLadder_coboundary (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (primitive : binarySmoothValues cusp index) :
    binaryRelativeRaising cusp basis (-2) (binaryRelativeLowering cusp basis 0 primitive) =
      binaryRelativeLowering cusp basis 2 (binaryRelativeRaising cusp basis 0 primitive) := by
  have equality := LinearMap.congr_fun (binaryRelativeLadder_commutator cusp basis 0) primitive
  simpa only [Int.cast_zero, zero_sub, zero_add, zero_smul, LinearMap.zero_apply,
    LinearMap.sub_apply, Module.End.mul_apply, sub_eq_zero] using equality

theorem binaryRelativeLadder_shift (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (lower upper primitive : binarySmoothValues cusp index)
    (closed : binaryRelativeRaising cusp basis (-2) lower = binaryRelativeLowering cusp basis 2 upper) :
    binaryRelativeRaising cusp basis (-2) (lower - binaryRelativeLowering cusp basis 0 primitive) =
      binaryRelativeLowering cusp basis 2 (upper - binaryRelativeRaising cusp basis 0 primitive) := by
  rw [map_sub, map_sub, closed, binaryRelativeLadder_coboundary]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
