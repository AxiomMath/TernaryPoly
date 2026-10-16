module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.FrameOrbit

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

theorem integral_det_cast_inverse (frame : IntegralGL3) :
    (((GeneralLinearGroup.det frame : ℤ) : ℂ))⁻¹ =
      ((GeneralLinearGroup.det frame : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or (GeneralLinearGroup.det frame) with determinant | determinant <;>
    rw [determinant] <;> norm_num

theorem rationalCoefficient_integralFrame (degree : ℕ) (frame : IntegralGL3)
    (polynomial : HomogeneousPoly degree) :
    (rationalCoefficientComponent degree trivialCharacter
      (GeneralLinearGroup.map (Int.castRingHom ℚ) frame) polynomial).val =
      C ((GeneralLinearGroup.det frame : ℤ) : ℂ) *
        substitute ((GeneralLinearGroup.map (Int.castRingHom ℂ) frame)⁻¹).val polynomial.val := by
  let complex_matrix : GL3 := GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (GeneralLinearGroup.map (Int.castRingHom ℚ) frame))
  have complex_eq : complex_matrix = GeneralLinearGroup.map (Int.castRingHom ℂ) frame := by
    apply GeneralLinearGroup.ext
    intro row column
    simp [complex_matrix]
  have trivial_action :
      (rationalCoefficientComponent degree trivialCharacter
        (GeneralLinearGroup.map (Int.castRingHom ℚ) frame) polynomial).val =
        action (-1) complex_matrix polynomial.val := by
    simp [rationalCoefficientComponent, realCoefficientComponent, componentCharacter,
      trivialCharacter, realCoefficient, complex_matrix]
  have determinant : ((GeneralLinearGroup.det complex_matrix : ℂˣ) : ℂ) =
      ((GeneralLinearGroup.det frame : ℤ) : ℂ) := by
    rw [complex_eq]
    change (frame.val.map (Int.castRingHom ℂ)).det = (frame.val.det : ℂ)
    exact (RingHom.map_det (Int.castRingHom ℂ) frame.val).symm
  rw [trivial_action, action_apply]
  change ((GeneralLinearGroup.det complex_matrix : ℂˣ) : ℂ) ^ (-1 : ℤ) •
    substitute (complex_matrix⁻¹).val polynomial.val = _
  rw [determinant, zpow_neg_one, integral_det_cast_inverse, complex_eq,
    MvPolynomial.smul_eq_C_mul]

def framePolynomial (degree : ℕ) (frame : IntegralGL3) (polynomial : HomogeneousPoly degree) :
    HomogeneousPoly degree := rationalCoefficientComponent degree trivialCharacter
      (GeneralLinearGroup.map (Int.castRingHom ℚ) frame) polynomial

theorem referenceFrame_value (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    (framePolynomial degree referenceFrame polynomial).val =
      substitute ((GeneralLinearGroup.map (Int.castRingHom ℂ) referenceFrame)⁻¹).val polynomial.val := by
  rw [framePolynomial, rationalCoefficient_integralFrame]
  have determinant : (GeneralLinearGroup.det referenceFrame : ℤ) = 1 := by
    change referenceFrame.val.det = 1
    norm_num [referenceFrame, Matrix.det_fin_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  rw [determinant]
  simp

theorem framePolynomial_orbit (degree : ℕ) (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1)
    (polynomial : HomogeneousPoly degree) :
    framePolynomial degree frame polynomial =
      rationalCoefficientComponent degree trivialCharacter (frameTransition frame normalized).val
        (framePolynomial degree referenceFrame polynomial) := by
  rw [framePolynomial, framePolynomial, ← Module.End.mul_apply, ← map_mul,
    frameTransition_reference]

theorem polynomialFunctional_exists_of_referenceCycleMap {degree : ℕ}
    (polynomial : HomogeneousPoly degree)
    (cycle_map : goodCycleModule →ₗ[ℂ] HomogeneousPoly degree)
    (equivariant : ∀ matrix : rationalLevel, ∀ chain : goodCycleModule,
      cycle_map (translateGoodCycle matrix chain) =
        rationalCoefficientComponent degree trivialCharacter matrix.val (cycle_map chain))
    (reference_value : cycle_map (normalizedApartmentCycle referenceFrame referenceFrame_normalized) =
      framePolynomial degree referenceFrame polynomial) :
    ∃ functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree,
      IsPolynomialFunctional polynomial functional := by
  apply polynomialFunctional_exists_of_goodCycleMap polynomial cycle_map equivariant
  intro frame normalized
  rw [normalizedApartmentCycle_orbit, equivariant, reference_value, ← framePolynomial_orbit]
  exact rationalCoefficient_integralFrame degree frame polynomial

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
