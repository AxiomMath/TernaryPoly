module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Rational
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

@[expose] public section


/-! The literal homogeneous coefficient space is the scalar extension of its rational form. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open SL3PolynomialCoercivity MvPolynomial
open scoped TensorProduct

abbrev ExtendedCoefficients (n : ℕ) := ℝ ⊗[ℚ] RationalCoefficients n

def coefficientBaseChange (n : ℕ) : ExtendedCoefficients n →ₗ[ℝ] Coefficients n :=
  (scalarExtensionLinear n).liftBaseChange ℝ

@[simp] theorem coefficientBaseChange_tmul (n : ℕ) (r : ℝ) (p : RationalCoefficients n) :
    coefficientBaseChange n (r ⊗ₜ[ℚ] p) = r • scalarExtensionCoefficient n p := rfl

def rationalHomogeneousProjection (n : ℕ) : PolynomialGLAction.Poly →ₗ[ℚ] RationalCoefficients n :=
  (homogeneousComponent n).codRestrict _ (homogeneousComponent_mem n)

def realHomogeneousProjection (n : ℕ) : Poly →ₗ[ℝ] Coefficients n :=
  (homogeneousComponent n).codRestrict _ (homogeneousComponent_mem n)

theorem scalarExtension_homogeneousComponent (n : ℕ) (p : PolynomialGLAction.Poly) :
    scalarExtensionPolynomial (homogeneousComponent n p) =
      homogeneousComponent n (scalarExtensionPolynomial p) := by
  ext d
  simp only [scalarExtensionPolynomial, coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

def coefficientBaseChangeInverse (n : ℕ) : Coefficients n →ₗ[ℝ] ExtendedCoefficients n :=
  (rationalHomogeneousProjection n).baseChange ℝ ∘ₗ
    (algebraTensorAlgEquiv ℚ ℝ).symm.toLinearMap ∘ₗ
    (homogeneousSubmodule (Fin 3) ℝ n).subtype

theorem coefficientBaseChange_project (n : ℕ) (z : ℝ ⊗[ℚ] PolynomialGLAction.Poly) :
    coefficientBaseChange n ((rationalHomogeneousProjection n).baseChange ℝ z) =
      realHomogeneousProjection n (algebraTensorAlgEquiv ℚ ℝ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r p =>
    simp only [LinearMap.baseChange_tmul, coefficientBaseChange_tmul,
      algebraTensorAlgEquiv_tmul, map_smul]
    congr 1
    apply Subtype.ext
    exact scalarExtension_homogeneousComponent n p
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coefficientBaseChange_right_inverse (n : ℕ) (p : Coefficients n) :
    coefficientBaseChange n (coefficientBaseChangeInverse n p) = p := by
  change coefficientBaseChange n ((rationalHomogeneousProjection n).baseChange ℝ
    ((algebraTensorAlgEquiv ℚ ℝ).symm p.val)) = p
  rw [coefficientBaseChange_project, AlgEquiv.apply_symm_apply]
  exact Subtype.ext (homogeneousComponent_eq_self p.property)

theorem coefficientBaseChange_left_inverse (n : ℕ) (z : ExtendedCoefficients n) :
    coefficientBaseChangeInverse n (coefficientBaseChange n z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul r p =>
    rw [coefficientBaseChange_tmul, map_smul]
    change r • (rationalHomogeneousProjection n).baseChange ℝ
      ((algebraTensorAlgEquiv ℚ ℝ).symm (MvPolynomial.map (algebraMap ℚ ℝ) p.val)) = _
    rw [algebraTensorAlgEquiv_symm_map, LinearMap.baseChange_tmul]
    have h : rationalHomogeneousProjection n p.val = p :=
      Subtype.ext (homogeneousComponent_eq_self p.property)
    rw [h]
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

def coefficientScalarExtension (n : ℕ) : ExtendedCoefficients n ≃ₗ[ℝ] Coefficients n :=
  LinearEquiv.ofLinearMap (coefficientBaseChange n) (coefficientBaseChangeInverse n)
    (LinearMap.ext (coefficientBaseChange_right_inverse n))
    (LinearMap.ext (coefficientBaseChange_left_inverse n))

@[simp] theorem coefficientScalarExtension_tmul (n : ℕ) (r : ℝ) (p : RationalCoefficients n) :
    coefficientScalarExtension n (r ⊗ₜ[ℚ] p) = r • scalarExtensionCoefficient n p := rfl

theorem coefficientScalarExtension_equivariant (n : ℕ) (e : ℤ)
    (g : SymmetricSpaceCovering.DeckGroup) (z : ExtendedCoefficients n) :
    coefficientScalarExtension n ((rationalDeckRepresentation n e g).baseChange ℝ z) =
      deckRepresentation n g (coefficientScalarExtension n z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r p =>
    simp only [LinearMap.baseChange_tmul, coefficientScalarExtension_tmul, map_smul,
      scalarExtensionCoefficient_equivariant]
  | add x y hx hy => simp only [map_add, hx, hy]

end TernaryPoly.PolynomialCoefficientMetric
