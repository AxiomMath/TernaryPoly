module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Varying
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section


/-! Differentiation of the actual polynomial substitution, in the fixed factorial norm. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open SL3PolynomialCoercivity MvPolynomial
open scoped ContDiff Matrix.Norms.Elementwise


 theorem factorialPairing_infinitesimal_mul_X (B : Mat) (p q : Poly) (i : Fin 3) :
    factorialPairing q (infinitesimal B (p * X i)) =
      -(∑ j : Fin 3, B i j * factorialPairing (pderiv j q) p) +
        factorialPairing (pderiv i q) (infinitesimal B p) := by
  rw [Derivation.leibniz, infinitesimal_X]
  simp only [smul_eq_mul, map_add, mul_neg, Finset.mul_sum, map_neg, map_sum]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have h : p * (B i j • X j) = B i j • (X j * p) := by
      simp only [smul_eq_C_mul]
      ring
    rw [h, map_smul, smul_eq_mul, factorialPairing_X_right]
  · rw [factorialPairing_X_right]

theorem hasDerivAt_matrixPairing_identity (B : Mat) (A : ℝ → Mat)
    (hA : HasDerivAt A (-B) 0) (h0 : A 0 = 1) (p q : Poly) :
    HasDerivAt (fun t => matrixPairing (A t) q p) (factorialPairing q (infinitesimal B p)) 0 := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C r =>
    simpa [matrixPairing] using (hasDerivAt_const (0 : ℝ) (factorialPairing q (C r)))
  | add p r hp hr =>
    convert! (hp q).add (hr q) using 1 <;> simp [matrixPairing]
    rfl
  | mul_X p i hp =>
    simp_rw [matrixPairing_mul_X]
    have h := HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j)).mul (hp (pderiv j q)))
    convert! h using 1
    rw [factorialPairing_infinitesimal_mul_X]
    simp [h0, matrixPairing, realSubstitute_one, Finset.sum_add_distrib,
      Matrix.one_apply, Finset.sum_neg_distrib]

def coefficientSubstitution (n : ℕ) (A : Mat) : Coefficients n →ₗ[ℝ] Coefficients n :=
  ((realSubstitute A).toLinearMap.comp (homogeneousSubmodule (Fin 3) ℝ n).subtype).codRestrict _
    (fun p => realSubstitute_preserves_degree A p.property)

@[simp] theorem coefficientSubstitution_apply (n : ℕ) (A : Mat) (p : Coefficients n) :
    (coefficientSubstitution n A p).val = realSubstitute A p.val := rfl

theorem coefficientSubstitution_dual (n : ℕ) (A : Mat) (p : Coefficients n) :
    coefficientSubstitution n A p =
      (InnerProductSpace.toDual ℝ (Coefficients n)).symm (matrixContinuousBilin n A.transpose p) := by
  apply (InnerProductSpace.toDual ℝ (Coefficients n)).injective
  ext q
  simp only [InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply,
    matrixContinuousBilin_apply, coefficient_inner, coefficientSubstitution_apply, matrixPairing]
  exact realSubstitute_transpose_adjoint A p.val q.val

theorem contDiff_coefficientSubstitution (n : ℕ) (p : Coefficients n) :
    ContDiff ℝ ∞ (fun A : Mat => coefficientSubstitution n A p) := by
  simp_rw [coefficientSubstitution_dual]
  apply (InnerProductSpace.toDual ℝ (Coefficients n)).symm.toContinuousLinearEquiv.contDiff.comp
  apply ContDiff.clm_apply _ contDiff_const
  apply (contDiff_matrixContinuousBilin n).comp
  exact contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => contDiff_apply_apply ℝ ℝ j i))

def coefficientInfinitesimal (n : ℕ) (B : Mat) : Coefficients n →ₗ[ℝ] Coefficients n :=
  ((infinitesimal B).toLinearMap.comp (homogeneousSubmodule (Fin 3) ℝ n).subtype).codRestrict _
    (fun p => infinitesimal_preserves_degree B p.property)

@[simp] theorem coefficientInfinitesimal_apply (n : ℕ) (B : Mat) (p : Coefficients n) :
    (coefficientInfinitesimal n B p).val = infinitesimal B p.val := rfl

theorem hasDerivAt_coefficientSubstitution_identity (n : ℕ) (B : Mat) (A : ℝ → Mat)
    (hA : HasDerivAt A (-B) 0) (h0 : A 0 = 1) (p : Coefficients n) :
    HasDerivAt (fun t => coefficientSubstitution n (A t) p) (coefficientInfinitesimal n B p) 0 := by
  have hd := ((contDiff_coefficientSubstitution n p).differentiable (by simp)).differentiableAt.comp
    0 hA.differentiableAt
  have he : deriv (fun t => coefficientSubstitution n (A t) p) 0 = coefficientInfinitesimal n B p := by
    apply ext_inner_left ℝ
    intro q
    have h := (hasDerivAt_const (0 : ℝ) q).inner ℝ hd.hasDerivAt
    have h' : HasDerivAt (fun t => matrixPairing (A t) q.val p.val)
        (inner ℝ q (deriv (fun t => coefficientSubstitution n (A t) p) 0)) 0 := by
      convert! h using 1
      simp [coefficient_inner, Function.comp_def]
    exact h'.unique (hasDerivAt_matrixPairing_identity B A hA h0 p.val q.val)
  rw [← he]
  exact hd.hasDerivAt

end TernaryPoly.PolynomialCoefficientMetric
