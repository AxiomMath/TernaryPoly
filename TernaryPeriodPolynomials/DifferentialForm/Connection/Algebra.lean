module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Basic

@[expose] public section


/-! Algebra of the literal coefficient action used by the metric connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open scoped ContDiff Matrix.Norms.Elementwise

abbrev Mat := PolynomialCoefficientMetric.Mat

@[simp] theorem coefficientSubstitution_one (n : ℕ) (p : Coefficients n) :
    coefficientSubstitution n 1 p = p := by
  apply Subtype.ext
  simp [realSubstitute_one]

theorem coefficientSubstitution_mul (n : ℕ) (A B : Mat) (p : Coefficients n) :
    coefficientSubstitution n A (coefficientSubstitution n B p) = coefficientSubstitution n (B * A) p := by
  apply Subtype.ext
  exact realSubstitute_apply_apply A B p.val

@[simp] theorem coefficientInfinitesimal_add (n : ℕ) (A B : Mat) (p : Coefficients n) :
    coefficientInfinitesimal n (A + B) p = coefficientInfinitesimal n A p + coefficientInfinitesimal n B p := by
  apply Subtype.ext
  exact congrArg (fun D : Derivation ℝ Poly Poly => D p.val) (infinitesimal_add A B)

@[simp] theorem coefficientInfinitesimal_smul (n : ℕ) (c : ℝ) (A : Mat) (p : Coefficients n) :
    coefficientInfinitesimal n (c • A) p = c • coefficientInfinitesimal n A p := by
  apply Subtype.ext
  exact congrArg (fun D : Derivation ℝ Poly Poly => D p.val) (infinitesimal_smul c A)

@[simp] theorem coefficientInfinitesimal_neg (n : ℕ) (A : Mat) (p : Coefficients n) :
    coefficientInfinitesimal n (-A) p = -coefficientInfinitesimal n A p := by
  simpa only [neg_one_smul] using coefficientInfinitesimal_smul n (-1) A p

@[simp] theorem coefficientInfinitesimal_zero (n : ℕ) (p : Coefficients n) :
    coefficientInfinitesimal n 0 p = 0 := by
  simpa using coefficientInfinitesimal_smul n 0 (0 : Mat) p

theorem coefficientInfinitesimal_commutator (n : ℕ) (A B : Mat) (p : Coefficients n) :
    coefficientInfinitesimal n (A * B - B * A) p =
      coefficientInfinitesimal n A (coefficientInfinitesimal n B p) -
        coefficientInfinitesimal n B (coefficientInfinitesimal n A p) := by
  apply Subtype.ext
  exact congrArg (fun D : Derivation ℝ Poly Poly => D p.val) (infinitesimal_commutator A B)

/-- The actual endomorphism, continuous in the coefficient norm. -/
def infinitesimalCLM (n : ℕ) (A : Mat) : Coefficients n →L[ℝ] Coefficients n :=
  (coefficientInfinitesimal n A).toContinuousLinearMap

@[simp] theorem infinitesimalCLM_apply (n : ℕ) (A : Mat) (p : Coefficients n) :
    infinitesimalCLM n A p = coefficientInfinitesimal n A p := rfl

/-- Linear dependence of the infinitesimal endomorphism on its matrix. -/
def infinitesimalLinear (n : ℕ) : Mat →ₗ[ℝ] (Coefficients n →L[ℝ] Coefficients n) where
  toFun := infinitesimalCLM n
  map_add' A B := by apply ContinuousLinearMap.ext; intro p; exact coefficientInfinitesimal_add n A B p
  map_smul' c A := by apply ContinuousLinearMap.ext; intro p; exact coefficientInfinitesimal_smul n c A p

theorem contDiff_infinitesimalCLM (n : ℕ) : ContDiff ℝ ∞ (infinitesimalCLM n) :=
  ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Mat) (F := Coefficients n →L[ℝ] Coefficients n)
    (infinitesimalLinear n).toContinuousLinearMap

end TernaryPoly.PolynomialFormConnection
