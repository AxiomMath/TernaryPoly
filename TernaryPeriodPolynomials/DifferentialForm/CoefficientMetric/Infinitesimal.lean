module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Derivative
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricSmooth

@[expose] public section


/-! The derivative of the literal inverse-substitution representation and its metric adjoint. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open SL3PolynomialCoercivity SymmetricSpacePositive
open scoped ContDiff Matrix.Norms.Elementwise

theorem hasDerivAt_matrix_product {A B : ℝ → Mat} {A' B' : Mat} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun u => A u * B u) (A' * B t + A t * B') t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hB k) j))
  convert! h using 1
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

theorem contDiff_matrix_inverse_curve (g : ℝ → RealGL)
    (hg : ContDiff ℝ ∞ (fun t => (g t : Mat))) :
    ContDiff ℝ ∞ (fun t => ((g t)⁻¹ : RealGL).val) := by
  simp only [Matrix.GeneralLinearGroup.coe_inv]
  rw [← contDiffOn_univ]
  exact SymmetricSpaceTraceMetric.contDiffOn_inverse hg.contDiffOn (fun t _ => (g t).isUnit)

theorem hasDerivAt_matrix_inverse_identity (g : ℝ → RealGL)
    (hg : ContDiff ℝ ∞ (fun t => (g t : Mat))) (h0 : g 0 = 1) (A : Mat)
    (hA : HasDerivAt (fun t => (g t : Mat)) A 0) :
    HasDerivAt (fun t => ((g t)⁻¹ : RealGL).val) (-A) 0 := by
  have hi := ((contDiff_matrix_inverse_curve g hg).differentiable (by simp)).differentiableAt (x := 0) |>.hasDerivAt
  have hp := hasDerivAt_matrix_product hA hi
  have hz : A + deriv (fun t => ((g t)⁻¹ : RealGL).val) 0 = 0 := by
    have hc : HasDerivAt (fun _ : ℝ => (1 : Mat))
        (A + deriv (fun t => ((g t)⁻¹ : RealGL).val) 0) 0 := by
      convert! hp using 1 <;> simp [h0]
      rfl
    exact hc.unique (hasDerivAt_const (0 : ℝ) (1 : Mat))
  convert! hi using 1
  exact (eq_neg_of_add_eq_zero_right hz).symm

/-- The actual real group action differentiates to the exact derivation used in the
coefficient Hodge estimate, for every smooth group curve through the identity. -/
theorem hasDerivAt_realHomogeneousAction_identity (n : ℕ) (g : ℝ → RealGL)
    (hg : ContDiff ℝ ∞ (fun t => (g t : Mat))) (h0 : g 0 = 1) (A : Mat)
    (hA : HasDerivAt (fun t => (g t : Mat)) A 0) (p : Coefficients n) :
    HasDerivAt (fun t => realHomogeneousAction n (g t) p) (coefficientInfinitesimal n A p) 0 := by
  exact hasDerivAt_coefficientSubstitution_identity n A _
    (hasDerivAt_matrix_inverse_identity g hg h0 A hA) (by simp [h0]) p

theorem coefficientInfinitesimal_basepoint_adjoint (n : ℕ) (A : Mat) (p q : Coefficients n) :
    coefficientMetric n basepoint (coefficientInfinitesimal n A p) q =
      coefficientMetric n basepoint p (coefficientInfinitesimal n A.transpose q) := by
  simp only [coefficientMetric_basepoint, coefficientInfinitesimal_apply]
  exact infinitesimal_transpose_adjoint A p.val q.val

end TernaryPoly.PolynomialCoefficientMetric
