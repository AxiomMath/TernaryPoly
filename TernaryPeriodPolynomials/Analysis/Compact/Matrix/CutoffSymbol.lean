module

public import TernaryPeriodPolynomials.Analysis.Compact.DoubleCutoffCommutatorIdentity
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.FormalAdjoint

@[expose] public section


/-! Both localization terms are exactly the actual first-order commutator with the product cutoff. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
variable {E I J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I] [Fintype K]

theorem firstOrder_two_cutoffs (v : E) (a b χ η f : E → ℝ) (x : E)
    (hχ : DifferentiableAt ℝ χ x) (hη : DifferentiableAt ℝ η x) (hf : DifferentiableAt ℝ f x) :
    firstOrder v a b (fun y => η y * (χ y * f y)) x =
      η x * (χ x * firstOrder v a b f x) +
        ((a x * fderiv ℝ η x v) * (χ x * f x) + η x * ((a x * fderiv ℝ χ x v) * f x)) := by
  rw [firstOrder_cutoff v a b η (fun y => χ y * f y) x hη (hχ.mul hf), firstOrder_cutoff v a b χ f x hχ hf]
  ring

theorem matrixFirstOrder_two_cutoffs (v : K → E) (a b : J → I → K → E → ℝ)
    (χ η : E → ℝ) (f : I → E → ℝ) (j : J) (x : E)
    (hχ : DifferentiableAt ℝ χ x) (hη : DifferentiableAt ℝ η x) (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    matrixFirstOrder v a b (fun i y => η y * (χ y * f i y)) j x -
      η x * (χ x * matrixFirstOrder v a b f j x) =
      ∑ i, ∑ k, ((a j i k x * fderiv ℝ η x (v k)) * (χ x * f i x) +
        η x * ((a j i k x * fderiv ℝ χ x (v k)) * f i x)) := by
  unfold matrixFirstOrder
  simp_rw [firstOrder_two_cutoffs _ _ _ χ η _ x hχ hη (hf _)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end TernaryPoly.CompactCoordinateIntegration
