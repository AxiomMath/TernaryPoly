module

public import TernaryPeriodPolynomials.Analysis.Compact.Weighted.MatrixAdjoint

@[expose] public section

/-! Exact scalar cutoff commutators for the actual first-order coordinate expressions. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- Multiplication by a variable cutoff adds precisely the principal-symbol term. -/
theorem firstOrder_cutoff (v : E) (a b c f : E → ℝ) {x : E}
    (hc : DifferentiableAt ℝ c x) (hf : DifferentiableAt ℝ f x) :
    firstOrder v a b (fun y => c y * f y) x =
      c x * firstOrder v a b f x + a x * fderiv ℝ c x v * f x := by
  simp only [firstOrder, fderiv_fun_mul hc hf, add_apply,
    smul_apply, smul_eq_mul]
  ring

/-- The transpose divergence has the opposite principal-symbol cutoff term. -/
theorem transposeOrder_cutoff (v : E) (a b c g : E → ℝ) {x : E}
    (ha : DifferentiableAt ℝ a x) (hc : DifferentiableAt ℝ c x)
    (hg : DifferentiableAt ℝ g x) :
    transposeOrder v a b (fun y => c y * g y) x =
      c x * transposeOrder v a b g x - a x * fderiv ℝ c x v * g x := by
  change b x * (c x * g x) - fderiv ℝ (a * (c * g)) x v =
    c x * (b x * g x - fderiv ℝ (a * g) x v) - a x * fderiv ℝ c x v * g x
  rw [(ha.hasFDerivAt.mul (hc.hasFDerivAt.mul hg.hasFDerivAt)).fderiv,
    (ha.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply]
  ring

/-- The forward cutoff symbol in the fixed finite coordinate arrays. -/
def matrixSymbol (v : K → E) (a : J → I → K → E → ℝ)
    (c : E → ℝ) (f : I → E → ℝ) (j : J) (x : E) : ℝ :=
  ∑ i, ∑ k, a j i k x * fderiv ℝ c x (v k) * f i x

/-- The transposed cutoff symbol, before inverse-Gram multiplication. -/
def matrixSymbolTranspose (v : K → E) (a : J → I → K → E → ℝ)
    (c : E → ℝ) (g : J → E → ℝ) (i : I) (x : E) : ℝ :=
  ∑ j, ∑ k, a j i k x * fderiv ℝ c x (v k) * g j x

omit [Fintype J] in
theorem matrixFirstOrder_cutoff (v : K → E) (a b : J → I → K → E → ℝ)
    (c : E → ℝ) (f : I → E → ℝ) {x : E}
    (hc : DifferentiableAt ℝ c x) (hf : ∀ i, DifferentiableAt ℝ (f i) x) (j : J) :
    matrixFirstOrder v a b (fun i y => c y * f i y) j x =
      c x * matrixFirstOrder v a b f j x + matrixSymbol v a c f j x := by
  simp only [matrixFirstOrder, firstOrder_cutoff _ _ _ _ _ hc (hf _),
    Finset.sum_add_distrib, ← Finset.mul_sum, matrixSymbol]

omit [Fintype I] in
theorem matrixTranspose_cutoff (v : K → E) (a b : J → I → K → E → ℝ)
    (c : E → ℝ) (g : J → E → ℝ) {x : E}
    (ha : ∀ j i k, DifferentiableAt ℝ (a j i k) x)
    (hc : DifferentiableAt ℝ c x) (hg : ∀ j, DifferentiableAt ℝ (g j) x) (i : I) :
    matrixTranspose v a b (fun j y => c y * g j y) i x =
      c x * matrixTranspose v a b g i x - matrixSymbolTranspose v a c g i x := by
  simp only [matrixTranspose, transposeOrder_cutoff _ _ _ _ _ (ha _ _ _) hc (hg _),
    Finset.sum_sub_distrib, ← Finset.mul_sum, matrixSymbolTranspose]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Metric dualization commutes with multiplication by a scalar function. -/
theorem metricDual_cutoff (M : E → Matrix I I ℝ) (c : E → ℝ)
    (f : I → E → ℝ) (i : I) (x : E) :
    metricDual M (fun i y => c y * f i y) i x = c x * metricDual M f i x := by
  simp only [metricDual, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end TernaryPoly.CompactCoordinateIntegration
