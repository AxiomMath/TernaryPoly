module

public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.FormalAdjoint
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section


/-! Actual inverse-metric formal adjoints for variable density-weighted matrix pairings. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I]

/-- A matrix times the coefficient vector, in the fixed coordinate basis. -/
def metricDual (M : E → Matrix I I ℝ) (f : I → E → ℝ) (i : I) (x : E) : ℝ :=
  (M x).mulVec (fun l => f l x) i

/-- Both a metric Gram matrix and the coordinate volume density can be included in M. -/
def weightedPairing (M : E → Matrix I I ℝ) (f g : I → E → ℝ) (x : E) : ℝ :=
  ∑ i, f i x * metricDual M g i x

/-- The literal inverse source metric times the transpose divergence of the target metric dual. -/
def weightedMatrixAdjoint (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (v : K → E) (a b : J → I → K → E → ℝ) (g : J → E → ℝ) : I → E → ℝ :=
  metricDual (fun x => (M x)⁻¹) (matrixTranspose v a b (metricDual N g))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DecidableEq I] in
/-- Smooth target metrics and fields give a smooth dual field. -/
theorem contDiff_metricDual {M : E → Matrix I I ℝ} {f : I → E → ℝ}
    {n : WithTop ℕ∞} (hM : ∀ i l, ContDiff ℝ n (fun x => M x i l))
    (hf : ∀ i, ContDiff ℝ n (f i)) (i : I) : ContDiff ℝ n (metricDual M f i) := by
  unfold metricDual Matrix.mulVec dotProduct
  exact ContDiff.sum (fun l _ => (hM i l).mul (hf l))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The inverse metric exactly cancels inside the source pairing. -/
theorem metricDual_weightedMatrixAdjoint (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (hM : ∀ x, IsUnit (M x).det) (v : K → E) (a b : J → I → K → E → ℝ)
    (g : J → E → ℝ) (i : I) (x : E) :
    metricDual M (weightedMatrixAdjoint M N v a b g) i x =
      matrixTranspose v a b (metricDual N g) i x := by
  change ((M x).mulVec ((M x)⁻¹.mulVec (fun l => matrixTranspose v a b (metricDual N g) l x))) i = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hM x), Matrix.one_mulVec]

/-- The actual weighted coordinate integral identity, including inverse Gram and density terms. -/
theorem integral_weightedMatrixAdjoint [DecidableEq J] (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (hM : ∀ x, IsUnit (M x).det) (hN : ∀ j l, ContDiff ℝ 1 (fun x => N x j l))
    (v : K → E) (a b : J → I → K → E → ℝ) (f : I → E → ℝ) (g : J → E → ℝ)
    (ha : ∀ j i k, ContDiff ℝ 1 (a j i k)) (hb : ∀ j i k, Continuous (b j i k))
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hg : ∀ j, ContDiff ℝ 1 (g j))
    (hc : ∀ i, HasCompactSupport (f i)) :
    ∫ x, weightedPairing N (matrixFirstOrder v a b f) g x ∂μ =
      ∫ x, weightedPairing M f (weightedMatrixAdjoint M N v a b g) x ∂μ := by
  simp only [weightedPairing, metricDual_weightedMatrixAdjoint M N hM]
  exact integral_matrixFirstOrder v a b f (metricDual N g) ha hb hf
    (fun j => contDiff_metricDual hN hg j) hc

end TernaryPoly.CompactCoordinateIntegration
