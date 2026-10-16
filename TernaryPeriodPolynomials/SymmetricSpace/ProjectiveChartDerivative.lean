module

public import TernaryPeriodPolynomials.SymmetricSpace.ProjectiveChartOrientation
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.ProjectiveChartOrientation
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixCLM (A : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (Matrix.toLin' A).toContinuousLinearMap

def rowCLM (c : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, c i • ContinuousLinearMap.proj i

@[simp] theorem matrixCLM_apply (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    matrixCLM A x = A *ᵥ x := rfl

omit [DecidableEq ι] in
@[simp] theorem rowCLM_apply (c x : ι → ℝ) : rowCLM c x=c ⬝ᵥ x := by
  simp [rowCLM,dotProduct]

def projective (A : Matrix ι ι ℝ) (b c : ι → ℝ) (d : ℝ) (x : ι → ℝ) : ι → ℝ :=
  (denominator c d x)⁻¹ • numerator A b x

/-- The matrix used in the determinant identity is the actual Frechet derivative. -/
theorem hasFDerivAt_projective (A : Matrix ι ι ℝ) (b c : ι → ℝ) (d : ℝ)
    (x : ι → ℝ) (ht : denominator c d x ≠ 0) :
    HasFDerivAt (projective A b c d) (matrixCLM (jacobian A b c d x)) x := by
  have hn : HasFDerivAt (numerator A b) (matrixCLM A) x :=
    (matrixCLM A).hasFDerivAt.add_const b
  have hd : HasFDerivAt (denominator c d) (rowCLM c) x := by
    apply ((rowCLM c).hasFDerivAt.add_const d).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun z => (congrArg (·+d) (rowCLM_apply c z)).symm)
  have hi := (hasFDerivAt_inv ht).comp x hd
  have h := hi.smul hn
  apply h.congr_fderiv
  symm
  apply ContinuousLinearMap.ext
  intro v
  ext i
  simp only [matrixCLM_apply,_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,rowCLM_apply,Pi.add_apply,Pi.smul_apply,
    smul_eq_mul,Matrix.mulVec,dotProduct,jacobian]
  simp only [Finset.mul_sum,Finset.sum_mul,inv_pow,Function.comp_apply]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact determinant of the genuine derivative as a real linear endomorphism. -/
theorem fderiv_det (A : Matrix ι ι ℝ) (b c : ι → ℝ) (d : ℝ)
    (x : ι → ℝ) (ht : denominator c d x ≠ 0) :
    LinearMap.det (fderiv ℝ (projective A b c d) x).toLinearMap =
      (denominator c d x)⁻¹^(Fintype.card ι+1)*(homogeneous A b c d).det := by
  rw [(hasFDerivAt_projective A b c d x ht).fderiv]
  change LinearMap.det (Matrix.toLin' (jacobian A b c d x))=_
  rw [LinearMap.det_toLin',jacobian_det A b c d x ht]

/-- Positivity belongs to the actual derivative, not just a candidate matrix. -/
theorem fderiv_det_pos (A : Matrix ι ι ℝ) (b c : ι → ℝ) (d : ℝ)
    (x : ι → ℝ) (ht : 0 < denominator c d x) (hdet : 0 < (homogeneous A b c d).det) :
    0 < LinearMap.det (fderiv ℝ (projective A b c d) x).toLinearMap := by
  rw [fderiv_det A b c d x (ne_of_gt ht)]
  exact mul_pos (pow_pos (inv_pos.mpr ht) _) hdet

end TernaryPoly.ProjectiveChartOrientation
