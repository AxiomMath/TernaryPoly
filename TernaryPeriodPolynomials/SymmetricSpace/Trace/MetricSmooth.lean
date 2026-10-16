module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricCongruence
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Entrywise smoothness of the genuine matrix inverse and trace metric. -/
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix
open scoped ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : Set E}

theorem contDiffOn_det {A : E → Mat} (hA : ContDiffOn ℝ ∞ A s) :
    ContDiffOn ℝ ∞ (fun x => (A x).det) s := by
  simp only [det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply ContDiffOn.mul contDiffOn_const
  apply contDiffOn_prod
  intro i _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp hA (σ i)) i)

theorem contDiffOn_adjugate {A : E → Mat} (hA : ContDiffOn ℝ ∞ A s) :
    ContDiffOn ℝ ∞ (fun x => (A x).adjugate) s := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  change ContDiffOn ℝ ∞ (fun x : E => (A x).adjugate i j) s
  simp only [adjugate_apply]
  apply contDiffOn_det
  apply contDiffOn_pi.mpr
  intro k
  apply contDiffOn_pi.mpr
  intro l
  by_cases h : k = j
  · subst k
    change ContDiffOn ℝ ∞ (fun x : E => (A x).updateRow j (Pi.single i 1) j l) s
    simpa only [Matrix.updateRow_self] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (Pi.single i (1 : ℝ) : Fin 3 → ℝ) l) s)
  · change ContDiffOn ℝ ∞ (fun x : E => (A x).updateRow j (Pi.single i 1) k l) s
    have he : (fun x : E => (A x).updateRow j (Pi.single i 1) k l) =
        (fun x : E => A x k l) := by
      funext x
      exact congrFun (Function.update_of_ne h (Pi.single i 1) (A x)) l
    rw [he]
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hA k) l

/-- No alternative norm on matrices is installed: this proves smoothness in
the same entrywise norm used by the coordinate atlas. -/
theorem contDiffOn_inverse {A : E → Mat} (hA : ContDiffOn ℝ ∞ A s)
    (hinv : ∀ x ∈ s, IsUnit (A x)) : ContDiffOn ℝ ∞ (fun x => (A x)⁻¹) s := by
  have hd : ∀ x ∈ s, (A x).det ≠ 0 := fun x hx =>
    isUnit_iff_ne_zero.mp (((A x).isUnit_iff_isUnit_det).mp (hinv x hx))
  have h := ((contDiffOn_det hA).inv hd).smul (contDiffOn_adjugate hA)
  change ContDiffOn ℝ ∞ (fun x => (A x).det⁻¹ • (A x).adjugate) s at h
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv'] using h

theorem contDiffOn_matrix_mul {A B : E → Mat} (hA : ContDiffOn ℝ ∞ A s)
    (hB : ContDiffOn ℝ ∞ B s) : ContDiffOn ℝ ∞ (fun x => A x * B x) s := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiffOn.sum
  intro k _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp hA i) k).mul
    (contDiffOn_pi.mp (contDiffOn_pi.mp hB k) j)

theorem contDiffOn_trace {A : E → Mat} (hA : ContDiffOn ℝ ∞ A s) :
    ContDiffOn ℝ ∞ (fun x => (A x).trace) s := by
  change ContDiffOn ℝ ∞ (fun x => ∑ i, A x i i) s
  exact ContDiffOn.sum fun i _ => contDiffOn_pi.mp (contDiffOn_pi.mp hA i) i

/-- Joint smoothness of the actual invariant pairing wherever the base matrix is invertible. -/
theorem contDiffOn_tangentPair {A U V : E → Mat} (hA : ContDiffOn ℝ ∞ A s)
    (hU : ContDiffOn ℝ ∞ U s) (hV : ContDiffOn ℝ ∞ V s)
    (hinv : ∀ x ∈ s, IsUnit (A x)) :
    ContDiffOn ℝ ∞ (fun x => tangentPair (A x) (U x) (V x)) s := by
  have hu := contDiffOn_matrix_mul (contDiffOn_inverse hA hinv) hU
  have hv := contDiffOn_matrix_mul (contDiffOn_inverse hA hinv) hV
  simp only [tangentPair_formula]
  exact (contDiffOn_trace (contDiffOn_matrix_mul hu hv)).sub
    (((contDiffOn_trace hu).mul (contDiffOn_trace hv)).div contDiffOn_const (by norm_num))

end TernaryPoly.SymmetricSpaceTraceMetric
