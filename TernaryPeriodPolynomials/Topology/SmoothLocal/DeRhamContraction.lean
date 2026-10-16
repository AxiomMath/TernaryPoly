module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothLocalDeRham
open Set ContinuousAlternatingMap
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- Insertion of one vector into the first slot of an alternating form. -/
def insertCLM (x : E) : (E [⋀^Fin (n + 1)]→L[ℝ] F) →L[ℝ] (E [⋀^Fin n]→L[ℝ] F) :=
  (ContinuousLinearMap.apply ℝ (E [⋀^Fin n]→L[ℝ] F) x).comp
    (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := n)).toContinuousLinearMap

@[simp] theorem insertCLM_apply (x : E) (w : E [⋀^Fin (n + 1)]→L[ℝ] F) :
    insertCLM x w = w.curryLeft x := rfl

/-- The algebraic identity behind the radial Cartan homotopy formula. -/
theorem alternatize_insert (h : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) :
    alternatizeUncurryFin ((insertCLM x).comp h) + (alternatizeUncurryFin h).curryLeft x = h x := by
  ext v
  simp only [ContinuousAlternatingMap.add_apply, alternatizeUncurryFin_apply,
    ContinuousLinearMap.comp_apply, insertCLM_apply, curryLeft_apply_apply]
  conv_lhs => rhs; rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero, Fin.removeNth_zero,
    Fin.val_succ, pow_succ, Matrix.cons_val_succ]
  have hremove (i : Fin (n + 1)) :
      i.succ.removeNth (Matrix.vecCons x v) = Matrix.vecCons x (i.removeNth v) := by
    ext j
    cases j using Fin.cases with
    | zero => simp [Fin.removeNth]
    | succ j => simp [Fin.removeNth]
  simp only [hremove, mul_smul, neg_one_smul, smul_neg]
  rw [Finset.sum_neg_distrib]
  abel

/-- Differentiate insertion of the radial vector into a varying form. -/
theorem radialInsert_hasFDerivAt {w : RawForm E F (n + 1)} {x : E}
    (hw : DifferentiableAt ℝ w x) (a : E) :
    HasFDerivAt (fun y => (w y).curryLeft (y - a))
      ((w x).curryLeft + (insertCLM (x - a)).comp (fderiv ℝ w x)) x := by
  have hc : HasFDerivAt (fun y => (w y).curryLeft)
      ((curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := n)).toContinuousLinearMap.comp
        (fderiv ℝ w x)) x := by
    let L : (E [⋀^Fin (n + 1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] E [⋀^Fin n]→L[ℝ] F) :=
      (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := n)).toContinuousLinearMap
    have hL : HasFDerivAt L L (w x) := L.hasFDerivAt
    exact HasFDerivAt.comp (𝕜 := ℝ) (f := w) (g := L) x hL hw.hasFDerivAt
  have h := hc.clm_apply ((hasFDerivAt_id x).sub_const a)
  convert h using 1 <;> ext v <;> rfl

/-- Cartan's radial identity with the exact normalization used by Mathlib. -/
theorem extDeriv_radialInsert {w : RawForm E F (n + 1)} {x : E}
    (hw : DifferentiableAt ℝ w x) (a : E) :
    extDeriv (fun y => (w y).curryLeft (y - a)) x + (extDeriv w x).curryLeft (x - a) =
      (n + 1) • w x + fderiv ℝ w x (x - a) := by
  unfold extDeriv
  rw [(radialInsert_hasFDerivAt hw a).fderiv, alternatizeUncurryFin_add,
    alternatizeUncurryFin_curryLeft, add_assoc, alternatize_insert]

end TernaryPoly.SmoothLocalDeRham
