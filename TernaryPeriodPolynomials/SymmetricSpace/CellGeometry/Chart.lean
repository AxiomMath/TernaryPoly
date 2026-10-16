module

public import TernaryPeriodPolynomials.SymmetricSpace.CellGeometry.Convex
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add

@[expose] public section


/-!
# Appendix B cell calculation: the chart `(w₁, w₂, t) ↦ (Cw, t)` and the homeomorphism `Tfib ≃ₜ Tcell`

Formalized by Claude Sonnet 5.5.  Paper: "The image is the standard ternary cell, and its residue coefficient at `a = 0` is the same
polynomial `q(b,c)` throughout the fibre. No derivative or change of the variables `b, c` occurs in integration.  The Jacobian from `(w₁,w₂,t)` to `(Cw,t)` is positive."

* `chartMap_hasFDerivAt`, `chartJac_det`: the chart `(w₁,w₂,t) ↦ (w₁ + t w₂, t w₁ + w₂, t)` is differentiable with Jacobian matrix `chartJac` of determinant `1 - t²`, positive on the standard edge.
* `cellMat t w`: on the Voronoi cell, `G(w, C(t))` is the unit-diagonal Gram matrix with off-diagonal entries `(Cw)₁, (Cw)₂, t` (`Gmat_eq_cellMat`).
* `TparamHomeo : Tfib ≃ₜ Tcell`: the parametrization `(t, w) ↦ G(w, C(t))` of the standard cell by the Voronoi fibration over the standard edge is a homeomorphism.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBCellGeometry

open TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry Matrix

/-- The chart `(w₁, w₂, t) ↦ (w₁ + t w₂, t w₁ + w₂, t) = (Cw, t)`. -/
def chartMap (x : Fin 3 → ℝ) : Fin 3 → ℝ := ![x 0 + x 2 * x 1, x 2 * x 0 + x 1, x 2]

/-- Its Jacobian matrix. -/
def chartJac (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, x 2, x 1; x 2, 1, x 0; 0, 0, 1]

theorem chartJac_det (x : Fin 3 → ℝ) : (chartJac x).det = 1 - x 2 ^ 2 := by
  simp [chartJac, Matrix.det_fin_three]
  ring

/-- **The Jacobian from `(w₁, w₂, t)` to `(Cw, t)` is positive on the standard edge.** -/
theorem chartJac_det_pos (x : Fin 3 → ℝ) (hx : |x 2| ≤ 1 / 2) : 0 < (chartJac x).det := by
  rw [chartJac_det]
  have := abs_le.mp hx
  nlinarith

theorem chartMap_hasFDerivAt (x : Fin 3 → ℝ) :
    HasFDerivAt chartMap (LinearMap.toContinuousLinearMap (Matrix.toLin' (chartJac x))) x := by
  have d0 : HasFDerivAt (fun y : Fin 3 → ℝ => y 0) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0) x :=
    hasFDerivAt_apply 0 x
  have d1 : HasFDerivAt (fun y : Fin 3 → ℝ => y 1) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1) x :=
    hasFDerivAt_apply 1 x
  have d2 : HasFDerivAt (fun y : Fin 3 → ℝ => y 2) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2) x :=
    hasFDerivAt_apply 2 x
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · have h : HasFDerivAt (fun y : Fin 3 → ℝ => y 0 + y 2 * y 1) _ x := d0.add (d2.mul d1)
    refine h.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp [chartJac, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
    try ring
  · have h : HasFDerivAt (fun y : Fin 3 → ℝ => y 2 * y 0 + y 1) _ x := (d2.mul d0).add d1
    refine h.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp [chartJac, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
    try ring
  · refine d2.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp [chartJac, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]

/-- The unit-diagonal Gram matrix with off-diagonal entries `(Cw)₁, (Cw)₂, t`. -/
def cellMat (t : ℝ) (w : Vec2) : Mat3 :=
  !![1, w 0 + t * w 1, t * w 0 + w 1; w 0 + t * w 1, 1, t; t * w 0 + w 1, t, 1]

theorem Gmat_eq_cellMat {t : ℝ} {w : Vec2} (hw : w ∈ Voronoi (Ct t)) : Gmat w (Ct t) = cellMat t w := by
  have hw' : quad (Ct t) w = deltaSq (Ct t) w := hw
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | (show 1 + quad (Ct t) w - deltaSq (Ct t) w = 1
       rw [hw']
       ring)
    | simp [Gmat, cellMat, Ct, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The inverse chart: `t = A₁₂` and `w = (1 - t²)⁻¹ (A₀₁ - t A₀₂, A₀₂ - t A₀₁)`. -/
def chartInv (A : Mat3) : ℝ × Vec2 :=
  (A 1 2, ![(A 0 1 - A 1 2 * A 0 2) / (1 - A 1 2 ^ 2), (A 0 2 - A 1 2 * A 0 1) / (1 - A 1 2 ^ 2)])

theorem chartInv_cellMat {t : ℝ} (ht : |t| ≤ 1 / 2) (w : Vec2) : chartInv (cellMat t w) = (t, w) := by
  have h := abs_le.mp ht
  have hd : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith
  refine Prod.ext (by simp [chartInv, cellMat]) ?_
  funext i
  fin_cases i <;> simp [chartInv, cellMat] <;> (try field_simp) <;> (try ring)

theorem Tcell_chartInv_mem {A : Mat3} (hA : A ∈ Tcell) : chartInv A ∈ Tfib := by
  obtain ⟨t, ht, w, hw, rfl⟩ := Tcell_eq_Gmat hA
  rw [Gmat_eq_cellMat hw, chartInv_cellMat ht]
  exact ⟨ht, hw⟩

theorem Tcell_denom {A : Mat3} (hA : A ∈ Tcell) : (1 : ℝ) - A 1 2 ^ 2 ≠ 0 := by
  obtain ⟨t, ht, w, hw, rfl⟩ := Tcell_eq_Gmat hA
  rw [Gmat_eq_cellMat hw]
  have h := abs_le.mp ht
  show (1 : ℝ) - (t) ^ 2 ≠ 0
  nlinarith

theorem Tparam_apply_val (p : Tfib) : (Tparam p).1 = cellMat p.1.1 p.1.2 := Gmat_eq_cellMat p.2.2

/-- **The standard cell is homeomorphic to the Voronoi fibration over the standard edge**, by `(t, w) ↦ G(w, C(t))`. -/
def TparamHomeo : Tfib ≃ₜ Tcell where
  toEquiv := Tparam
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have : (fun p : Tfib => Gmat p.1.2 (Ct p.1.1)) = fun p => cellMat p.1.1 p.1.2 :=
      funext fun p => Gmat_eq_cellMat p.2.2
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [cellMat] <;> fun_prop
  continuous_invFun := by
    have hfun : ∀ A : Tcell, Tparam.symm A = ⟨chartInv A.1, Tcell_chartInv_mem A.2⟩ := by
      intro A
      rw [Equiv.symm_apply_eq]
      apply Subtype.ext
      obtain ⟨t, ht, w, hw, hA⟩ := Tcell_eq_Gmat A.2
      have h1 : chartInv A.1 = (t, w) := by rw [hA, Gmat_eq_cellMat hw, chartInv_cellMat ht]
      show A.1 = (Tparam ⟨chartInv A.1, Tcell_chartInv_mem A.2⟩).1
      rw [Tparam_apply_val]
      simp only [h1]
      rw [hA, Gmat_eq_cellMat hw]
    have hc : ∀ i j, Continuous fun A : Tcell => A.1 i j := fun i j =>
      (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    have hd : ∀ A : Tcell, (1 : ℝ) - A.1 1 2 ^ 2 ≠ 0 := fun A => Tcell_denom A.2
    have hf : Continuous fun A : Tcell => chartInv A.1 := by
      refine Continuous.prodMk (hc 1 2) ?_
      refine continuous_pi fun i => ?_
      fin_cases i
      · exact ((hc 0 1).sub ((hc 1 2).mul (hc 0 2))).div (continuous_const.sub ((hc 1 2).pow 2)) hd
      · exact ((hc 0 2).sub ((hc 1 2).mul (hc 0 1))).div (continuous_const.sub ((hc 1 2).pow 2)) hd
    show Continuous (Tparam.symm : Tcell → Tfib)
    have hfun' : (Tparam.symm : Tcell → Tfib) = fun A => ⟨chartInv A.1, Tcell_chartInv_mem A.2⟩ := funext hfun
    rw [hfun']
    exact Continuous.subtype_mk hf _

end TernaryPeriodPolynomials.Argument.AppendixBCellGeometry
