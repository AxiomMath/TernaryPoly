module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.SeriesTransl
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.Transport

@[expose] public section


/-!
# The face form of the series at the cusp `h⁻¹ P h`

The pullback of the series `𝓔_{h⁻¹Ph}` to the boundary model `e(P)` along `i_h = planeAct(h⁻¹) ∘ ι`
is the `ρ(h⁻¹)`-twist of the standard face form (`cuspFaceForm_eq_twist`), a consequence of the
translation law `𝓔_{h⁻¹Ph} = ρ(h)⁻¹ h^* 𝓔_P` (`seriesFormK_false_eq`).

Formalized by Claude Sonnet 5.5.
-/

open ContinuousAlternatingMap TernaryPoly.SmoothCoveringDeRham
open scoped MatrixGroups ContDiff
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass

/-- Pulling back by `h` and then by `h⁻¹` is the identity on `Ω`. -/
theorem formPullback_pull_inv (h : SL(3, ℤ))
    (W : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) {p : Fin 5 → ℝ} (hp : p ∈ Omega)
    (i j : Fin 5) :
    formPullback (planeAct (realMat h⁻¹)) (formPullback (planeAct (realMat h)) W) p i j =
      W p i j := by
  rw [← formPullback_comp (planeAct (realMat h⁻¹)) (planeAct (realMat h)) W p
    (differentiableAt_planeAct (det_realMat _) hp)
    (differentiableAt_planeAct (det_realMat _) (planeAct_mem (det_realMat _) hp)) i j]
  have hev : (planeAct (realMat h) ∘ planeAct (realMat h⁻¹)) =ᶠ[nhds p] fun y => y + 0 :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hp) fun y hy => by
      simp only [Function.comp]
      rw [← planeAct_mul (det_realMat h⁻¹) hy, ← realMat_mul, mul_inv_cancel, realMat_one,
        planeAct_one hy, add_zero]
  rw [formPullback_congr W hev, formPullback_add_const]
  simp

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)

/-- **The pullback of the series at the cusp `h⁻¹Ph` to its boundary model is the `ρ(h⁻¹)`-twist of
the standard face form.** -/
theorem cuspFaceForm_eq_twist (h : SL(3, ℤ)) :
    ((cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h) (gammaN N)
      (leviGroup N) n f hn (leviInCusp_gammaN N h)) :
        ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h) (rhoAt N h n)) :
          Form (F := Coef n) faceSet 2) =
      ZigZag.twForm (rhoOfSL n h⁻¹) 2 (eisensteinFace N n f hn : Form (F := Coef n) faceSet 2) := by
  apply Form.ext
  intro x hx
  rw [ZigZag.twForm_apply, coefficientFormMap_apply]
  apply ext2Face
  intro i j
  apply Coef.toPoly_injective
  have hp : ptOf x ∈ Omega := ptOf_mem hx
  have hRHS : Coef.toPoly ((rhoOfSL n h⁻¹).compContinuousAlternatingMap
      (((eisensteinFace N n f hn : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x)
        ![Pi.single i 1, Pi.single j 1]) =
      rho (realMat h⁻¹) (seriesForm (gammaN N) n f (ptOf x) i.castSucc j.castSucc) := by
    show Coef.toPoly (rhoOfSL n h⁻¹ (((eisensteinFace N n f hn : Form (F := Coef n) faceSet 2) :
      RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1])) = _
    rw [toPoly_rhoOfSL]
    congr 1
    exact congrArg Coef.toPoly (faceForm_basis (gammaNPlaneData N) (inclP N)
      (fun g => gammaNPlaneData_plm N g)
      (planeEisensteinComponents (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N)) hx i j)
  rw [hRHS]
  rw [toPoly_cuspFaceForm_basis N h _ hx i j]
  -- the chain rule for the composite `planeAct h⁻¹ ∘ ptOf`
  have hd : HasFDerivAt (cuspPt h)
      ((fderiv ℝ (planeAct (realMat h⁻¹)) (ptOf x)).comp ptCLM) x :=
    (differentiableAt_planeAct (det_realMat h⁻¹) hp).hasFDerivAt.comp x (hasFDerivAt_ptOf x)
  have hw : ∀ k : Fin 4, fderiv ℝ (cuspPt h) x (Pi.single k 1) =
      fderiv ℝ (planeAct (realMat h⁻¹)) (ptOf x) (Pi.single k.castSucc 1) := by
    intro k
    rw [hd.fderiv]
    simp [ptCLM_single]
  simp_rw [hw]
  have hΩ : cuspPt h x ∈ Omega := planeAct_mem (det_realMat h⁻¹) hp
  have hcomp : ∀ a b : Fin 5,
      Coef.toPoly ((planeEisensteinAtComponents false (CuspData.ofSL h) (gammaN N) (leviGroup N) n f
        hn (leviInCusp_gammaN N h)).comp (cuspPt h x) a b) =
      rho (realMat h⁻¹) (formPullback (planeAct (realMat h)) (seriesForm (gammaN N) n f)
        (cuspPt h x) a b) := by
    intro a b
    show seriesFormK false (CuspData.ofSL h) (gammaN N) n f (cuspPt h x) a b = _
    rw [seriesFormK_false_eq N n f hn h hΩ, realMat_inv]
  simp_rw [hcomp]
  have hrho : ∀ (c : ℂ) (q : MvPolynomial (Fin 3) ℂ), rho (realMat h⁻¹) (C c * q) =
      C c * rho (realMat h⁻¹) q := fun c q => rho_C_mul _ _ _
  simp_rw [← hrho]
  have key := formPullback_pull_inv h (seriesForm (gammaN N) n f) hp i.castSucc j.castSucc
  unfold formPullback at key
  simp_rw [← rho_sum]
  congr 1

end TernaryPeriodPolynomials.Argument.EisensteinClass
