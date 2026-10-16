module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.SeriesForm
public import TernaryPeriodPolynomials.EisensteinSeries.Class.FaceK

@[expose] public section


/-!
# The face form of the series at any cusp, at any cusp face

Paper: "the same
letters for the rational conjugates".

For `h, h' ∈ SL₃(ℤ)`, the pullback to the boundary model of the cusp `h⁻¹Ph` of the series at the
cusp `h'⁻¹Ph'` is the `ρ(h⁻¹)`-twist of the face form `ι^* E_{k⁻¹Pk}` of the series at the cusp
`k = h' h⁻¹` (`cuspFaceForm_eq_twist_gen`): the series at `h'` is `ρ(h')⁻¹ h'^* E_P`
(`seriesFormK_false_eq`), and `planeAct(h') ∘ planeAct(h⁻¹) = planeAct(h' h⁻¹)` on `Ω`.

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
  TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)

/-- **The pullback of the series at the cusp `h'` to the boundary model of the cusp `h` is the
`ρ(h⁻¹)`-twist of the face form of the series at the cusp `h' h⁻¹`.** -/
theorem cuspFaceForm_eq_twist_gen (h h' : SL(3, ℤ)) :
    ((cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h') (gammaN N)
      (leviGroup N) n f hn (leviInCusp_gammaN N h')) :
        ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h) (rhoAt N h n)) :
          Form (F := Coef n) faceSet 2) =
      ZigZag.twForm (rhoOfSL n h⁻¹) 2
        (faceSeriesK N (h' * h⁻¹) n f hn : Form (F := Coef n) faceSet 2) := by
  apply Form.ext
  intro x hx
  rw [ZigZag.twForm_apply, coefficientFormMap_apply]
  apply ext2Face
  intro i j
  apply Coef.toPoly_injective
  have hp : ptOf x ∈ Omega := ptOf_mem hx
  set k : SL(3, ℤ) := h' * h⁻¹ with hk
  have hRHS : Coef.toPoly ((rhoOfSL n h⁻¹).compContinuousAlternatingMap
      (((faceSeriesK N k n f hn : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x)
        ![Pi.single i 1, Pi.single j 1]) =
      rho (realMat h⁻¹) (seriesFormK false (CuspData.ofSL k) (gammaN N) n f (ptOf x)
        i.castSucc j.castSucc) := by
    show Coef.toPoly (rhoOfSL n h⁻¹ (((faceSeriesK N k n f hn : Form (F := Coef n) faceSet 2) :
      RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1])) = _
    rw [toPoly_rhoOfSL]
    congr 1
    exact congrArg Coef.toPoly (faceForm_basis (gammaNPlaneData N) (inclP N)
      (fun g => gammaNPlaneData_plm N g)
      (planeEisensteinAtComponents false (CuspData.ofSL k) (gammaN N) (leviGroup N) n f hn
        (leviInCusp_gammaN N k)) hx i j)
  rw [hRHS, seriesFormK_false_eq N n f hn k hp]
  rw [toPoly_cuspFaceForm_basis N h _ hx i j]
  have hd : HasFDerivAt (cuspPt h)
      ((fderiv ℝ (planeAct (realMat h⁻¹)) (ptOf x)).comp ptCLM) x :=
    (differentiableAt_planeAct (det_realMat h⁻¹) hp).hasFDerivAt.comp x (hasFDerivAt_ptOf x)
  have hw : ∀ k' : Fin 4, fderiv ℝ (cuspPt h) x (Pi.single k' 1) =
      fderiv ℝ (planeAct (realMat h⁻¹)) (ptOf x) (Pi.single k'.castSucc 1) := by
    intro k'
    rw [hd.fderiv]
    simp [ptCLM_single]
  simp_rw [hw]
  have hΩ : cuspPt h x ∈ Omega := planeAct_mem (det_realMat h⁻¹) hp
  have hcomp : ∀ a b : Fin 5,
      Coef.toPoly ((planeEisensteinAtComponents false (CuspData.ofSL h') (gammaN N) (leviGroup N) n
        f hn (leviInCusp_gammaN N h')).comp (cuspPt h x) a b) =
      rho (realMat h')⁻¹ (formPullback (planeAct (realMat h')) (seriesForm (gammaN N) n f)
        (cuspPt h x) a b) := by
    intro a b
    show seriesFormK false (CuspData.ofSL h') (gammaN N) n f (cuspPt h x) a b = _
    rw [seriesFormK_false_eq N n f hn h' hΩ]
  simp_rw [hcomp]
  have hrho : ∀ (c : ℂ) (q : MvPolynomial (Fin 3) ℂ), rho (realMat h')⁻¹ (C c * q) =
      C c * rho (realMat h')⁻¹ q := fun c q => rho_C_mul _ _ _
  simp_rw [← hrho]
  simp_rw [← rho_sum]
  -- the sum is the pullback of the pullback
  have hS : (∑ a : Fin 5, ∑ b : Fin 5,
      C (((fderiv ℝ (planeAct (realMat h⁻¹)) (ptOf x) (Pi.single i.castSucc 1) a *
        fderiv ℝ (planeAct (realMat h⁻¹)) (ptOf x) (Pi.single j.castSucc 1) b : ℝ) : ℂ)) *
        formPullback (planeAct (realMat h')) (seriesForm (gammaN N) n f) (cuspPt h x) a b) =
      formPullback (planeAct (realMat k)) (seriesForm (gammaN N) n f) (ptOf x)
        i.castSucc j.castSucc := by
    have e1 := formPullback_comp (planeAct (realMat h⁻¹)) (planeAct (realMat h'))
      (seriesForm (gammaN N) n f) (ptOf x) (differentiableAt_planeAct (det_realMat _) hp)
      (differentiableAt_planeAct (det_realMat _) hΩ) i.castSucc j.castSucc
    have hev : planeAct (realMat k) =ᶠ[nhds (ptOf x)]
        (planeAct (realMat h') ∘ planeAct (realMat h⁻¹)) :=
      Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hp) fun z hz => by
        rw [hk, realMat_mul]
        exact planeAct_mul (det_realMat _) hz
    rw [formPullback_congr _ hev, e1]
    rfl
  rw [hS]
  -- the matrices
  have hmat : realMat h⁻¹ * (realMat k)⁻¹ = (realMat h')⁻¹ := by
    have hu : IsUnit (realMat h⁻¹).det := by rw [det_realMat]; exact isUnit_one
    rw [hk, realMat_mul, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mul]
  rw [rho_mul, hmat]

end TernaryPeriodPolynomials.Argument.EisensteinClass
