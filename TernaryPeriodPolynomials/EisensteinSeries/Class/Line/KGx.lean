module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KEntry

@[expose] public section


/-!
# The frame matrix `g_x` of a face point

Paper: Appendix C.5.

For a point `x` of the face, `g_x = rt (planePinv (ptOf x))` is an upper triangular matrix of determinant one
(the anti-transpose of the inverse of the Iwasawa factor of `ptOf x`) with
`jFace x = planeAct g_x (1 · SO(3))` (`jFace_eq_planeAct_gx`, from the equivariance of `ȷ`). Its entries are smooth in
`x` and the Maurer-Cartan matrices `V_e(x) = g_x⁻¹ ∂_e g_x` are the Lie algebra elements representing the
tangent vectors `d jFace (e)` (see `LineKTangent`).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial ComplexConjugate
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinDual
  TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
  TernaryPeriodPolynomials.Argument.SeedC3.Psi

section Gx

/-- The frame matrix of a face point. -/
def gx (x : Face) : Matrix (Fin 3) (Fin 3) ℝ := rt (planePinv (ptOf x))

theorem det_gx {x : Face} (hx : x ∈ faceSet) : (gx x).det = 1 := by
  unfold gx
  rw [det_rt, det_planePinv (ptOf_mem hx)]

theorem planeAct_planeP_basePt {p : Fin 5 → ℝ} (hp : p ∈ Omega) : planeAct (planeP p) basePt = p := by
  unfold planeAct
  rw [planeGram_basePt, Matrix.mul_one, planeP_mul_transpose hp, planePoint_planeGram hp]

theorem jPlane_basePt : jPlane basePt = basePt := by
  unfold jPlane jGram
  rw [planeGram_basePt, inv_one, rt_one, planePoint_one]

/-- **`jFace x = g_x · (1 · SO(3))`.** -/
theorem jFace_eq_planeAct_gx {x : Face} (hx : x ∈ faceSet) : jFace x = planeAct (gx x) basePt := by
  have hp := ptOf_mem hx
  have hinv : (planeP (ptOf x))⁻¹ = planePinv (ptOf x) :=
    Matrix.inv_eq_right_inv (planeP_mul_planePinv hp)
  calc jFace x = jPlane (planeAct (planeP (ptOf x)) basePt) := by
        unfold jFace; rw [planeAct_planeP_basePt hp]
    _ = planeAct (rt (planeP (ptOf x))⁻¹) (jPlane basePt) :=
        jPlane_equivariant_real (det_planeP hp) basePt_mem
    _ = planeAct (gx x) basePt := by
        rw [jPlane_basePt, hinv]; rfl

theorem contDiffAt_ptOf (x : Face) : ContDiffAt ℝ ⊤ ptOf x := by
  rw [ptOf_eq]
  exact ptCLM.contDiff.contDiffAt.add contDiffAt_const

theorem contDiffAt_gx_entry {x : Face} (hx : x ∈ faceSet) (i j : Fin 3) :
    ContDiffAt ℝ ⊤ (fun y : Face => gx y i j) x :=
  (contDiffAt_planePinv_entry (ptOf_mem hx) j.rev i.rev).comp x (contDiffAt_ptOf x)

theorem differentiableAt_gx_entry {x : Face} (hx : x ∈ faceSet) (i j : Fin 3) :
    DifferentiableAt ℝ (fun y : Face => gx y i j) x :=
  (contDiffAt_gx_entry hx i j).differentiableAt (by simp)

/-- The derivative of the frame matrix along a face direction. -/
def dgx (x : Face) (e : Face) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => fderiv ℝ (fun y : Face => gx y i j) x e

/-- The Maurer-Cartan matrix `V_e(x) = g_x⁻¹ ∂_e g_x`. -/
def Vgx (x : Face) (e : Face) : Matrix (Fin 3) (Fin 3) ℝ := (gx x)⁻¹ * dgx x e

theorem hasDerivAt_gx_entry {x : Face} (hx : x ∈ faceSet) (e : Face) (i j : Fin 3) :
    HasDerivAt (fun ε : ℝ => gx (x + ε • e) i j) (dgx x e i j) 0 := by
  have hd : HasFDerivAt (fun y : Face => gx y i j) (fderiv ℝ (fun y : Face => gx y i j) x)
      (x + (0 : ℝ) • e) := by
    simpa using (differentiableAt_gx_entry hx i j).hasFDerivAt
  have hl : HasDerivAt (fun ε : ℝ => x + ε • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  exact hd.comp_hasDerivAt (0 : ℝ) hl

end Gx

end TernaryPeriodPolynomials.Argument.EisensteinClass
