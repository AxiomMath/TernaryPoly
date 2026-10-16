module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KTangent

@[expose] public section


/-!
# The Maurer-Cartan curve of the frame matrix and the transport of the face tangents

Paper: Appendix C.5.

`kx x e ε = g_x⁻¹ g_{x+εe}` is a curve of determinant-one matrices through `1` with velocity `V_e(x) = g_x⁻¹ ∂_e g_x`;
`dj_eq_transport`: `d jFace x (e) = D(planeAct g_x)(chartTangent 1 V_e(x))`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed (gramChart gramCurve chartTangent)


section Bridge

open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed (frameCoefficient frameValue)

theorem hasDerivAt_jFace_line_at {x : Face} (hx : x ∈ faceSet) (e : Face) :
    HasDerivAt (fun ε : ℝ => jFace (x + ε • e)) (fderiv ℝ jFace x e) 0 := by
  have hd : HasFDerivAt jFace (fderiv ℝ jFace x) (x + (0 : ℝ) • e) := by
    simpa using (differentiableAt_jFace hx).hasFDerivAt
  have hl : HasDerivAt (fun ε : ℝ => x + ε • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  exact hd.comp_hasDerivAt (0 : ℝ) hl

/-- The curve `k(ε) = g_x⁻¹ g_{x + ε e}` of matrices of determinant one through `1`. -/
def kx (x e : Face) (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (gx x)⁻¹ * gx (x + ε • e)

theorem unit_det_gx {x : Face} (hx : x ∈ faceSet) : IsUnit (gx x).det := by
  rw [det_gx hx]; exact isUnit_one

theorem kx_zero {x : Face} (hx : x ∈ faceSet) (e : Face) : kx x e 0 = 1 := by
  simp [kx, Matrix.nonsing_inv_mul _ (unit_det_gx hx)]

theorem hasDerivAt_kx {x : Face} (hx : x ∈ faceSet) (e : Face) (i j : Fin 3) :
    HasDerivAt (fun ε => kx x e ε i j) (Vgx x e i j) 0 := by
  have hc : ∀ i j, HasDerivAt (fun _ : ℝ => (gx x)⁻¹ i j) ((0 : Matrix (Fin 3) (Fin 3) ℝ) i j) 0 :=
    fun i j => by simpa using hasDerivAt_const (0 : ℝ) ((gx x)⁻¹ i j)
  have := hasDerivAt_mat_mul (A := fun _ => (gx x)⁻¹) (B := fun ε => gx (x + ε • e)) hc
    (hasDerivAt_gx_entry hx e) i j
  simpa [kx, Vgx] using this

theorem eventually_mem_face {x : Face} (hx : x ∈ faceSet) (e : Face) :
    ∀ᶠ ε in nhds (0 : ℝ), x + ε • e ∈ faceSet := by
  have hopen : IsOpen {ε : ℝ | x + ε • e ∈ faceSet} :=
    isOpen_faceSet.preimage (by fun_prop)
  exact hopen.mem_nhds (by simpa using hx)

theorem det_kx_eventually {x : Face} (hx : x ∈ faceSet) (e : Face) :
    ∀ᶠ ε in nhds (0 : ℝ), (kx x e ε).det = 1 := by
  filter_upwards [eventually_mem_face hx e] with ε hε
  unfold kx
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, det_gx hx, det_gx hε]
  simp

/-- **Transport of the face tangents**: `d jFace x (e) = D(planeAct g_x)(chartTangent 1 V_e(x))`. -/
theorem dj_eq_transport {x : Face} (hx : x ∈ faceSet) (e : Face) :
    fderiv ℝ jFace x e = fderiv ℝ (planeAct (gx x)) basePt (chartTangent 1 (Vgx x e)) := by
  have h1 := hasDerivAt_jFace_line_at hx e
  have h2 := hasDerivAt_planeAct_chain (k := kx x e) (K := Vgx x e) (kx_zero hx e)
    (hasDerivAt_kx hx e) (det_kx_eventually hx e) (det_gx hx)
  have hev : (fun ε => jFace (x + ε • e)) =ᶠ[nhds 0]
      fun ε => planeAct (gx x) (planeAct (kx x e ε) basePt) := by
    filter_upwards [det_kx_eventually hx e, eventually_mem_face hx e] with ε hε hε'
    have hmul : gx x * kx x e ε = gx (x + ε • e) := by
      unfold kx; rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (unit_det_gx hx), Matrix.one_mul]
    rw [jFace_eq_planeAct_gx hε', ← planeAct_mul hε basePt_mem, hmul]
  exact h1.unique (h2.congr_of_eventuallyEq hev)

theorem fderiv_planeAct_comp {M g : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.det = 1) (hg : g.det = 1)
    (v : Fin 5 → ℝ) :
    fderiv ℝ (planeAct M) (planeAct g basePt) (fderiv ℝ (planeAct g) basePt v) =
      fderiv ℝ (planeAct (M * g)) basePt v := by
  have hev : planeAct (M * g) =ᶠ[nhds basePt] planeAct M ∘ planeAct g :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds basePt_mem) fun y hy => planeAct_mul hg hy
  rw [hev.fderiv_eq, fderiv_comp basePt (differentiableAt_planeAct hM (planeAct_mem hg basePt_mem))
    (differentiableAt_planeAct hg basePt_mem)]
  rfl

end Bridge


end TernaryPeriodPolynomials.Argument.EisensteinClass
