module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBridgeA

@[expose] public section


/-!
# Pointwise bridge: the face pairing of a summand is a twisted frame coefficient

Paper: Appendix C.5.

`fPull_gx`: for `det M = 1` and a face point `x`, the `jFace`-pullback of the summand `S_h(M)` on `(e_p, e_q)` is
`ρ(g_x) · ω̃_h(M g_x)(V_p, V_q)`, the frame coefficient of the seed at `M g_x` on the Maurer-Cartan directions.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed (gramChart gramCurve chartTangent)


section Pointwise

open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed (frameCoefficient frameValue)

theorem chartTangent_gx {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.det = 1) {x : Face} (hx : x ∈ faceSet)
    (e : Face) :
    chartTangent (M * gx x) (Vgx x e) = fderiv ℝ (planeAct (M * gx x)) basePt (chartTangent 1 (Vgx x e)) :=
  chartTangent_transport (kx_zero hx e) (hasDerivAt_kx hx e) (det_kx_eventually hx e)
    (by rw [Matrix.det_mul, hM, det_gx hx]; simp)

/-- **Pointwise form of the bridge**: the face pairing of the summand `S_h(M)` at `x` is the frame coefficient at
`M g_x` of the Maurer-Cartan directions, twisted by `ρ(g_x)`. -/
theorem fPull_gx (n : ℕ) (h : ℂ → ℂ) {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.det = 1) {x : Face}
    (hx : x ∈ faceSet) (p q : Fin 4) :
    fPull jFace (fun y a b => summandPoly n h M y a b) x p q =
      rho (gx x) (frameCoefficient (seedForm n h) (M * gx x) (Vgx x (Pi.single p 1))
        (Vgx x (Pi.single q 1))) := by
  set g := gx x with hgdef
  have hg : g.det = 1 := det_gx hx
  have hMg : (M * g).det = 1 := by rw [Matrix.det_mul, hM, hg]; simp
  have hy : jFace x = planeAct g basePt := jFace_eq_planeAct_gx hx
  have hjd : DifferentiableAt ℝ jFace x := differentiableAt_jFace hx
  have hyΩ : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  have hpd : DifferentiableAt ℝ (planeAct M) (jFace x) := differentiableAt_planeAct hM hyΩ
  have e : fPull jFace (fun y a b => formPullback (planeAct M) (seedForm n h) y a b) x p q =
      fPull (planeAct M ∘ jFace) (seedForm n h) x p q :=
    (fPull_comp jFace (planeAct M) (seedForm n h) x hjd hpd p q).symm
  have h1 : fPull jFace (fun y a b => summandPoly n h M y a b) x p q =
      rho M⁻¹ (fPull jFace (fun y a b => formPullback (planeAct M) (seedForm n h) y a b) x p q) := by
    simp only [summandPoly]
    exact fPull_rho M⁻¹ jFace (fun y a b => formPullback (planeAct M) (seedForm n h) y a b) x p q
  have hgram : IsGram ((M * g) * (M * g).transpose) := isGram_self_transpose hMg
  have hpt : (planeAct M ∘ jFace) x = gramChart ((M * g) * (M * g).transpose) := by
    rw [Function.comp_apply, hy, ← planeAct_mul hg basePt_mem, gramChart_eq_planePoint hgram]
    unfold planeAct
    rw [planeGram_basePt, Matrix.mul_one]
  have hD : ∀ (k : Fin 4) (a : Fin 5), fderiv ℝ (planeAct M ∘ jFace) x (Pi.single k 1) a =
      chartTangent (M * g) (Vgx x (Pi.single k 1)) a := by
    intro k a
    rw [fderiv_comp x hpd hjd, ContinuousLinearMap.comp_apply, dj_eq_transport hx, hy,
      fderiv_planeAct_comp hM hg, chartTangent_gx hM hx]
  have h2 : fPull (planeAct M ∘ jFace) (seedForm n h) x p q =
      frameValue (seedForm n h) (M * g) (Vgx x (Pi.single p 1)) (Vgx x (Pi.single q 1)) := by
    unfold fPull frameValue
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hD p a, hD q b, hpt]
  have hinv : g * (M * g)⁻¹ = M⁻¹ := by
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (unit_det_gx hx), Matrix.one_mul]
  rw [h1, e, h2]
  unfold frameCoefficient
  rw [← TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed.rho_mul, hinv]

end Pointwise


end TernaryPeriodPolynomials.Argument.EisensteinClass
