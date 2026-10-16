module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KGx
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KGramD

@[expose] public section


/-!
# Transport of the face tangents: `d jFace (e) = D(planeAct g_x)(chartTangent 1 V_e)`

Paper: Appendix C.5.

For a curve `k(ε)` of matrices of determinant one with `k(0) = 1` and velocity `K`, the chart tangent of `K` at
`g · SO(3)` is `D(planeAct g)` applied to the chart tangent of `K` at the base point
(`chartTangent_transport`). The face directions `e` are the velocities of the curves
`k(ε) = g_x⁻¹ g_{x+εe}`, so (`dj_eq_transport`)

  `d jFace x (e) = D(planeAct g_x) (chartTangent 1 V_e(x))`,   `V_e(x) = g_x⁻¹ ∂_e g_x`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed (gramChart gramCurve chartTangent)

section Dgc

/-- The derivative of the Gram chart at a matrix. -/
def Dgc (G₀ : Matrix (Fin 3) (Fin 3) ℝ) : (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 5 → ℝ) :=
  fderiv ℝ (fun z : Fin 3 → Fin 3 → ℝ => gramChart (matOfFun z)) (matToFun G₀)

theorem isGram_self_transpose {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) :
    IsGram (g * g.transpose) := by
  have := (planeGram_isGram basePt_mem).conj hg
  simpa [planeGram_basePt] using this

theorem gramSchur_det_pos {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G) :
    0 < (G 0 0 - G 0 2 * G 0 2 / G 2 2) * (G 1 1 - G 1 2 * G 1 2 / G 2 2) -
      (G 0 1 - G 0 2 * G 1 2 / G 2 2) * (G 1 0 - G 1 2 * G 0 2 / G 2 2) := by
  have h := gramSchur_det hG
  rw [Matrix.det_fin_two] at h
  simp only [gramSchur, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h
  rw [h]
  exact one_div_pos.2 hG.s_pos

theorem differentiableAt_gramChartF {G₀ : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G₀) :
    DifferentiableAt ℝ (fun z : Fin 3 → Fin 3 → ℝ => gramChart (matOfFun z)) (matToFun G₀) := by
  have hF : ∀ i j, ContDiffAt ℝ ⊤ (fun z : Fin 3 → Fin 3 → ℝ => matOfFun z i j) (matToFun G₀) := by
    intro i j
    exact ((contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 3 → ℝ) i)).contDiffAt
  exact (contDiffAt_gramChart_comp (F := fun z : Fin 3 → Fin 3 → ℝ => matOfFun z) hF hG.s_pos
    hG.schur_pos (gramSchur_det_pos hG)).differentiableAt (by simp)

theorem hasDerivAt_gramChart_curve {G : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {S : Matrix (Fin 3) (Fin 3) ℝ}
    (hG0 : IsGram (G 0)) (hder : ∀ i j, HasDerivAt (fun ε => G ε i j) (S i j) 0) :
    HasDerivAt (fun ε => gramChart (G ε)) (Dgc (G 0) (matToFun S)) 0 := by
  have hd := (differentiableAt_gramChartF hG0).hasFDerivAt
  have hc : HasDerivAt (fun ε => matToFun (G ε)) (matToFun S) 0 := by
    rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j; exact hder i j
  exact hd.comp_hasDerivAt (0 : ℝ) hc

theorem chartTangent_eq_Dgc (g V : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det = 1) (a : Fin 5) :
    chartTangent g V a = Dgc (g * g.transpose) (matToFun (g * (V + V.transpose) * g.transpose)) a := by
  have e0 : gramCurve g V 0 = g * g.transpose := by simp [gramCurve]
  have h := hasDerivAt_gramChart_curve (G := gramCurve g V) (S := g * (V + V.transpose) * g.transpose)
    (by rw [e0]; exact isGram_self_transpose hg) (hasDerivAt_gram_V g V)
  rw [e0] at h
  have := (hasDerivAt_pi.1 h) a
  unfold chartTangent
  exact this.deriv

end Dgc

section Curves

variable {k : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {K : Matrix (Fin 3) (Fin 3) ℝ}

theorem hasDerivAt_gram_k (hk0 : k 0 = 1) (hk : ∀ i j, HasDerivAt (fun ε => k ε i j) (K i j) 0)
    (g : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    HasDerivAt (fun ε => (g * (k ε * (k ε).transpose) * g.transpose) i j)
      ((g * (K + K.transpose) * g.transpose) i j) 0 := by
  have hkt : ∀ i j, HasDerivAt (fun ε => (k ε).transpose i j) (K.transpose i j) 0 :=
    fun i j => by simpa using hk j i
  have hG : ∀ i j, HasDerivAt (fun ε => (k ε * (k ε).transpose) i j)
      ((K + K.transpose) i j) 0 := by
    intro i j
    have := hasDerivAt_mat_mul (A := k) (B := fun ε => (k ε).transpose) hk hkt i j
    simpa [hk0] using this
  exact hasDerivAt_conj hG g i j

theorem gramChart_k_eq {ε : ℝ} (hε : (k ε).det = 1) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) :
    gramChart (g * (k ε * (k ε).transpose) * g.transpose) = planeAct g (planeAct (k ε) basePt) := by
  have h1 : IsGram (k ε * (k ε).transpose) := isGram_self_transpose hε
  have e : planeAct (k ε) basePt = planePoint (k ε * (k ε).transpose) := by
    unfold planeAct; rw [planeGram_basePt, Matrix.mul_one]
  rw [e]
  unfold planeAct
  rw [planeGram_planePoint h1]
  exact gramChart_eq_planePoint (h1.conj hg)

theorem hasDerivAt_planeAct_curve (hk0 : k 0 = 1)
    (hk : ∀ i j, HasDerivAt (fun ε => k ε i j) (K i j) 0)
    (hdet : ∀ᶠ ε in nhds (0 : ℝ), (k ε).det = 1) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) :
    HasDerivAt (fun ε => planeAct g (planeAct (k ε) basePt))
      (Dgc (g * g.transpose) (matToFun (g * (K + K.transpose) * g.transpose))) 0 := by
  have e0 : g * (k 0 * (k 0).transpose) * g.transpose = g * g.transpose := by
    simp [hk0]
  have h := hasDerivAt_gramChart_curve (G := fun ε => g * (k ε * (k ε).transpose) * g.transpose)
    (S := g * (K + K.transpose) * g.transpose) (by rw [e0]; exact isGram_self_transpose hg)
    (hasDerivAt_gram_k hk0 hk g)
  rw [e0] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hdet] with ε hε
  exact (gramChart_k_eq hε hg).symm

theorem chartTangent_one_eq (hg : (1 : Matrix (Fin 3) (Fin 3) ℝ).det = 1 := by simp) :
    chartTangent 1 K = Dgc 1 (matToFun (K + K.transpose)) := by
  funext a
  have := chartTangent_eq_Dgc 1 K hg a
  simpa using this

theorem hasDerivAt_planeAct_chain (hk0 : k 0 = 1)
    (hk : ∀ i j, HasDerivAt (fun ε => k ε i j) (K i j) 0)
    (hdet : ∀ᶠ ε in nhds (0 : ℝ), (k ε).det = 1) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) :
    HasDerivAt (fun ε => planeAct g (planeAct (k ε) basePt))
      (fderiv ℝ (planeAct g) basePt (chartTangent 1 K)) 0 := by
  have h1' := hasDerivAt_planeAct_curve hk0 hk hdet (g := 1) (by simp)
  have e1 : (fun ε => planeAct 1 (planeAct (k ε) basePt)) =ᶠ[nhds 0] fun ε => planeAct (k ε) basePt := by
    filter_upwards [hdet] with ε hε
    exact planeAct_one (planeAct_mem hε basePt_mem)
  have h2 : HasDerivAt (fun ε => planeAct (k ε) basePt)
      (Dgc (1 * (1 : Matrix (Fin 3) (Fin 3) ℝ).transpose)
        (matToFun (1 * (K + K.transpose) * (1 : Matrix (Fin 3) (Fin 3) ℝ).transpose))) 0 :=
    h1'.congr_of_eventuallyEq e1.symm
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h2
  have hd : HasFDerivAt (planeAct g) (fderiv ℝ (planeAct g) basePt)
      ((fun ε => planeAct (k ε) basePt) 0) := by
    have : (fun ε => planeAct (k ε) basePt) 0 = basePt := by simp [hk0, planeAct_one basePt_mem]
    rw [this]
    exact (differentiableAt_planeAct hg basePt_mem).hasFDerivAt
  have h3 := hd.comp_hasDerivAt (0 : ℝ) h2
  rw [chartTangent_one_eq]
  exact h3

theorem chartTangent_transport (hk0 : k 0 = 1) (hk : ∀ i j, HasDerivAt (fun ε => k ε i j) (K i j) 0)
    (hdet : ∀ᶠ ε in nhds (0 : ℝ), (k ε).det = 1) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) :
    chartTangent g K = fderiv ℝ (planeAct g) basePt (chartTangent 1 K) := by
  have h1 := hasDerivAt_planeAct_curve hk0 hk hdet hg
  have h3 := hasDerivAt_planeAct_chain hk0 hk hdet hg
  have h4 := h1.unique h3
  funext a
  rw [chartTangent_eq_Dgc g K hg a, h4]

end Curves

end TernaryPeriodPolynomials.Argument.EisensteinClass
