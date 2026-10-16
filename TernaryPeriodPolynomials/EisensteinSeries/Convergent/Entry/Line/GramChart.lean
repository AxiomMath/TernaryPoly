module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.GramDomain
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.SeedFrame

@[expose] public section


/-!
# The line-face chart on the Gram cone

The open set `lineDomain` on which the line-face chart `lineChart` (the coordinates `w = G_{1,{2,3}} (G_{{2,3},{2,3}})⁻¹`,
`τ`, `λ`) is given by formulas with positive denominators, the smoothness of its five components, the membership of
Gram matrices of invertible matrices (`gram_mem_lineDomain`), and the identification of the tangent coordinates
`lineTangent g V` with the Fréchet derivative of the chart in the Gram direction `g (V + Vᵀ) gᵀ`
(`lineTangent_eq_fderiv`).  Mirror of `GramDomain` for the line face.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The determinant of the trailing `2 × 2` block (for a possibly nonsymmetric matrix). -/
def lineD (G : Mat3) : ℝ := G 1 1 * G 2 2 - G 1 2 * G 2 1

/-- The square of the line normal height, `λ² = G₀₀ - w · G_{0,{1,2}}`. -/
def lineLam2 (G : Mat3) : ℝ :=
  G 0 0 - ((G 0 1 * G 2 2 - G 0 2 * G 2 1) * G 0 1 + (G 0 2 * G 1 1 - G 0 1 * G 1 2) * G 0 2) / lineD G

/-- The open set of matrices on which the line chart is defined with positive denominators. -/
def lineDomain : Set Mat3 := {G | 0 < G 2 2 ∧ 0 < lineD G ∧ 0 < lineLam2 G}

theorem lineChart_eq (G : Mat3) : lineChart G = ![(G 0 1 * G 2 2 - G 0 2 * G 2 1) / lineD G,
    (G 0 2 * G 1 1 - G 0 1 * G 1 2) / lineD G, G 1 2 / G 2 2, Real.sqrt (lineD G) / G 2 2,
    Real.sqrt (lineLam2 G)] := rfl

theorem continuousOn_lineLam2 : ContinuousOn lineLam2 {G : Mat3 | 0 < lineD G} := by
  intro G hG
  apply ContinuousAt.continuousWithinAt
  have hD : lineD G ≠ 0 := (show 0 < lineD G from hG).ne'
  unfold lineLam2 lineD at *
  have e : ∀ i j, Continuous (fun G : Mat3 => G i j) := fun i j => by fun_prop
  refine ContinuousAt.sub (e 0 0).continuousAt (ContinuousAt.div ?_ ?_ hD)
  · fun_prop
  · fun_prop

theorem continuous_lineD : Continuous lineD := by unfold lineD; fun_prop

theorem continuous_entry3 (i j : Fin 3) : Continuous (fun G : Mat3 => G i j) := by fun_prop

theorem isOpen_lineDomain : IsOpen lineDomain := by
  have h1 : IsOpen {G : Mat3 | 0 < G 2 2} := isOpen_lt continuous_const (continuous_entry3 2 2)
  have h2 : IsOpen {G : Mat3 | 0 < lineD G} := isOpen_lt continuous_const continuous_lineD
  have h3 := continuousOn_lineLam2.isOpen_inter_preimage h2 (isOpen_Ioi (a := (0 : ℝ)))
  have h4 := h1.inter h3
  convert h4 using 1
  ext G
  simp [lineDomain]

theorem contDiff_lineD : ContDiff ℝ ⊤ lineD := by unfold lineD; fun_prop

theorem contDiffOn_lineLam2 : ContDiffOn ℝ ⊤ lineLam2 lineDomain := by
  unfold lineLam2
  have e : ∀ i j : Fin 3, ContDiff ℝ ⊤ (fun G : Mat3 => G i j) := fun i j => by fun_prop
  refine (e 0 0).contDiffOn.sub (ContDiffOn.div ?_ contDiff_lineD.contDiffOn (fun G hG => hG.2.1.ne'))
  fun_prop

theorem contDiffOn_lineChart (a : Fin 5) :
    ContDiffOn ℝ ⊤ (fun G : Mat3 => lineChart G a) lineDomain := by
  have e : ∀ i j : Fin 3, ContDiff ℝ ⊤ (fun G : Mat3 => G i j) := fun i j => by fun_prop
  have hD : ∀ G ∈ lineDomain, lineD G ≠ 0 := fun G hG => hG.2.1.ne'
  have h22 : ∀ G ∈ lineDomain, G 2 2 ≠ 0 := fun G hG => hG.1.ne'
  fin_cases a
  · simp only [lineChart_eq]
    refine ContDiffOn.div ?_ contDiff_lineD.contDiffOn hD
    fun_prop
  · simp only [lineChart_eq]
    refine ContDiffOn.div ?_ contDiff_lineD.contDiffOn hD
    fun_prop
  · simp only [lineChart_eq]
    exact (e 1 2).contDiffOn.div (e 2 2).contDiffOn h22
  · simp only [lineChart_eq]
    exact (contDiff_lineD.contDiffOn.sqrt hD).div (e 2 2).contDiffOn h22
  · simp only [lineChart_eq]
    exact contDiffOn_lineLam2.sqrt (fun G hG => hG.2.2.ne')

theorem lineLam2_eq_det (G : Mat3) (hG : G.IsSymm) (hD : lineD G ≠ 0) : lineLam2 G = G.det / lineD G := by
  have h10 : G 1 0 = G 0 1 := hG.apply 0 1
  have h20 : G 2 0 = G 0 2 := hG.apply 0 2
  have h21 : G 2 1 = G 1 2 := hG.apply 1 2
  rw [eq_div_iff hD]
  unfold lineLam2
  rw [sub_mul, div_mul_cancel₀ _ hD, Matrix.det_fin_three, h10, h20, h21]
  unfold lineD
  rw [h21]
  ring

theorem gram_mem_lineDomain (g : Mat3) (hg : g.det ≠ 0) : g * g.transpose ∈ lineDomain := by
  have h22 := gram_pos_22 g hg
  have hm := gram_minor_pos g hg
  have hsym := gram_isSymm g
  have hD : 0 < lineD (g * g.transpose) := by
    unfold lineD
    rw [hsym.apply 1 2]
    nlinarith [hm]
  refine ⟨h22, hD, ?_⟩
  rw [lineLam2_eq_det _ hsym hD.ne', Matrix.det_mul, Matrix.det_transpose]
  exact div_pos (mul_self_pos.mpr hg) hD

theorem hasFDerivAt_lineChart {G : Mat3} (hG : G ∈ lineDomain) (a : Fin 5) :
    HasFDerivAt (fun G : Mat3 => lineChart G a) (fderiv ℝ (fun G : Mat3 => lineChart G a) G) G :=
  (((contDiffOn_lineChart a).differentiableOn (by simp)).differentiableAt
    (isOpen_lineDomain.mem_nhds hG)).hasFDerivAt

theorem hasDerivAt_gramCurve_mat (g V : Mat3) :
    HasDerivAt (fun ε : ℝ => gramCurve g V ε) (g * (V + V.transpose) * g.transpose) 0 :=
  hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => hasDerivAt_gramCurve g V i j

/-- The line-chart tangent `dL_g V` is the Fréchet derivative of the line chart in the Gram direction
`g (V + Vᵀ) gᵀ`. -/
theorem lineTangent_eq_fderiv (g V : Mat3) (hg : g.det ≠ 0) (a : Fin 5) :
    lineTangent g V a = fderiv ℝ (fun G : Mat3 => lineChart G a) (g * g.transpose)
      (g * (V + V.transpose) * g.transpose) := by
  have hmem := gram_mem_lineDomain g hg
  have h0 : gramCurve g V 0 = g * g.transpose := gramCurve_zero g V
  have hF : HasFDerivAt (fun G : Mat3 => lineChart G a)
      (fderiv ℝ (fun G : Mat3 => lineChart G a) (g * g.transpose)) (gramCurve g V 0) := by
    rw [h0]; exact hasFDerivAt_lineChart hmem a
  have h1 := hF.comp_hasDerivAt (0 : ℝ) (hasDerivAt_gramCurve_mat g V)
  exact h1.deriv

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
