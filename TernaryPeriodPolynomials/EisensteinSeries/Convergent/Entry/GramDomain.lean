module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Seed
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RealIwasawa
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityLevi

@[expose] public section


/-!
# The plane chart on the Gram cone

The open set `gramDomain` of matrices on which the plane horospherical chart `gramChart` is defined by
formulas with positive denominators, the smoothness of the five chart functions on it
(`contDiffOn_gramChart`), and the identification of their Fréchet derivative on symmetric directions with
`planeTangent` (`fderiv_gramChart_apply`).  This lets the affine simplices of the (convex) cone of Gram matrices
be used with the generic cup/triangle bridge.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The open set of matrices on which the plane chart is defined and smooth. -/
def gramDomain : Set Mat3 :=
  {G | 0 < G 2 2 ∧ 0 < gramSchur G 1 1 ∧ 0 < (gramSchur G).det}

theorem entry_continuous (i j : Fin 3) : Continuous (fun G : Mat3 => G i j) := by fun_prop

theorem gramSchur_continuousOn (i j : Fin 2) :
    ContinuousOn (fun G : Mat3 => gramSchur G i j) {G | 0 < G 2 2} := by
  intro G hG
  have h22 : G 2 2 ≠ 0 := (show 0 < G 2 2 from hG).ne'
  fin_cases i <;> fin_cases j <;>
    simp only [gramSchur, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
    (apply ContinuousAt.continuousWithinAt
     exact (entry_continuous _ _).continuousAt.sub (((entry_continuous _ _).continuousAt.mul
       (entry_continuous _ _).continuousAt).div (entry_continuous 2 2).continuousAt h22))

theorem isOpen_gramDomain : IsOpen gramDomain := by
  have hS : IsOpen {G : Mat3 | 0 < G 2 2} := isOpen_lt continuous_const (by fun_prop)
  have hf : ContinuousOn (fun G : Mat3 => (gramSchur G 1 1, (gramSchur G).det)) {G | 0 < G 2 2} := by
    refine ContinuousOn.prodMk (gramSchur_continuousOn 1 1) ?_
    simp only [Matrix.det_fin_two]
    exact ((gramSchur_continuousOn 0 0).mul (gramSchur_continuousOn 1 1)).sub
      ((gramSchur_continuousOn 0 1).mul (gramSchur_continuousOn 1 0))
  have ht : IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)
  have := hf.isOpen_inter_preimage hS ht
  convert this using 1
  ext G
  simp [gramDomain]

theorem gramChart_re_tau (G : Mat3) :
    (gramPlaneTau G).re = gramSchur G 0 1 / gramSchur G 1 1 := by
  simp [gramPlaneTau]

theorem gramChart_im_tau (G : Mat3) :
    (gramPlaneTau G).im = Real.sqrt (gramSchur G).det / gramSchur G 1 1 := by
  simp [gramPlaneTau]

theorem contDiff_entry (i j : Fin 3) : ContDiff ℝ ⊤ (fun G : Mat3 => G i j) := by fun_prop

theorem contDiffOn_gramSchur (i j : Fin 2) :
    ContDiffOn ℝ ⊤ (fun G : Mat3 => gramSchur G i j) gramDomain := by
  have h22 : ∀ G ∈ gramDomain, G 2 2 ≠ 0 := fun G hG => hG.1.ne'
  fin_cases i <;> fin_cases j <;>
    simp only [gramSchur, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
    exact (contDiff_entry _ _).contDiffOn.sub
      ((((contDiff_entry _ _).mul (contDiff_entry _ _)).contDiffOn).div (contDiff_entry 2 2).contDiffOn h22)

theorem contDiffOn_gramChart (a : Fin 5) :
    ContDiffOn ℝ ⊤ (fun G : Mat3 => gramChart G a) gramDomain := by
  have h22 : ∀ G ∈ gramDomain, G 2 2 ≠ 0 := fun G hG => hG.1.ne'
  have hs11 : ∀ G ∈ gramDomain, gramSchur G 1 1 ≠ 0 := fun G hG => hG.2.1.ne'
  have hdet : ContDiffOn ℝ ⊤ (fun G : Mat3 => (gramSchur G).det) gramDomain := by
    simp only [Matrix.det_fin_two]
    exact ((contDiffOn_gramSchur 0 0).mul (contDiffOn_gramSchur 1 1)).sub
      ((contDiffOn_gramSchur 0 1).mul (contDiffOn_gramSchur 1 0))
  fin_cases a
  · simp only [gramChart, gramPlaneU]
    exact (contDiff_entry 0 2).contDiffOn.div (contDiff_entry 2 2).contDiffOn h22
  · simp only [gramChart, gramPlaneU]
    exact (contDiff_entry 1 2).contDiffOn.div (contDiff_entry 2 2).contDiffOn h22
  · simp only [gramChart, gramChart_re_tau]
    exact (contDiffOn_gramSchur 0 1).div (contDiffOn_gramSchur 1 1) hs11
  · simp only [gramChart, gramChart_im_tau]
    exact (hdet.sqrt (fun G hG => hG.2.2.ne')).div (contDiffOn_gramSchur 1 1) hs11
  · simp only [gramChart, gramNormal]
    exact (contDiff_entry 2 2).contDiffOn.sqrt h22

theorem hasDerivAt_gramChart_line (G Q : Mat3) (hGs : G.IsSymm) (hQs : Q.IsSymm) (hG : G ∈ gramDomain) (a : Fin 5) :
    HasDerivAt (fun ε : ℝ => gramChart (G + ε • Q) a) (planeTangent G Q a) 0 := by
  have hsym : ∀ ε : ℝ, (G + ε • Q).IsSymm := fun ε => by
    unfold Matrix.IsSymm at *
    rw [Matrix.transpose_add, Matrix.transpose_smul, hGs, hQs]
  have hder : ∀ i j, HasDerivAt (fun ε : ℝ => (G + ε • Q) i j) (Q i j) 0 := by
    intro i j
    have : (fun ε : ℝ => (G + ε • Q) i j) = fun ε => G i j + ε * Q i j := by
      funext ε; simp
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Q i j)).const_add (G i j)
  have h0 : (G + (0 : ℝ) • Q) = G := by simp
  have hR : 0 < (G + (0 : ℝ) • Q) 2 2 := by rw [h0]; exact hG.1
  have h11 : 0 < gramSchur (G + (0 : ℝ) • Q) 1 1 := by rw [h0]; exact hG.2.1
  have hdet : 0 < (gramSchur (G + (0 : ℝ) • Q)).det := by rw [h0]; exact hG.2.2
  have hτ := hasDerivAt_gramPlaneTau (fun ε : ℝ => G + ε • Q) Q hsym hder hR h11 hdet
  have hu := hasDerivAt_gramPlaneU (fun ε : ℝ => G + ε • Q) Q hder hR.ne'
  have hs := ((hder 2 2).sqrt hR.ne')
  simp only [h0] at hτ hu hs
  unfold planeTangent
  fin_cases a
  · exact hu 0
  · exact hu 1
  · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hτ
  · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hτ
  · exact hs

theorem hasFDerivAt_gramChart (G : Mat3) (hG : G ∈ gramDomain) (a : Fin 5) :
    HasFDerivAt (fun G : Mat3 => gramChart G a) (fderiv ℝ (fun G : Mat3 => gramChart G a) G) G :=
  (((contDiffOn_gramChart a).differentiableOn (by simp)).differentiableAt
    (isOpen_gramDomain.mem_nhds hG)).hasFDerivAt

theorem fderiv_gramChart_apply (G Q : Mat3) (hGs : G.IsSymm) (hQs : Q.IsSymm) (hG : G ∈ gramDomain)
    (a : Fin 5) : fderiv ℝ (fun G : Mat3 => gramChart G a) G Q = planeTangent G Q a := by
  have hline : HasDerivAt (fun ε : ℝ => G + ε • Q) Q 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const Q).const_add G
    convert this using 1 <;> first | rfl | simp
  have h0 : G + (0 : ℝ) • Q = G := by simp
  have hF : HasFDerivAt (fun G : Mat3 => gramChart G a) (fderiv ℝ (fun G : Mat3 => gramChart G a) G)
      (G + (0 : ℝ) • Q) := by rw [h0]; exact hasFDerivAt_gramChart G hG a
  have h1 := hF.comp_hasDerivAt (0 : ℝ) hline
  exact h1.unique (hasDerivAt_gramChart_line G Q hGs hQs hG a)

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
