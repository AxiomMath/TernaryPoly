module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBruhat
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Seed
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Normalization

@[expose] public section


/-!
# The face tangents `e_p` and the real entry frame: the base point of the line face

Paper: Appendix C.5 (`ar:sec:real`),
`ar:eq:intertwiner`, `ar:eq:realintegral`.

At the base point `x* = (0, 0, 0, 1)` of the face (`jFace x* = (0,0,0,1,1)` is the identity coset `1 · SO(3)`), the
involution `jFace` carries the face tangents to the plane-chart tangents of the real entry frame:

* `jFace (x* + ε e₀) = (-ε, 0, 0, 1, 1)`, `jFace (x* + ε e₂) = (0, -ε, 0, 1, 1)` (exactly, for all `ε`);
  so `d jFace (e₀) = -∂_{u₁}`, `d jFace (e₂) = -∂_{u₂}`, and `∂_{u₁}, ∂_{u₂}` are the tangents of
  `E₁₃, E₂₃` at `1 · SO(3)` (`chartTangent_E13`, `chartTangent_E23`);
* hence the face pairing `(e₀, e₂)` at `x*` of the summand `S_h(g)` is the frame coefficient
  `ρ(g)⁻¹ ω_h(dL_g E₁₃, dL_g E₂₃)` of the real entry computation (the two signs cancel):
  `fPull_xStar_eq_frameCoefficient`.

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
open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed (frameCoefficient frameValue chartTangent gramChart
  gramCurve)


section Measure

theorem integral_fin2_negswap (F : ℝ × ℝ → ℂ) :
    ∫ u : Fin 2 → ℝ, F (-(u 1), -(u 0)) = ∫ st : ℝ × ℝ, F st := by
  let e : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have he : MeasurePreserving e volume volume := volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)
  let σ : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    MeasurableEquiv.prodComm.trans ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ))
  have hσ : MeasurePreserving σ volume volume := by
    have h1 : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) volume volume :=
      Measure.measurePreserving_swap
    have h2 : MeasurePreserving (fun z : ℝ × ℝ => (-z.1, -z.2)) volume volume :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
        (Measure.measurePreserving_neg (volume : Measure ℝ))
    exact h2.comp h1
  have hφ : MeasurePreserving (e.trans σ) volume volume := hσ.comp he
  have h3 : ∀ u : Fin 2 → ℝ, (e.trans σ) u = (-(u 1), -(u 0)) := fun u => rfl
  have := hφ.integral_comp' F
  simp only [h3] at this
  exact this

theorem coeff_single_eq_eval {n : ℕ} {p : MvPolynomial (Fin 3) ℂ} (hp : p.IsHomogeneous n) :
    p.coeff (Finsupp.single 1 n) = eval ![0, 1, 0] p := by
  classical
  rw [MvPolynomial.eval_eq']
  by_cases hmem : Finsupp.single 1 n ∈ p.support
  · rw [Finset.sum_eq_single (Finsupp.single 1 n)]
    · simp [Fin.prod_univ_three]
    · intro d hd hne
      have hdeg : ∑ i, d i = n := by
        have := hp (mem_support_iff.1 hd)
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
      have : d 0 ≠ 0 ∨ d 2 ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hne
        ext i
        fin_cases i
        · simp [hcon.1]
        · have : d 1 = n := by
            rw [Fin.sum_univ_three, hcon.1, hcon.2] at hdeg; simpa using hdeg
          simp [this]
        · simp [hcon.2]
      rcases this with h0 | h2
      · simp [Fin.prod_univ_three, h0]
      · simp [Fin.prod_univ_three, h2]
    · intro h; exact absurd hmem h
  · have hz : p.coeff (Finsupp.single 1 n) = 0 := notMem_support_iff.1 hmem
    rw [hz, Finset.sum_eq_zero]
    intro d hd
    have hdeg : ∑ i, d i = n := by
      have := hp (mem_support_iff.1 hd)
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
    have hne : d ≠ Finsupp.single 1 n := fun h => hmem (h ▸ hd)
    have : d 0 ≠ 0 ∨ d 2 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hne
      ext i
      fin_cases i
      · simp [hcon.1]
      · have : d 1 = n := by
          rw [Fin.sum_univ_three, hcon.1, hcon.2] at hdeg; simpa using hdeg
        simp [this]
      · simp [hcon.2]
    rcases this with h0 | h2
    · simp [Fin.prod_univ_three, h0]
    · simp [Fin.prod_univ_three, h2]


end Measure

section Base

/-- The base point of the face. -/
def xStar : Face := ![0, 0, 0, 1]

theorem xStar_mem : xStar ∈ faceSet := by
  show (0 : ℝ) < xStar 3
  simp [xStar]

theorem rt_explicit (a b c d e f g h i : ℝ) :
    rt (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) ℝ) = !![i, f, c; h, e, b; g, d, a] := by
  ext r s
  fin_cases r <;> fin_cases s <;> rfl

theorem jFace_line0 (ε : ℝ) : jFace (xStar + ε • (Pi.single 0 1 : Face)) = ![-ε, 0, 0, 1, 1] := by
  have hp : ptOf (xStar + ε • (Pi.single 0 1 : Face)) = ![ε, 0, 0, 1, 1] := by
    funext i; fin_cases i <;> simp [ptOf, xStar]
  have hG : planeGram ![ε, 0, 0, 1, 1] = !![1 + ε ^ 2, 0, ε; 0, 1, 0; ε, 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [planeGram]
  have hinv : (!![1 + ε ^ 2, 0, ε; 0, 1, 0; ε, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ =
      !![1, 0, -ε; 0, 1, 0; -ε, 0, 1 + ε ^ 2] := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  unfold jFace jPlane jGram
  rw [hp, hG, hinv, rt_explicit]
  funext i
  fin_cases i <;> simp [planePoint]

theorem jFace_line2 (ε : ℝ) : jFace (xStar + ε • (Pi.single 2 1 : Face)) = ![0, -ε, 0, 1, 1] := by
  have hp : ptOf (xStar + ε • (Pi.single 2 1 : Face)) = ![0, 0, ε, 1, 1] := by
    funext i; fin_cases i <;> simp [ptOf, xStar]
  have hG : planeGram ![0, 0, ε, 1, 1] = !![1 + ε ^ 2, ε, 0; ε, 1, 0; 0, 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [planeGram]
    all_goals ring
  have hinv : (!![1 + ε ^ 2, ε, 0; ε, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ =
      !![1, -ε, 0; -ε, 1 + ε ^ 2, 0; 0, 0, 1] := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  unfold jFace jPlane jGram
  rw [hp, hG, hinv, rt_explicit]
  funext i
  fin_cases i <;> simp [planePoint]
  all_goals ring

theorem jFace_xStar : jFace xStar = basePt := by
  have := jFace_line0 0
  simp only [zero_smul, add_zero, neg_zero] at this
  rw [this]
  funext i; fin_cases i <;> simp [basePt]

theorem hasDerivAt_jFace_line (e : Face) :
    HasDerivAt (fun ε : ℝ => jFace (xStar + ε • e)) (fderiv ℝ jFace xStar e) 0 := by
  have hd : HasFDerivAt jFace (fderiv ℝ jFace xStar) (xStar + (0 : ℝ) • e) := by
    simpa using (differentiableAt_jFace xStar_mem).hasFDerivAt
  have hl : HasDerivAt (fun ε : ℝ => xStar + ε • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add xStar
  exact hd.comp_hasDerivAt (0 : ℝ) hl

theorem fderiv_jFace_e0 : fderiv ℝ jFace xStar (Pi.single 0 1) = ![-1, 0, 0, 0, 0] := by
  have h1 := hasDerivAt_jFace_line (Pi.single 0 1)
  have h2 : HasDerivAt (fun ε : ℝ => jFace (xStar + ε • (Pi.single 0 1 : Face))) ![-1, 0, 0, 0, 0] 0 := by
    have : (fun ε : ℝ => jFace (xStar + ε • (Pi.single 0 1 : Face))) = fun ε => ![-ε, 0, 0, 1, 1] :=
      funext jFace_line0
    rw [this, hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hasDerivAt_neg' (0 : ℝ)
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    · simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  exact h1.unique h2

theorem fderiv_jFace_e2 : fderiv ℝ jFace xStar (Pi.single 2 1) = ![0, -1, 0, 0, 0] := by
  have h1 := hasDerivAt_jFace_line (Pi.single 2 1)
  have h2 : HasDerivAt (fun ε : ℝ => jFace (xStar + ε • (Pi.single 2 1 : Face))) ![0, -1, 0, 0, 0] 0 := by
    have : (fun ε : ℝ => jFace (xStar + ε • (Pi.single 2 1 : Face))) = fun ε => ![0, -ε, 0, 1, 1] :=
      funext jFace_line2
    rw [this, hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa using hasDerivAt_neg' (0 : ℝ)
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    · simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  exact h1.unique h2

end Base

section Charts

/-- `gramChart` is `planePoint` on Gram matrices. -/
theorem gramSchur_det {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G) :
    (gramSchur G).det = 1 / G 2 2 := by
  have hs := hG.s_pos
  have h10 := hG.symm 1 0
  have h20 := hG.symm 2 0
  have h21 := hG.symm 2 1
  have hd := hG.2
  have key : (gramSchur G).det * G 2 2 = G.det := by
    rw [Matrix.det_fin_three, Matrix.det_fin_two]
    simp only [gramSchur, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [h10, h20, h21]
    field_simp
    ring
  rw [hd] at key
  field_simp
  linarith

theorem gramPlaneTau_re (G : Matrix (Fin 3) (Fin 3) ℝ) :
    (gramPlaneTau G).re = gramSchur G 0 1 / gramSchur G 1 1 := by
  unfold gramPlaneTau
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, add_zero, sub_self]

theorem gramPlaneTau_im (G : Matrix (Fin 3) (Fin 3) ℝ) :
    (gramPlaneTau G).im = Real.sqrt (gramSchur G).det / gramSchur G 1 1 := by
  unfold gramPlaneTau
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, one_mul, mul_zero, zero_add]

theorem gramChart_eq_planePoint {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G) :
    gramChart G = planePoint G := by
  have hs := hG.s_pos
  have hd := gramSchur_det hG
  have hsq : Real.sqrt ((gramSchur G).det) = 1 / Real.sqrt (G 2 2) := by
    rw [hd, Real.sqrt_div' _ hs.le, Real.sqrt_one]
  have h01 : gramSchur G 0 1 = G 0 1 - G 0 2 * G 1 2 / G 2 2 := by simp [gramSchur]
  have h11 : gramSchur G 1 1 = G 1 1 - G 1 2 * G 1 2 / G 2 2 := by simp [gramSchur]
  funext i
  fin_cases i
  · simp [gramChart, planePoint, gramPlaneU]
  · simp [gramChart, planePoint, gramPlaneU]
  · show (gramPlaneTau G).re = _
    rw [gramPlaneTau_re, h01, h11]
    rfl
  · show (gramPlaneTau G).im = _
    rw [gramPlaneTau_im, hsq, h11]
    show 1 / Real.sqrt (G 2 2) / (G 1 1 - G 1 2 * G 1 2 / G 2 2) = 1 / (Real.sqrt (G 2 2) * (G 1 1 - G 1 2 * G 1 2 / G 2 2))
    rw [div_div]
  · simp [gramChart, planePoint, gramNormal]

/-- The curves of Gram matrices of `1 + ε E₁₃`, `1 + ε E₂₃`. -/
def cE0 (ε : ℝ) : Fin 5 → ℝ := ![ε, 0, 0, 1, 1]

def cE2 (ε : ℝ) : Fin 5 → ℝ := ![0, ε, 0, 1, 1]

theorem cE0_mem (ε : ℝ) : cE0 ε ∈ Omega := by
  constructor <;> simp [cE0]

theorem cE2_mem (ε : ℝ) : cE2 ε ∈ Omega := by
  constructor <;> simp [cE2]

theorem E13_gram (ε : ℝ) :
    (1 + ε • (Matrix.single 0 2 1 : Matrix (Fin 3) (Fin 3) ℝ)) *
        (1 + ε • (Matrix.single 0 2 1 : Matrix (Fin 3) (Fin 3) ℝ)).transpose = planeGram (cE0 ε) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeGram, cE0, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      Matrix.one_apply]
  all_goals ring

theorem E23_gram (ε : ℝ) :
    (1 + ε • (Matrix.single 1 2 1 : Matrix (Fin 3) (Fin 3) ℝ)) *
        (1 + ε • (Matrix.single 1 2 1 : Matrix (Fin 3) (Fin 3) ℝ)).transpose = planeGram (cE2 ε) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeGram, cE2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      Matrix.one_apply]
  all_goals ring

theorem hasDerivAt_cE0 : HasDerivAt cE0 (Pi.single 0 1) 0 := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [cE0] using hasDerivAt_id' (0 : ℝ)
  · simpa [cE0] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · simpa [cE0] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · simpa [cE0] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  · simpa [cE0] using hasDerivAt_const (0 : ℝ) (1 : ℝ)

theorem hasDerivAt_cE2 : HasDerivAt cE2 (Pi.single 1 1) 0 := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [cE2] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · simpa [cE2] using hasDerivAt_id' (0 : ℝ)
  · simpa [cE2] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · simpa [cE2] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  · simpa [cE2] using hasDerivAt_const (0 : ℝ) (1 : ℝ)

theorem cE0_zero : cE0 0 = basePt := by funext i; fin_cases i <;> simp [cE0, basePt]

theorem cE2_zero : cE2 0 = basePt := by funext i; fin_cases i <;> simp [cE2, basePt]

/-- The chart tangent of `E₁₃` at `g · SO(3)` is `D(planeAct g)` applied to `∂_{u₁}`. -/
theorem chartTangent_E13 {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) (c : Fin 5) :
    chartTangent g (Matrix.single 0 2 1) c = fderiv ℝ (planeAct g) basePt (Pi.single 0 1) c := by
  have hc : ∀ ε : ℝ, gramChart (gramCurve g (Matrix.single 0 2 1) ε) = planeAct g (cE0 ε) := by
    intro ε
    have hgr : gramCurve g (Matrix.single 0 2 1) ε = g * planeGram (cE0 ε) * g.transpose := by
      unfold gramCurve
      rw [← E13_gram ε]
      simp only [Matrix.mul_assoc]
    rw [hgr]
    exact gramChart_eq_planePoint ((planeGram_isGram (cE0_mem ε)).conj hg)
  have hd : HasFDerivAt (planeAct g) (fderiv ℝ (planeAct g) basePt) (cE0 0) := by
    rw [cE0_zero]
    exact (differentiableAt_planeAct hg basePt_mem).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) hasDerivAt_cE0
  have h' := (hasDerivAt_pi.1 h) c
  unfold chartTangent
  simp_rw [hc]
  exact h'.deriv

theorem chartTangent_E23 {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) (c : Fin 5) :
    chartTangent g (Matrix.single 1 2 1) c = fderiv ℝ (planeAct g) basePt (Pi.single 1 1) c := by
  have hc : ∀ ε : ℝ, gramChart (gramCurve g (Matrix.single 1 2 1) ε) = planeAct g (cE2 ε) := by
    intro ε
    have hgr : gramCurve g (Matrix.single 1 2 1) ε = g * planeGram (cE2 ε) * g.transpose := by
      unfold gramCurve
      rw [← E23_gram ε]
      simp only [Matrix.mul_assoc]
    rw [hgr]
    exact gramChart_eq_planePoint ((planeGram_isGram (cE2_mem ε)).conj hg)
  have hd : HasFDerivAt (planeAct g) (fderiv ℝ (planeAct g) basePt) (cE2 0) := by
    rw [cE2_zero]
    exact (differentiableAt_planeAct hg basePt_mem).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) hasDerivAt_cE2
  have h' := (hasDerivAt_pi.1 h) c
  unfold chartTangent
  simp_rw [hc]
  exact h'.deriv

end Charts


section Assembly

open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed (lowestWeightVector
  seed_frameCoefficient_entryFrame seed_frameCoefficient_entryFrame_eval)

theorem fPull_rho (G : Matrix (Fin 3) (Fin 3) ℝ) (Φ : Face → Fin 5 → ℝ)
    (W : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (x : Face) (i j : Fin 4) :
    fPull Φ (fun y a b => rho G (W y a b)) x i j = rho G (fPull Φ W x i j) := by
  unfold fPull
  rw [rho_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rho_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rho_C_mul]

/-- **The face pairing `(e₀, e₂)` at the base point of the summand `S_h(g)` is the frame coefficient of
S1's real entry computation**: `jFace^* S_h(g)(x*; e₀, e₂) = ρ(g)⁻¹ ω_h(dL_g E₁₃, dL_g E₂₃)`. The two
signs `d jFace e₀ = -∂_{u₁}`, `d jFace e₂ = -∂_{u₂}` cancel. -/
theorem fPull_xStar_eq_frameCoefficient (n : ℕ) (h : ℂ → ℂ) {g : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : g.det = 1) :
    fPull jFace (fun y a b => summandPoly n h g y a b) xStar 0 2 =
      frameCoefficient (seedForm n h) g (Matrix.single 0 2 1) (Matrix.single 1 2 1) := by
  have hjd : DifferentiableAt ℝ jFace xStar := differentiableAt_jFace xStar_mem
  have hpd : DifferentiableAt ℝ (planeAct g) (jFace xStar) := by
    rw [jFace_xStar]; exact differentiableAt_planeAct hg basePt_mem
  have e : fPull jFace (fun y a b => formPullback (planeAct g) (seedForm n h) y a b) xStar 0 2 =
      fPull (planeAct g ∘ jFace) (seedForm n h) xStar 0 2 :=
    (fPull_comp jFace (planeAct g) (seedForm n h) xStar hjd hpd 0 2).symm
  have hgram : IsGram (g * g.transpose) := by
    have := (planeGram_isGram basePt_mem).conj hg
    simpa [planeGram_basePt] using this
  have hpt : (planeAct g ∘ jFace) xStar = gramChart (g * g.transpose) := by
    rw [Function.comp_apply, jFace_xStar, gramChart_eq_planePoint hgram]
    simp [planeAct, planeGram_basePt]
  have hD : fderiv ℝ (planeAct g ∘ jFace) xStar =
      (fderiv ℝ (planeAct g) basePt).comp (fderiv ℝ jFace xStar) := by
    rw [fderiv_comp xStar hpd hjd, jFace_xStar]
  have hD0 : ∀ a, fderiv ℝ (planeAct g ∘ jFace) xStar (Pi.single 0 1) a =
      -chartTangent g (Matrix.single 0 2 1) a := by
    intro a
    rw [hD, ContinuousLinearMap.comp_apply, fderiv_jFace_e0, chartTangent_E13 hg]
    have : (![-1, 0, 0, 0, 0] : Fin 5 → ℝ) = -(Pi.single 0 1 : Fin 5 → ℝ) := by
      funext i; fin_cases i <;> simp
    rw [this, map_neg]
    rfl
  have hD2 : ∀ b, fderiv ℝ (planeAct g ∘ jFace) xStar (Pi.single 2 1) b =
      -chartTangent g (Matrix.single 1 2 1) b := by
    intro b
    rw [hD, ContinuousLinearMap.comp_apply, fderiv_jFace_e2, chartTangent_E23 hg]
    have : (![0, -1, 0, 0, 0] : Fin 5 → ℝ) = -(Pi.single 1 1 : Fin 5 → ℝ) := by
      funext i; fin_cases i <;> simp
    rw [this, map_neg]
    rfl
  have h1 : fPull jFace (fun y a b => summandPoly n h g y a b) xStar 0 2 =
      rho g⁻¹ (fPull jFace (fun y a b => formPullback (planeAct g) (seedForm n h) y a b) xStar 0 2) := by
    simp only [summandPoly]
    exact fPull_rho g⁻¹ jFace (fun y a b => formPullback (planeAct g) (seedForm n h) y a b) xStar 0 2
  calc fPull jFace (fun y a b => summandPoly n h g y a b) xStar 0 2
      = rho g⁻¹ (fPull jFace (fun y a b => formPullback (planeAct g) (seedForm n h) y a b) xStar 0 2) :=
        h1
    _ = rho g⁻¹ (fPull (planeAct g ∘ jFace) (seedForm n h) xStar 0 2) := by rw [e]
    _ = frameCoefficient (seedForm n h) g (Matrix.single 0 2 1) (Matrix.single 1 2 1) := by
        unfold frameCoefficient frameValue
        refine congrArg (rho g⁻¹) ?_
        unfold fPull
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [hD0 a, hD2 b, hpt, neg_mul_neg]

theorem W0inv_qMat (u : Fin 2 → ℝ) : W0inv * qMat u = entryFrame (-(u 1)) (-(u 0)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W0inv, qMat, entryFrame, Matrix.mul_apply, Fin.sum_univ_three]

/-- **`Tinf` at the base point is the real intertwining integral of S1's frame coefficient**, for every seed
`h`: `T_∞[h](x*; e₀, e₂)_m = ∫_{ℝ²} coeff_m ρ(L)⁻¹ ω_h(dL E₁₃, dL E₂₃) ds dt`, `L = w₀⁻¹u(s,t)`. -/
theorem Tinf_eq_entryFrame (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) :
    Tinf n h xStar 0 2 m = ∫ st : ℝ × ℝ,
      (frameCoefficient (seedForm n h) (entryFrame st.1 st.2) (Matrix.single 0 2 1)
        (Matrix.single 1 2 1)).coeff m := by
  unfold Tinf
  have hpt : ∀ u : Fin 2 → ℝ, orbitIntegrand n h xStar 0 2 m W0inv u =
      (frameCoefficient (seedForm n h) (entryFrame (-(u 1)) (-(u 0))) (Matrix.single 0 2 1)
        (Matrix.single 1 2 1)).coeff m := by
    intro u
    have hg : (W0inv * qMat u).det = 1 := by rw [Matrix.det_mul, det_W0inv, det_qMat]; norm_num
    unfold orbitIntegrand
    rw [fPull_xStar_eq_frameCoefficient n h hg, W0inv_qMat]
  simp_rw [hpt]
  exact integral_fin2_negswap (fun st => (frameCoefficient (seedForm n h) (entryFrame st.1 st.2)
    (Matrix.single 0 2 1) (Matrix.single 1 2 1)).coeff m)

theorem hom_aux (n : ℕ) (c a b d : ℂ) :
    (C c * (C a * X 0 + C b * X 1 + C d * X 2) ^ n : MvPolynomial (Fin 3) ℂ).IsHomogeneous n := by
  have h1 : (C a * X 0 + C b * X 1 + C d * X 2 : MvPolynomial (Fin 3) ℂ).IsHomogeneous 1 :=
    ((isHomogeneous_C_mul_X a 0).add (isHomogeneous_C_mul_X b 1)).add (isHomogeneous_C_mul_X d 2)
  have h2 := h1.pow n
  rw [one_mul] at h2
  have := (isHomogeneous_C (Fin 3) c).mul h2
  rwa [zero_add] at this

/-- **The lowest-weight instance** (S1's real entry): at the base point, for the lowest-weight vector
`h = (τ + i)^{-(n+3)}`, the `Yⁿ`-coefficient of the real intertwining integral is `I_n = entryIntegral n`. -/
theorem Tinf_lowestWeight (n : ℕ) :
    Tinf n (lowestWeightVector n) xStar 0 2 (Finsupp.single 1 n) = entryIntegral n := by
  rw [Tinf_eq_entryFrame]
  have hpt : ∀ st : ℝ × ℝ, (frameCoefficient (seedForm n (lowestWeightVector n))
      (entryFrame st.1 st.2) (Matrix.single 0 2 1) (Matrix.single 1 2 1)).coeff (Finsupp.single 1 n) =
      -Complex.I * entryIntegrand n st := by
    intro st
    have hhom : (frameCoefficient (seedForm n (lowestWeightVector n)) (entryFrame st.1 st.2)
        (Matrix.single 0 2 1) (Matrix.single 1 2 1)).IsHomogeneous n := by
      rw [seed_frameCoefficient_entryFrame]
      exact hom_aux n _ _ _ _
    rw [coeff_single_eq_eval hhom, seed_frameCoefficient_entryFrame_eval]
  simp_rw [hpt]
  rw [integral_const_mul]
  rfl

/-- **`c_∞`**: at the base point the lowest-weight instance of the real intertwining integral is
`c_∞ · (-1)ⁿ h(i)` with `c_∞ = -2πi/(n+1)` and `h(i) = (2i)^{-(n+3)}` (the value of the line seed at `τ = i`). -/
theorem Tinf_lowestWeight_cinfty (n : ℕ) :
    Tinf n (lowestWeightVector n) xStar 0 2 (Finsupp.single 1 n) =
      (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) *
        ((-1) ^ n * (2 * Complex.I) ^ (-((n : ℤ) + 3))) := by
  rw [Tinf_lowestWeight]
  have hD : ((-1 : ℂ) ^ n * (2 * Complex.I) ^ (-((n : ℤ) + 3))) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact zpow_ne_zero _ (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  exact (div_eq_iff hD).1 (real_constant_term_entry n).2.2.1

end Assembly

end TernaryPeriodPolynomials.Argument.EisensteinClass
