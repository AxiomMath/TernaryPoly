module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Twist
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RadialBound
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CholeskyContinuity

@[expose] public section


/-!
# A uniform `L¹` bound for the twisted pullback along a Gram triangle

For a Gram triangle whose points all lie in the Cholesky domain, the integrals
`∫_{ℝ²} ‖coeff_κ twPull ω L_{s,t} P_p Q₁ Q₂‖ ds dt` are bounded uniformly in the point `p` of the standard triangle
(`uniform_l1_twPull`).  Per point the bound is `l1_twPull` (coefficient mixing in the Cholesky frame and the `L¹` bound
`l1_bound_lineParabolic`); uniformity follows from the continuity of the Cholesky factor, of the frame directions
`halfConj`, of the coefficient action `ρ(q)` and compactness of the triangle.  This is the input of the Fubini
exchange of the real intertwining integral with the integral over the simplex.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem mem_cholDomain_conds {P : Mat3} (hP : P ∈ cholDomain) :
    0 < P 2 2 ∧ 0 < P 1 1 * P 2 2 - P 1 2 ^ 2 ∧ 0 < P.det := hP

/-- The coefficient of the twisted pullback in the Cholesky frame, as a finite sum. -/
theorem coeff_twPull_cholLine (n : ℕ) (h : ℂ → ℂ) (L P Q₁ Q₂ : Mat3) (hL : L.det ≠ 0)
    (hP : Pᵀ = P) (hPd : P ∈ cholDomain) (hQ₁ : Q₁ᵀ = Q₁) (hQ₂ : Q₂ᵀ = Q₂) (κ : Fin 3 →₀ ℕ) :
    (twPull (seedForm n h) L P Q₁ Q₂).coeff κ =
      ∑ ν ∈ degSet n, (frameCoefficient (seedForm n h) (L * cholLine P) (halfConj (cholLine P) Q₁)
          (halfConj (cholLine P) Q₂)).coeff ν *
        (SeedC3.rho (cholLine P) (MvPolynomial.monomial ν 1)).coeff κ := by
  obtain ⟨hs, hD, hdet⟩ := hPd
  have hqP : cholLine P * (cholLine P)ᵀ = P := cholLine_mul_transpose P hP hs hD hdet
  have hqne : (cholLine P).det ≠ 0 := (cholLine_det_pos hs hD hdet).ne'
  have := twPull_eq_frame (seedForm n h) L (cholLine P) Q₁ Q₂ hL hqne hQ₁ hQ₂
  rw [hqP] at this
  rw [this]
  exact coeff_rho_eq_sum (cholLine P) n _ (fun m' hm' => coeff_eq_zero_of_sum_ne
    (isHomogeneous_frameCoefficient_seed n h _ _ _) m' hm') κ

theorem cholLine_C_det (P : Mat3) :
    (!![cholC00 P, cholC01 P; 0, cholC11 P] : Matrix (Fin 2) (Fin 2) ℝ).det = cholC00 P * cholC11 P := by
  simp [Matrix.det_fin_two]

/-- **The `L¹` norm in `(s,t)` of the twisted pullback at a Gram point.** -/
theorem l1_twPull (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im})
    (M : ℝ) (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (P Q₁ Q₂ : Mat3) (hP : Pᵀ = P) (hPd : P ∈ cholDomain) (hQ₁ : Q₁ᵀ = Q₁) (hQ₂ : Q₂ᵀ = Q₂)
    (κ : Fin 3 →₀ ℕ) (Cw : ℝ)
    (hCw : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ‖wedgePoly (halfConj (cholLine P) Q₁ + (halfConj (cholLine P) Q₁)ᵀ)
      (halfConj (cholLine P) Q₂ + (halfConj (cholLine P) Q₂)ᵀ) ξ‖ ≤ Cw) :
    ∫ u : ℝ × ℝ, ‖(twPull (seedForm n h) (entryFrame u.1 u.2) P Q₁ Q₂).coeff κ‖ ≤
      ∑ ν ∈ degSet n, ‖(SeedC3.rho (cholLine P) (MvPolynomial.monomial ν 1)).coeff κ‖ *
        ((cholA P ^ 2 / (cholC00 P * cholC11 P)) *
          (Real.sqrt (radialA n ((cholC00 P * cholC11 P) ^ (n + 3) * M) ν Cw) * radK3)) := by
  obtain ⟨hs, hD, hdet⟩ := hPd
  have hdetC : 0 < cholC00 P * cholC11 P := mul_pos (cholC00_pos P hs hD) (cholC11_pos P hs)
  have hpos : 0 < (cholLine P).det := cholLine_det_pos hs hD hdet
  set V₁ := halfConj (cholLine P) Q₁ with hV₁
  set V₂ := halfConj (cholLine P) Q₂ with hV₂
  set r : (Fin 3 →₀ ℕ) → ℝ := fun ν =>
    ‖(SeedC3.rho (cholLine P) (MvPolynomial.monomial ν 1)).coeff κ‖ with hr
  have hpt : ∀ u : ℝ × ℝ, ‖(twPull (seedForm n h) (entryFrame u.1 u.2) P Q₁ Q₂).coeff κ‖ ≤
      ∑ ν ∈ degSet n, ‖(frameCoefficient (seedForm n h) (entryFrame u.1 u.2 * cholLine P) V₁ V₂).coeff ν‖ * r ν := by
    intro u
    rw [coeff_twPull_cholLine n h _ P Q₁ Q₂ (by rw [entryFrame_det_eq]; exact one_ne_zero) hP
      ⟨hs, hD, hdet⟩ hQ₁ hQ₂ κ]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
    rw [norm_mul]
  have hF : ∀ ν ∈ degSet n, Integrable (fun u : ℝ × ℝ => ‖(frameCoefficient (seedForm n h) (entryFrame u.1 u.2 * cholLine P) V₁ V₂).coeff ν‖) :=
    fun ν _ => (form_identity_coeff n hn h hh M hM (cholLine P) hpos V₁ V₂ ν).1.norm
  have hsumint : Integrable (fun u : ℝ × ℝ => ∑ ν ∈ degSet n, ‖(frameCoefficient (seedForm n h) (entryFrame u.1 u.2 * cholLine P) V₁ V₂).coeff ν‖ * r ν) :=
    integrable_finsetSum _ (fun ν hν => (hF ν hν).mul_const _)
  have hL1 : ∀ ν ∈ degSet n, ∫ u : ℝ × ℝ, ‖(frameCoefficient (seedForm n h) (entryFrame u.1 u.2 * cholLine P) V₁ V₂).coeff ν‖ ≤
      (cholA P ^ 2 / (cholC00 P * cholC11 P)) *
        (Real.sqrt (radialA n ((cholC00 P * cholC11 P) ^ (n + 3) * M) ν Cw) * radK3) := by
    intro ν hν
    have := l1_bound_lineParabolic n hn h hh M hM (cholA P) ![cholB0 P, cholB1 P]
      !![cholC00 P, cholC01 P; 0, cholC11 P] (cholA_pos P hD hdet) (by rw [cholLine_C_det]; exact hdetC)
      V₁ V₂ Cw hCw ν (mem_degSet.mp hν)
    rw [cholLine_C_det] at this
    rw [cholLine_eq P]
    exact this
  calc ∫ u : ℝ × ℝ, ‖(twPull (seedForm n h) (entryFrame u.1 u.2) P Q₁ Q₂).coeff κ‖
      ≤ ∫ u : ℝ × ℝ, ∑ ν ∈ degSet n, ‖(frameCoefficient (seedForm n h) (entryFrame u.1 u.2 * cholLine P) V₁ V₂).coeff ν‖ * r ν :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _) hsumint
          (Filter.Eventually.of_forall hpt)
    _ = ∑ ν ∈ degSet n, (∫ u : ℝ × ℝ, ‖(frameCoefficient (seedForm n h) (entryFrame u.1 u.2 * cholLine P) V₁ V₂).coeff ν‖) * r ν := by
        rw [integral_finsetSum _ (fun ν hν => (hF ν hν).mul_const _)]
        simp_rw [integral_mul_const]
    _ ≤ ∑ ν ∈ degSet n, r ν * ((cholA P ^ 2 / (cholC00 P * cholC11 P)) *
          (Real.sqrt (radialA n ((cholC00 P * cholC11 P) ^ (n + 3) * M) ν Cw) * radK3)) := by
        refine Finset.sum_le_sum fun ν hν => ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (hL1 ν hν) (norm_nonneg _)

section Uniform

variable {X : Type*} [TopologicalSpace X] {S : Set X}

theorem continuousOn_matrix_mul' {A B : X → Mat3} (hA : ContinuousOn A S) (hB : ContinuousOn B S) :
    ContinuousOn (fun x => A x * B x) S := by
  rw [continuousOn_iff_continuous_domRestrict] at *
  exact Continuous.matrix_mul hA hB

theorem continuousOn_matrix_transpose' {A : X → Mat3} (hA : ContinuousOn A S) :
    ContinuousOn (fun x => (A x)ᵀ) S := by
  rw [continuousOn_iff_continuous_domRestrict] at *
  exact Continuous.matrix_transpose hA

theorem continuousOn_halfConj {q : X → Mat3} {Q : Mat3} (hq : ContinuousOn q S)
    (hdet : ∀ x ∈ S, (q x).det ≠ 0) : ContinuousOn (fun x => halfConj (q x) Q) S := by
  have hinv : ContinuousOn (fun x => (q x)⁻¹) S := continuousOn_matInv.comp hq (fun x hx => hdet x hx)
  unfold halfConj
  exact ContinuousOn.const_smul (M := ℝ)
    (continuousOn_matrix_mul' (continuousOn_matrix_mul' hinv continuousOn_const)
      (continuousOn_matrix_transpose' hinv)) (1 / 2 : ℝ)

end Uniform

theorem continuous_radialA (n : ℕ) (m : Fin 3 →₀ ℕ) (C : ℝ) : Continuous (fun M : ℝ => radialA n M m C) := by
  unfold radialA
  fun_prop

/-- **A uniform `L¹` bound along the triangle.** -/
theorem uniform_l1_twPull (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im})
    (M : ℝ) (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (Γ₀ Γ₁ Γ₂ : Mat3) (h₀ : Γ₀ᵀ = Γ₀) (h₁ : Γ₁ᵀ = Γ₁) (h₂ : Γ₂ᵀ = Γ₂)
    (hcond : ∀ p ∈ stdTriangle, affTri Γ₀ Γ₁ Γ₂ p ∈ cholDomain) (κ : Fin 3 →₀ ℕ) :
    ∃ B : ℝ, ∀ p ∈ stdTriangle, ∫ u : ℝ × ℝ, ‖(twPull (seedForm n h) (entryFrame u.1 u.2) (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ‖ ≤ B := by
  set Pf : ℝ × ℝ → Mat3 := affTri Γ₀ Γ₁ Γ₂ with hPf
  set qf : ℝ × ℝ → Mat3 := fun p => cholLine (Pf p) with hqf
  have hQ₁ : (Γ₁ - Γ₀)ᵀ = Γ₁ - Γ₀ := by rw [Matrix.transpose_sub, h₀, h₁]
  have hQ₂ : (Γ₂ - Γ₀)ᵀ = Γ₂ - Γ₀ := by rw [Matrix.transpose_sub, h₀, h₂]
  have hPs : ∀ p, (Pf p)ᵀ = Pf p := by
    intro p
    simp only [hPf, affTri, Matrix.transpose_add, Matrix.transpose_smul, hQ₁, hQ₂, h₀]
  have hPc : ContinuousOn Pf stdTriangle := (continuous_affTri Γ₀ Γ₁ Γ₂).continuousOn
  have hqc : ContinuousOn qf stdTriangle := continuousOn_cholLine.comp hPc hcond
  have hdetq : ∀ p ∈ stdTriangle, (qf p).det ≠ 0 := fun p hp =>
    (cholLine_det_pos (hcond p hp).1 (hcond p hp).2.1 (hcond p hp).2.2).ne'
  have hV₁ := continuousOn_halfConj (Q := Γ₁ - Γ₀) hqc hdetq
  have hV₂ := continuousOn_halfConj (Q := Γ₂ - Γ₀) hqc hdetq
  -- uniform bound for the wedge polynomial
  have hKc : IsCompact (stdTriangle ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    isCompact_stdTriangle.prod (isCompact_closedBall _ _)
  have hWc : ContinuousOn (fun z : (ℝ × ℝ) × ℂ => ‖wedgePoly
      (halfConj (qf z.1) (Γ₁ - Γ₀) + (halfConj (qf z.1) (Γ₁ - Γ₀))ᵀ)
      (halfConj (qf z.1) (Γ₂ - Γ₀) + (halfConj (qf z.1) (Γ₂ - Γ₀))ᵀ) z.2‖)
      (stdTriangle ×ˢ Metric.closedBall (0 : ℂ) 1) := by
    refine ContinuousOn.norm ?_
    have e1 : ContinuousOn (fun z : (ℝ × ℝ) × ℂ => halfConj (qf z.1) (Γ₁ - Γ₀))
        (stdTriangle ×ˢ Metric.closedBall (0 : ℂ) 1) :=
      hV₁.comp continuousOn_fst (fun z hz => hz.1)
    have e2 : ContinuousOn (fun z : (ℝ × ℝ) × ℂ => halfConj (qf z.1) (Γ₂ - Γ₀))
        (stdTriangle ×ˢ Metric.closedBall (0 : ℂ) 1) :=
      hV₂.comp continuousOn_fst (fun z hz => hz.1)
    have e1' := e1.add (continuousOn_matrix_transpose' e1)
    have e2' := e2.add (continuousOn_matrix_transpose' e2)
    have hF := e1'.prodMk (e2'.prodMk (continuousOn_snd (s := stdTriangle ×ˢ Metric.closedBall (0 : ℂ) 1)))
    have := continuous_wedgePoly.comp_continuousOn hF
    exact this
  obtain ⟨Cw, hCw⟩ := hKc.exists_bound_of_continuousOn hWc
  have hCwp : ∀ p ∈ stdTriangle, ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ‖wedgePoly
      (halfConj (qf p) (Γ₁ - Γ₀) + (halfConj (qf p) (Γ₁ - Γ₀))ᵀ)
      (halfConj (qf p) (Γ₂ - Γ₀) + (halfConj (qf p) (Γ₂ - Γ₀))ᵀ) ξ‖ ≤ Cw := by
    intro p hp ξ hξ
    have := hCw (p, ξ) ⟨hp, by simpa using hξ⟩
    simpa using this
  -- the continuous majorant
  set Bf : ℝ × ℝ → ℝ := fun p => ∑ ν ∈ degSet n,
    ‖(SeedC3.rho (qf p) (MvPolynomial.monomial ν 1)).coeff κ‖ *
      ((cholA (Pf p) ^ 2 / (cholC00 (Pf p) * cholC11 (Pf p))) *
        (Real.sqrt (radialA n ((cholC00 (Pf p) * cholC11 (Pf p)) ^ (n + 3) * M) ν Cw) * radK3)) with hBf
  have hBc : ContinuousOn Bf stdTriangle := by
    refine continuousOn_finsetSum _ fun ν _ => ?_
    refine ContinuousOn.mul ?_ ?_
    · exact (continuousOn_rho_coeff _ κ |>.comp hqc (fun p hp => hdetq p hp)).norm
    · have hA := continuousOn_cholA.comp hPc hcond
      have hC0 := continuousOn_cholC00.comp hPc hcond
      have hC1 := continuousOn_cholC11.comp hPc hcond
      have hCd : ContinuousOn (fun p => cholC00 (Pf p) * cholC11 (Pf p)) stdTriangle := hC0.mul hC1
      refine ContinuousOn.mul ((hA.pow 2).div hCd (fun p hp => ?_)) ?_
      · exact (mul_pos (cholC00_pos _ (hcond p hp).1 (hcond p hp).2.1) (cholC11_pos _ (hcond p hp).1)).ne'
      · refine ContinuousOn.mul ?_ continuousOn_const
        refine Real.continuous_sqrt.comp_continuousOn ?_
        exact (continuous_radialA n ν Cw).comp_continuousOn ((hCd.pow (n + 3)).mul continuousOn_const)
  obtain ⟨B, hB⟩ := isCompact_stdTriangle.exists_bound_of_continuousOn hBc
  refine ⟨B, fun p hp => ?_⟩
  have := l1_twPull n hn h hh M hM (Pf p) (Γ₁ - Γ₀) (Γ₂ - Γ₀) (hPs p) (hcond p hp) hQ₁ hQ₂ κ Cw
    (hCwp p hp)
  exact this.trans ((le_abs_self _).trans (hB p hp))

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
