module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.GramChart
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CupSeed
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CupBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.RadicalCocycle

@[expose] public section


/-!
# The cup of the line potential and the line radical is the line seed

Line-face analogue of `CupSeed`.  The line radical `lineRadical n χ p Q = ι(lrC₀(p) ∂₀Q + lrC₁(p) ∂₁Q)` is linear in
the radical coordinates, which are `lrC = (w₂, -w₁)` in terms of the line chart (`w = G_{1,{2,3}} (G_{{2,3},{2,3}})⁻¹`);
along the chart its coefficients are `lFunLine`.  For a vector potential `A` with `A_j' = F · pointCoord_j` and the
chart `τ(G)`, `cup_form_eq_seed_line` gives
`∑ⱼ [da_j(Q₁) dl_j(Q₂) - da_j(Q₂) dl_j(Q₁)] = coeff_μ σ_h(Q₁, Q₂)` with the line seed
`σ_h = h(τ)(τZ - Y)ⁿ (τ dw₁ + dw₂) ∧ dτ` and `h = (-1)^{n+1} (n+1) F` (compare `(-1)ⁿ (n+1) F` on the plane side:
the relative sign is real and enters the final scalar).  `line_cup_bridge` is the cup/triangle bridge on the line
face.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The binary point power, as a polynomial in the two binary variables. -/
theorem binaryPointPower_val (N : ℕ) (z : ℂ) :
    ((binaryPointPower N z : Binary.HomogeneousPoly N) : Binary.Poly) =
      (MvPolynomial.X 0 - MvPolynomial.C z * MvPolynomial.X 1) ^ N := rfl

theorem pderiv0_pointPower (n : ℕ) (z : ℂ) :
    pderiv (0 : Fin 2) ((MvPolynomial.X 0 - MvPolynomial.C z * MvPolynomial.X 1 : Binary.Poly) ^ (n + 1)) =
      MvPolynomial.C ((n + 1 : ℕ) : ℂ) * (MvPolynomial.X 0 - MvPolynomial.C z * MvPolynomial.X 1) ^ n := by
  rw [Derivation.leibniz_pow]
  simp [pderiv_X]

theorem pderiv1_pointPower (n : ℕ) (z : ℂ) :
    pderiv (1 : Fin 2) ((MvPolynomial.X 0 - MvPolynomial.C z * MvPolynomial.X 1 : Binary.Poly) ^ (n + 1)) =
      -(MvPolynomial.C ((n + 1 : ℕ) : ℂ) * MvPolynomial.C z) *
        (MvPolynomial.X 0 - MvPolynomial.C z * MvPolynomial.X 1) ^ n := by
  rw [Derivation.leibniz_pow]
  simp [pderiv_X]
  ring

/-- The linear functional `Q ↦ coeff_μ ι (∂_k Q)` on binary forms. -/
def derCoeff (n : ℕ) (k : Fin 2) (μ : Fin 3 →₀ ℕ) : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ μ).comp
    ((rename (Fin.succ : Fin 2 → Fin 3) : Binary.Poly →ₐ[ℂ] Poly).toLinearMap.comp
      ((pderiv k : Derivation ℂ Binary.Poly Binary.Poly).toLinearMap.comp (Submodule.subtype _)))

theorem derCoeff_apply (n : ℕ) (k : Fin 2) (μ : Fin 3 →₀ ℕ) (Q : Binary.HomogeneousPoly (n + 1)) :
    derCoeff n k μ Q = (rename (Fin.succ : Fin 2 → Fin 3) (pderiv k (Q : Binary.Poly))).coeff μ := rfl

/-- The coefficient vector of the derivative of a basis form. -/
def cDer (n : ℕ) (k : Fin 2) (μ : Fin 3 →₀ ℕ) (j : Fin (n + 2)) : ℂ :=
  derCoeff n k μ (binaryWeightBasis (n + 1) j)

theorem sum_pointCoord_cDer (n : ℕ) (k : Fin 2) (μ : Fin 3 →₀ ℕ) (z : ℂ) :
    ∑ j, pointCoord n z j * cDer n k μ j = derCoeff n k μ (binaryPointPower (n + 1) z) := by
  rw [← sum_pointCoord_smul n z, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, cDer]

/-- The line radical coefficients along the line chart: `l_j(G) = w₂(G) c⁰_j - w₁(G) c¹_j`. -/
def lFunLine (n : ℕ) (μ : Fin 3 →₀ ℕ) (G : Mat3) : Fin (n + 2) → ℂ :=
  fun j => ((lineChart G 1 : ℝ) : ℂ) * cDer n 0 μ j - ((lineChart G 0 : ℝ) : ℂ) * cDer n 1 μ j

theorem contDiffOn_lFunLine (n : ℕ) (μ : Fin 3 →₀ ℕ) : ContDiffOn ℝ ⊤ (lFunLine n μ) lineDomain := by
  refine contDiffOn_pi.mpr fun j => ?_
  unfold lFunLine
  exact (((Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_lineChart 1)).mul contDiffOn_const).sub
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_lineChart 0)).mul contDiffOn_const))

/-- `τ` in line-face coordinates, as a function of the Gram matrix. -/
def lineTauG (G : Mat3) : ℂ := ((lineChart G 2 : ℝ) : ℂ) + Complex.I * ((lineChart G 3 : ℝ) : ℂ)

theorem lineTauG_eq (G : Mat3) : lineTauG G = lineTau (lineChart G) := rfl

theorem contDiffOn_lineTauG : ContDiffOn ℝ ⊤ lineTauG lineDomain :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_lineChart 2)).add
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_lineChart 3)))

theorem lineTauG_im_pos {G : Mat3} (hG : G ∈ lineDomain) : 0 < (lineTauG G).im := by
  have : (lineTauG G).im = lineChart G 3 := by simp [lineTauG]
  rw [this, lineChart_eq]
  exact div_pos (Real.sqrt_pos.mpr hG.2.1) hG.1

namespace PotentialDatum

variable {n : ℕ} {F : ℂ → ℂ} (P : PotentialDatum n F)

/-- The potential along the line chart: `G ↦ A(τ(G))`. -/
def aFunLine (G : Mat3) : Fin (n + 2) → ℂ := fun j => P.A (lineTauG G) j

theorem contDiffOn_aFunLine : ContDiffOn ℝ ⊤ P.aFunLine lineDomain := by
  refine contDiffOn_pi.mpr fun j => ?_
  exact (P.contDiffOn_A j).comp contDiffOn_lineTauG (fun G hG => lineTauG_im_pos hG)

theorem hasFDerivAt_aFunLine {G : Mat3} (hG : G ∈ lineDomain) :
    HasFDerivAt P.aFunLine (ContinuousLinearMap.pi fun j =>
      (F (lineTauG G) * pointCoord n (lineTauG G) j) • fderiv ℝ lineTauG G) G := by
  have hd : HasFDerivAt lineTauG (fderiv ℝ lineTauG G) G :=
    ((contDiffOn_lineTauG.differentiableOn (by simp)).differentiableAt
      (isOpen_lineDomain.mem_nhds hG)).hasFDerivAt
  refine hasFDerivAt_pi'.mpr fun j => ?_
  have hA := (P.hasDeriv (lineTauG G) (lineTauG_im_pos hG) j).hasFDerivAt.restrictScalars ℝ
  refine (hA.comp G hd).congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro Q
  show (fderiv ℝ lineTauG G Q) • (F (lineTauG G) * pointCoord n (lineTauG G) j) =
    (F (lineTauG G) * pointCoord n (lineTauG G) j) • (fderiv ℝ lineTauG G Q)
  rw [smul_eq_mul, smul_eq_mul, mul_comm]

end PotentialDatum

/-- The tangent coordinate of the line chart in the direction `Q`. -/
def lineT (G Q : Mat3) (a : Fin 5) : ℝ := fderiv ℝ (fun G : Mat3 => lineChart G a) G Q

theorem fderiv_lineTauG_apply {G : Mat3} (hG : G ∈ lineDomain) (Q : Mat3) :
    fderiv ℝ lineTauG G Q = (lineT G Q 2 : ℂ) + Complex.I * (lineT G Q 3 : ℂ) := by
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp G (hasFDerivAt_lineChart hG 2)
  have h3 := (Complex.ofRealCLM.hasFDerivAt.comp G (hasFDerivAt_lineChart hG 3)).const_mul Complex.I
  have h := h2.add h3
  have h' : HasFDerivAt lineTauG (Complex.ofRealCLM ∘SL fderiv ℝ (fun G : Mat3 => lineChart G 2) G +
      Complex.I • Complex.ofRealCLM ∘SL fderiv ℝ (fun G : Mat3 => lineChart G 3) G) G := h
  rw [h'.fderiv]
  simp [lineT]

theorem fderiv_lFunLine_apply {G : Mat3} (hG : G ∈ lineDomain) (n : ℕ) (μ : Fin 3 →₀ ℕ) (Q : Mat3)
    (j : Fin (n + 2)) :
    fderiv ℝ (lFunLine n μ) G Q j = (lineT G Q 1 : ℂ) * cDer n 0 μ j - (lineT G Q 0 : ℂ) * cDer n 1 μ j := by
  have h1 := Complex.ofRealCLM.hasFDerivAt.comp G (hasFDerivAt_lineChart hG 1)
  have h0 := Complex.ofRealCLM.hasFDerivAt.comp G (hasFDerivAt_lineChart hG 0)
  have hj : HasFDerivAt (fun G : Mat3 => lFunLine n μ G j)
      ((cDer n 0 μ j) • (Complex.ofRealCLM ∘SL fderiv ℝ (fun G : Mat3 => lineChart G 1) G) -
        (cDer n 1 μ j) • (Complex.ofRealCLM ∘SL fderiv ℝ (fun G : Mat3 => lineChart G 0) G)) G := by
    have := (h1.mul_const (cDer n 0 μ j)).sub (h0.mul_const (cDer n 1 μ j))
    exact this
  have hv : HasFDerivAt (lFunLine n μ) (ContinuousLinearMap.pi fun j =>
      ((cDer n 0 μ j) • (Complex.ofRealCLM ∘SL fderiv ℝ (fun G : Mat3 => lineChart G 1) G) -
        (cDer n 1 μ j) • (Complex.ofRealCLM ∘SL fderiv ℝ (fun G : Mat3 => lineChart G 0) G))) G := by
    refine hasFDerivAt_pi'.mpr fun j => ?_
    have := (h1.mul_const (cDer n 0 μ j)).sub (h0.mul_const (cDer n 1 μ j))
    exact this
  rw [hv.fderiv]
  simp [lineT, mul_comm]

/-- The pairing of a coefficient-matrix two-form with two line-chart tangent vectors at a Gram matrix. -/
def lineFormPair (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (G Q₁ Q₂ : Mat3) :
    MvPolynomial (Fin 3) ℂ :=
  ∑ a : Fin 5, ∑ b : Fin 5, MvPolynomial.C ((lineT G Q₁ a * lineT G Q₂ b : ℝ) : ℂ) * ω (lineChart G) a b

theorem lineFormPair_lineSeedForm (n : ℕ) (h : ℂ → ℂ) (G Q₁ Q₂ : Mat3) :
    lineFormPair (lineSeedForm n h) G Q₁ Q₂ =
      MvPolynomial.C (h (lineTauG G) *
        ((lineTauG G * (lineT G Q₁ 0 : ℂ) + (lineT G Q₁ 1 : ℂ)) *
            ((lineT G Q₂ 2 : ℂ) + Complex.I * (lineT G Q₂ 3 : ℂ)) -
          (lineTauG G * (lineT G Q₂ 0 : ℂ) + (lineT G Q₂ 1 : ℂ)) *
            ((lineT G Q₁ 2 : ℂ) + Complex.I * (lineT G Q₁ 3 : ℂ)))) *
        (MvPolynomial.C (lineTauG G) * MvPolynomial.X 2 - MvPolynomial.X 1) ^ n := by
  have hterm : ∀ a b : Fin 5,
      MvPolynomial.C ((lineT G Q₁ a * lineT G Q₂ b : ℝ) : ℂ) * lineSeedForm n h (lineChart G) a b =
        MvPolynomial.C (h (lineTauG G) * (((lineT G Q₁ a * lineT G Q₂ b : ℝ) : ℂ) *
          ((![lineTauG G, 1, 0, 0, 0] : Fin 5 → ℂ) a * seedDTau b - (![lineTauG G, 1, 0, 0, 0] : Fin 5 → ℂ) b * seedDTau a))) *
        (MvPolynomial.C (lineTauG G) * MvPolynomial.X 2 - MvPolynomial.X 1) ^ n := by
    intro a b
    rw [lineSeedForm, ← lineTauG_eq, ← mul_assoc, ← MvPolynomial.C_mul]
    congr 2
    ring
  simp only [lineFormPair, hterm, ← Finset.sum_mul, ← map_sum, ← Finset.mul_sum]
  congr 3
  simp only [Fin.sum_univ_five, seedDTau, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

theorem derCoeff_pointPower_zero (n : ℕ) (μ : Fin 3 →₀ ℕ) (z : ℂ) :
    derCoeff n 0 μ (binaryPointPower (n + 1) z) =
      ((n + 1 : ℕ) : ℂ) * ((MvPolynomial.X 1 - MvPolynomial.C z * MvPolynomial.X 2 : Poly) ^ n).coeff μ := by
  rw [derCoeff_apply, binaryPointPower_val, pderiv0_pointPower, map_mul, rename_C, MvPolynomial.coeff_C_mul]
  simp [rename_X]

theorem derCoeff_pointPower_one (n : ℕ) (μ : Fin 3 →₀ ℕ) (z : ℂ) :
    derCoeff n 1 μ (binaryPointPower (n + 1) z) =
      -(((n + 1 : ℕ) : ℂ) * z) * ((MvPolynomial.X 1 - MvPolynomial.C z * MvPolynomial.X 2 : Poly) ^ n).coeff μ := by
  rw [derCoeff_apply, binaryPointPower_val, pderiv1_pointPower]
  have : rename (Fin.succ : Fin 2 → Fin 3) (-(MvPolynomial.C ((n + 1 : ℕ) : ℂ) * MvPolynomial.C z) *
      (MvPolynomial.X 0 - MvPolynomial.C z * MvPolynomial.X 1 : Binary.Poly) ^ n) =
      MvPolynomial.C (-(((n + 1 : ℕ) : ℂ) * z)) * (MvPolynomial.X 1 - MvPolynomial.C z * MvPolynomial.X 2 : Poly) ^ n := by
    simp only [map_mul, map_neg, rename_C, map_pow, map_sub, rename_X]
    simp
  rw [this, MvPolynomial.coeff_C_mul]

namespace PotentialDatum

variable {n : ℕ} {F : ℂ → ℂ} (P : PotentialDatum n F)

/-- **The cup form of the potential and the line radical is the line seed.**
`∑ⱼ [da_j(Q₁) dl_j(Q₂) - da_j(Q₂) dl_j(Q₁)] = coeff_μ σ_h(Q₁, Q₂)` with `h = (-1)^{n+1} (n+1) F`. -/
theorem cup_form_eq_seed_line (μ : Fin 3 →₀ ℕ) {G : Mat3} (hG : G ∈ lineDomain) (Q₁ Q₂ : Mat3) :
    ∑ j, (fderiv ℝ P.aFunLine G Q₁ j * fderiv ℝ (lFunLine n μ) G Q₂ j -
        fderiv ℝ P.aFunLine G Q₂ j * fderiv ℝ (lFunLine n μ) G Q₁ j) =
      (lineFormPair
        (lineSeedForm n (fun z => (-1) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) * F z)) G Q₁ Q₂).coeff μ := by
  have hB : ∀ B : Poly, (-B) ^ n = MvPolynomial.C ((-1 : ℂ) ^ n) * B ^ n := by
    intro B
    rw [neg_pow, map_pow, map_neg, map_one]
  have hK : (MvPolynomial.C (lineTauG G) * MvPolynomial.X 2 - MvPolynomial.X 1 : Poly) =
      -(MvPolynomial.X 1 - MvPolynomial.C (lineTauG G) * MvPolynomial.X 2) := by ring
  have e1 : ∀ Q j, fderiv ℝ P.aFunLine G Q j = F (lineTauG G) * pointCoord n (lineTauG G) j *
      ((lineT G Q 2 : ℂ) + Complex.I * (lineT G Q 3 : ℂ)) := by
    intro Q j
    rw [(P.hasFDerivAt_aFunLine hG).fderiv]
    simp only [ContinuousLinearMap.pi_apply, smul_apply, smul_eq_mul, fderiv_lineTauG_apply hG]
  have e2 : ∀ Q j, fderiv ℝ (lFunLine n μ) G Q j = (lineT G Q 1 : ℂ) * cDer n 0 μ j -
      (lineT G Q 0 : ℂ) * cDer n 1 μ j := fun Q j => fderiv_lFunLine_apply hG n μ Q j
  have hS : ∀ Q, ∑ j, pointCoord n (lineTauG G) j * fderiv ℝ (lFunLine n μ) G Q j =
      ((n + 1 : ℕ) : ℂ) * ((MvPolynomial.X 1 - MvPolynomial.C (lineTauG G) *
        MvPolynomial.X 2 : Poly) ^ n).coeff μ * (lineTauG G * (lineT G Q 0 : ℂ) + (lineT G Q 1 : ℂ)) := by
    intro Q
    have h0 := sum_pointCoord_cDer n 0 μ (lineTauG G)
    have h1 := sum_pointCoord_cDer n 1 μ (lineTauG G)
    rw [derCoeff_pointPower_zero] at h0
    rw [derCoeff_pointPower_one] at h1
    simp only [e2, mul_sub, Finset.sum_sub_distrib]
    have a1 : ∑ j, pointCoord n (lineTauG G) j * ((lineT G Q 1 : ℂ) * cDer n 0 μ j) =
        (lineT G Q 1 : ℂ) * ∑ j, pointCoord n (lineTauG G) j * cDer n 0 μ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have a2 : ∑ j, pointCoord n (lineTauG G) j * ((lineT G Q 0 : ℂ) * cDer n 1 μ j) =
        (lineT G Q 0 : ℂ) * ∑ j, pointCoord n (lineTauG G) j * cDer n 1 μ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [a1, a2, h0, h1]
    ring
  rw [lineFormPair_lineSeedForm, hK, hB, ← mul_assoc, ← MvPolynomial.C_mul, MvPolynomial.coeff_C_mul]
  have hsum : ∑ j, (fderiv ℝ P.aFunLine G Q₁ j * fderiv ℝ (lFunLine n μ) G Q₂ j -
        fderiv ℝ P.aFunLine G Q₂ j * fderiv ℝ (lFunLine n μ) G Q₁ j) =
      F (lineTauG G) * ((lineT G Q₁ 2 : ℂ) + Complex.I * (lineT G Q₁ 3 : ℂ)) *
        ∑ j, pointCoord n (lineTauG G) j * fderiv ℝ (lFunLine n μ) G Q₂ j -
      F (lineTauG G) * ((lineT G Q₂ 2 : ℂ) + Complex.I * (lineT G Q₂ 3 : ℂ)) *
        ∑ j, pointCoord n (lineTauG G) j * fderiv ℝ (lFunLine n μ) G Q₁ j := by
    simp only [e1, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, hS, hS]
  have hc : ((-1 : ℂ) ^ (n + 1)) * ((-1 : ℂ) ^ n) = -1 := by
    rw [pow_succ, mul_assoc, mul_comm (-1 : ℂ), ← mul_assoc, ← mul_pow]; simp
  set a : ℂ := ((n + 1 : ℕ) : ℂ) with ha
  set K : ℂ := ((MvPolynomial.X 1 - MvPolynomial.C (lineTauG G) * MvPolynomial.X 2 : Poly) ^ n).coeff μ
    with hKdef
  set f : ℂ := F (lineTauG G) with hf
  set b₁ : ℂ := lineTauG G * (lineT G Q₁ 0 : ℂ) + (lineT G Q₁ 1 : ℂ) with hb₁
  set b₂ : ℂ := lineTauG G * (lineT G Q₂ 0 : ℂ) + (lineT G Q₂ 1 : ℂ) with hb₂
  set d₁ : ℂ := (lineT G Q₁ 2 : ℂ) + Complex.I * (lineT G Q₁ 3 : ℂ) with hd₁
  set d₂ : ℂ := (lineT G Q₂ 2 : ℂ) + Complex.I * (lineT G Q₂ 3 : ℂ) with hd₂
  linear_combination (-(a * f * K * (b₁ * d₂ - b₂ * d₁))) * hc

end PotentialDatum

namespace PotentialDatum

variable {n : ℕ} {F : ℂ → ℂ} (P : PotentialDatum n F)

/-- **The cup / triangle bridge for the line source.** For `G₀, G₁, G₂` whose affine triangle lies in the
line-chart domain: the integral over the triangle of the line seed `σ_h`, `h = (-1)^{n+1} (n+1) F`, equals the cup
`∑ⱼ (a_j(G₁) - a_j(G₀)) (l_j(G₂) - l_j(G₁))` of the potential and the line radical plus the coboundary of the edge
cochain. -/
theorem line_cup_bridge (μ : Fin 3 →₀ ℕ) (G₀ G₁ G₂ : Mat3)
    (hT : ∀ p ∈ stdTriangle, affTri G₀ G₁ G₂ p ∈ lineDomain) :
    ∫ p in stdTriangle, (lineFormPair
        (lineSeedForm n (fun z => (-1) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) * F z))
          (affTri G₀ G₁ G₂ p) (G₁ - G₀) (G₂ - G₀)).coeff μ =
      ∑ j, (P.aFunLine G₁ j - P.aFunLine G₀ j) * (lFunLine n μ G₂ j - lFunLine n μ G₁ j) +
        cupEdge (dotPairing (n + 2)) P.aFunLine (lFunLine n μ) G₁ G₂ -
          cupEdge (dotPairing (n + 2)) P.aFunLine (lFunLine n μ) G₀ G₂ +
        cupEdge (dotPairing (n + 2)) P.aFunLine (lFunLine n μ) G₀ G₁ := by
  have key := cup_bridge (dotPairing (n + 2)) P.aFunLine (lFunLine n μ) lineDomain isOpen_lineDomain
    (P.contDiffOn_aFunLine.of_le (by simp)) ((contDiffOn_lFunLine n μ).of_le (by simp)) G₀ G₁ G₂ hT
  simp only [dotPairing_apply, Pi.sub_apply] at key
  rw [← key]
  refine setIntegral_congr_fun measurableSet_stdTriangle fun p hp => ?_
  have := P.cup_form_eq_seed_line μ (hT p hp) (G₁ - G₀) (G₂ - G₀)
  rw [← this, Finset.sum_sub_distrib]
  rfl

end PotentialDatum

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
