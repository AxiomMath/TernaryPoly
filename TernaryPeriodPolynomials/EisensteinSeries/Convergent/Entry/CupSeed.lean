module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.GramDomain
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RadicalPotential
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CupBridge

@[expose] public section


/-!
# The cup of the Eichler potential and the radical is the seed form

For a vector potential `A` on the upper half plane whose coordinates are primitives of
`F(z) · pointCoord n z j` (`PotentialDatum`; the Eichler potential of a holomorphic `F`), the coordinates
`a_j(G) = A(τ(G))_j` and `l_j(G) = coeff_μ R(u(G)) (basis j)` along the plane chart of a Gram matrix `G`
satisfy, for symmetric directions,
`∑ⱼ [da_j(Q₁) dl_j(Q₂) - da_j(Q₂) dl_j(Q₁)] = coeff_μ ω_h(Q₁, Q₂)` with the seed `ω_h = h(τ) 𝓑ⁿ β ∧ dτ`,
`h = (-1)ⁿ (n+1) F` (`cup_form_eq_seed`): the chain rule in the chart coordinates `(u, τ)` and the derivative of
the radical on a point power.  With the cup/triangle bridge this gives `plane_cup_bridge`: the integral of the seed
over an affine triangle of Gram matrices is the plane-source cup plus the coboundary of the edge cochain.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- A vector-valued potential whose coordinates are primitives of `F(z) · pointCoord n z j`. -/
structure PotentialDatum (n : ℕ) (F : ℂ → ℂ) where
  A : ℂ → Fin (n + 2) → ℂ
  hasDeriv : ∀ z : ℂ, 0 < z.im → ∀ j, HasDerivAt (fun w => A w j) (F z * pointCoord n z j) z

theorem gramPlaneTau_eq_chart (G : Mat3) :
    gramPlaneTau G = ((gramChart G 2 : ℝ) : ℂ) + Complex.I * ((gramChart G 3 : ℝ) : ℂ) := by
  simp only [gramChart, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  rw [mul_comm]
  exact (Complex.re_add_im _).symm

theorem gramPlaneTau_im_pos_of_domain {G : Mat3} (hG : G ∈ gramDomain) : 0 < (gramPlaneTau G).im := by
  rw [gramChart_im_tau]
  exact div_pos (Real.sqrt_pos.mpr hG.2.2) hG.2.1

theorem contDiffOn_gramPlaneTau :
    ContDiffOn ℝ ⊤ gramPlaneTau gramDomain := by
  have h2 := (contDiffOn_gramChart 2)
  have h3 := (contDiffOn_gramChart 3)
  have := (Complex.ofRealCLM.contDiff.comp_contDiffOn h2).add
    ((contDiffOn_const (c := Complex.I)).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn h3))
  refine this.congr fun G _ => ?_
  simpa using gramPlaneTau_eq_chart G

theorem line_hasDerivAt_entries (G Q : Mat3) (i j : Fin 3) :
    HasDerivAt (fun ε : ℝ => (G + ε • Q) i j) (Q i j) 0 := by
  have : (fun ε : ℝ => (G + ε • Q) i j) = fun ε => G i j + ε * Q i j := by
    funext ε; simp
  rw [this]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Q i j)).const_add (G i j)

theorem line_isSymm (G Q : Mat3) (hGs : G.IsSymm) (hQs : Q.IsSymm) (ε : ℝ) : (G + ε • Q).IsSymm := by
  unfold Matrix.IsSymm at *
  rw [Matrix.transpose_add, Matrix.transpose_smul, hGs, hQs]

theorem line_hasDerivAt (G Q : Mat3) : HasDerivAt (fun ε : ℝ => G + ε • Q) Q 0 := by
  have := ((hasDerivAt_id (0 : ℝ)).smul_const Q).const_add G
  convert this using 1 <;> first | rfl | simp

theorem fderiv_gramPlaneTau_apply (G Q : Mat3) (hGs : G.IsSymm) (hQs : Q.IsSymm) (hG : G ∈ gramDomain) :
    fderiv ℝ gramPlaneTau G Q = planeDTau G Q := by
  have hd : DifferentiableAt ℝ gramPlaneTau G :=
    (contDiffOn_gramPlaneTau.differentiableOn (by simp)).differentiableAt (isOpen_gramDomain.mem_nhds hG)
  have h0 : G + (0 : ℝ) • Q = G := by simp
  have hF : HasFDerivAt gramPlaneTau (fderiv ℝ gramPlaneTau G) (G + (0 : ℝ) • Q) := by
    rw [h0]; exact hd.hasFDerivAt
  have h1 := hF.comp_hasDerivAt (0 : ℝ) (line_hasDerivAt G Q)
  have hR : 0 < (G + (0 : ℝ) • Q) 2 2 := by rw [h0]; exact hG.1
  have h11 : 0 < gramSchur (G + (0 : ℝ) • Q) 1 1 := by rw [h0]; exact hG.2.1
  have hdet : 0 < (gramSchur (G + (0 : ℝ) • Q)).det := by rw [h0]; exact hG.2.2
  have h2 := hasDerivAt_gramPlaneTau (fun ε : ℝ => G + ε • Q) Q (line_isSymm G Q hGs hQs)
    (line_hasDerivAt_entries G Q) hR h11 hdet
  simp only [h0] at h2
  exact h1.unique h2


namespace PotentialDatum

variable {n : ℕ} {F : ℂ → ℂ} (P : PotentialDatum n F)

/-- The potential along the plane chart: `G ↦ A(τ(G))`. -/
def aFun (G : Mat3) : Fin (n + 2) → ℂ := fun j => P.A (gramPlaneTau G) j

theorem differentiableOn_A (j : Fin (n + 2)) :
    DifferentiableOn ℂ (fun w => P.A w j) {z : ℂ | 0 < z.im} := fun z hz =>
  (P.hasDeriv z hz j).differentiableAt.differentiableWithinAt

theorem contDiffOn_A (j : Fin (n + 2)) :
    ContDiffOn ℝ ⊤ (fun w => P.A w j) {z : ℂ | 0 < z.im} :=
  ((P.differentiableOn_A j).contDiffOn (isOpen_lt continuous_const Complex.continuous_im)).restrict_scalars ℝ

theorem contDiffOn_aFun : ContDiffOn ℝ ⊤ P.aFun gramDomain := by
  refine contDiffOn_pi.mpr fun j => ?_
  exact (P.contDiffOn_A j).comp contDiffOn_gramPlaneTau
    (fun G hG => gramPlaneTau_im_pos_of_domain hG)

theorem hasFDerivAt_aFun {G : Mat3} (hG : G ∈ gramDomain) :
    HasFDerivAt P.aFun (ContinuousLinearMap.pi fun j =>
      (F (gramPlaneTau G) * pointCoord n (gramPlaneTau G) j) • fderiv ℝ gramPlaneTau G) G := by
  have hd : HasFDerivAt gramPlaneTau (fderiv ℝ gramPlaneTau G) G :=
    ((contDiffOn_gramPlaneTau.differentiableOn (by simp)).differentiableAt
      (isOpen_gramDomain.mem_nhds hG)).hasFDerivAt
  refine hasFDerivAt_pi'.mpr fun j => ?_
  have hA := (P.hasDeriv (gramPlaneTau G) (gramPlaneTau_im_pos_of_domain hG) j).hasFDerivAt.restrictScalars ℝ
  refine (hA.comp G hd).congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro Q
  show (fderiv ℝ gramPlaneTau G Q) • (F (gramPlaneTau G) * pointCoord n (gramPlaneTau G) j) =
    (F (gramPlaneTau G) * pointCoord n (gramPlaneTau G) j) • (fderiv ℝ gramPlaneTau G Q)
  rw [smul_eq_mul, smul_eq_mul, mul_comm]

theorem fderiv_aFun_apply {G : Mat3} (hG : G ∈ gramDomain) (hGs : G.IsSymm) (Q : Mat3) (hQs : Q.IsSymm)
    (j : Fin (n + 2)) :
    fderiv ℝ P.aFun G Q j = F (gramPlaneTau G) * pointCoord n (gramPlaneTau G) j * planeDTau G Q := by
  rw [(P.hasFDerivAt_aFun hG).fderiv]
  simp only [ContinuousLinearMap.pi_apply, smul_apply, smul_eq_mul,
    fderiv_gramPlaneTau_apply G Q hGs hQs hG]

end PotentialDatum

/-- The radical coefficients along the plane chart: `G ↦ (coeff_μ R(u(G)) (basis j))_j`. -/
def lFun (n : ℕ) (μ : Fin 3 →₀ ℕ) (G : Mat3) : Fin (n + 2) → ℂ :=
  fun j => radicalCoeff n (binaryWeightBasis (n + 1) j) μ (gramPlaneU G)

theorem contDiffOn_lFun (n : ℕ) (μ : Fin 3 →₀ ℕ) : ContDiffOn ℝ ⊤ (lFun n μ) gramDomain := by
  refine contDiffOn_pi.mpr fun j => ?_
  have hu : ContDiffOn ℝ ⊤ (fun G : Mat3 => gramPlaneU G) gramDomain := by
    refine ContDiffOn.prodMk ?_ ?_
    · exact contDiffOn_gramChart 0
    · exact contDiffOn_gramChart 1
  exact (contDiff_radicalCoeff n _ μ).comp_contDiffOn hu

theorem hasFDerivAt_gramPlaneU {G : Mat3} (hG : G ∈ gramDomain) :
    HasFDerivAt gramPlaneU ((fderiv ℝ (fun G : Mat3 => gramChart G 0) G).prod
      (fderiv ℝ (fun G : Mat3 => gramChart G 1) G)) G :=
  (hasFDerivAt_gramChart G hG 0).prodMk (hasFDerivAt_gramChart G hG 1)

theorem hasFDerivAt_lFun (n : ℕ) (μ : Fin 3 →₀ ℕ) {G : Mat3} (hG : G ∈ gramDomain) :
    HasFDerivAt (lFun n μ) (ContinuousLinearMap.pi fun j =>
      (fderiv ℝ (radicalCoeff n (binaryWeightBasis (n + 1) j) μ) (gramPlaneU G)).comp
        ((fderiv ℝ (fun G : Mat3 => gramChart G 0) G).prod
          (fderiv ℝ (fun G : Mat3 => gramChart G 1) G))) G := by
  refine hasFDerivAt_pi'.mpr fun j => ?_
  exact ((differentiableAt_radicalCoeff n _ μ (gramPlaneU G)).hasFDerivAt).comp G (hasFDerivAt_gramPlaneU hG)

theorem fderiv_lFun_sum (n : ℕ) (μ : Fin 3 →₀ ℕ) {G : Mat3} (hG : G ∈ gramDomain) (hGs : G.IsSymm)
    (Q : Mat3) (hQs : Q.IsSymm) :
    ∑ j, pointCoord n (gramPlaneTau G) j * fderiv ℝ (lFun n μ) G Q j =
      (-((n + 1 : ℕ) : ℂ) * ((pointPowerTernary (gramPlaneTau G) -
        MvPolynomial.C (((gramPlaneU G).1 : ℂ) - gramPlaneTau G * ((gramPlaneU G).2 : ℂ)) *
          MvPolynomial.X 2) ^ n).coeff μ) *
        ((planeTangent G Q 0 : ℂ) - gramPlaneTau G * (planeTangent G Q 1 : ℂ)) := by
  rw [(hasFDerivAt_lFun n μ hG).fderiv]
  have h := sum_fderiv_radicalCoeff n (gramPlaneTau G) μ (gramPlaneU G)
    (planeTangent G Q 0, planeTangent G Q 1)
  rw [radLin_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderiv_gramChart_apply G Q hGs hQs hG]

/-- `ω(T₁, T₂)` for a coefficient-matrix two-form, on two chart tangent vectors. -/
def formPair (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (G Q₁ Q₂ : Mat3) :
    MvPolynomial (Fin 3) ℂ :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.C ((planeTangent G Q₁ a * planeTangent G Q₂ b : ℝ) : ℂ) * ω (gramChart G) a b

theorem planeDTau_eq (G Q : Mat3) :
    planeDTau G Q = (planeTangent G Q 2 : ℂ) + Complex.I * (planeTangent G Q 3 : ℂ) := by
  simp only [planeTangent, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  rw [mul_comm]
  exact (Complex.re_add_im _).symm

theorem formPair_seedForm (n : ℕ) (h : ℂ → ℂ) (G Q₁ Q₂ : Mat3) :
    formPair (seedForm n h) G Q₁ Q₂ =
      MvPolynomial.C (h (gramPlaneTau G) *
        (((planeTangent G Q₁ 0 : ℂ) - gramPlaneTau G * (planeTangent G Q₁ 1 : ℂ)) * planeDTau G Q₂ -
          ((planeTangent G Q₂ 0 : ℂ) - gramPlaneTau G * (planeTangent G Q₂ 1 : ℂ)) * planeDTau G Q₁)) *
        seedLinear (gramChart G) ^ n := by
  have hterm : ∀ a b : Fin 5,
      MvPolynomial.C ((planeTangent G Q₁ a * planeTangent G Q₂ b : ℝ) : ℂ) *
          seedForm n h (gramChart G) a b =
        MvPolynomial.C (h (gramPlaneTau G) *
            (((planeTangent G Q₁ a * planeTangent G Q₂ b : ℝ) : ℂ) *
              (seedBeta (gramChart G) a * seedDTau b - seedBeta (gramChart G) b * seedDTau a))) *
          seedLinear (gramChart G) ^ n := by
    intro a b
    rw [seedForm, seedTau_gramChart_eq, ← mul_assoc, ← MvPolynomial.C_mul]
    congr 2
    ring
  simp only [formPair, hterm, ← Finset.sum_mul, ← map_sum, ← Finset.mul_sum]
  congr 3
  rw [planeDTau_eq, planeDTau_eq]
  simp only [Fin.sum_univ_five, seedBeta, seedDTau, seedTau_gramChart_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

theorem seedLinear_eq_neg (G : Mat3) :
    seedLinear (gramChart G) = -(pointPowerTernary (gramPlaneTau G) -
      MvPolynomial.C (((gramPlaneU G).1 : ℂ) - gramPlaneTau G * ((gramPlaneU G).2 : ℂ)) *
        MvPolynomial.X 2) := by
  have h0 : gramChart G 0 = (gramPlaneU G).1 := by simp [gramChart]
  have h1 : gramChart G 1 = (gramPlaneU G).2 := by simp [gramChart]
  unfold seedLinear
  rw [seedTau_gramChart_eq, h0, h1]
  unfold pointPowerTernary
  simp only [map_sub, map_mul]
  ring

namespace PotentialDatum

variable {n : ℕ} {F : ℂ → ℂ} (P : PotentialDatum n F)

/-- **The cup form of the potential and the radical is the seed.** For `G` in the plane-chart domain and
symmetric directions `Q₁, Q₂`:
`∑ⱼ [da_j(Q₁) dl_j(Q₂) - da_j(Q₂) dl_j(Q₁)] = coeff_μ ω_h(Q₁, Q₂)` with `h = (-1)ⁿ (n+1) F`. -/
theorem cup_form_eq_seed (μ : Fin 3 →₀ ℕ) {G : Mat3} (hG : G ∈ gramDomain) (hGs : G.IsSymm)
    (Q₁ Q₂ : Mat3) (hQ₁ : Q₁.IsSymm) (hQ₂ : Q₂.IsSymm) :
    ∑ j, (fderiv ℝ P.aFun G Q₁ j * fderiv ℝ (lFun n μ) G Q₂ j -
        fderiv ℝ P.aFun G Q₂ j * fderiv ℝ (lFun n μ) G Q₁ j) =
      (formPair (seedForm n (fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) * F z)) G Q₁ Q₂).coeff μ := by
  have hB : ∀ B : MvPolynomial (Fin 3) ℂ, (-B) ^ n = MvPolynomial.C ((-1 : ℂ) ^ n) * B ^ n := by
    intro B
    rw [neg_pow, map_pow, map_neg, map_one]
  rw [formPair_seedForm, seedLinear_eq_neg, hB, ← mul_assoc, ← MvPolynomial.C_mul,
    MvPolynomial.coeff_C_mul]
  have e1 : ∀ j, fderiv ℝ P.aFun G Q₁ j = F (gramPlaneTau G) * pointCoord n (gramPlaneTau G) j *
      planeDTau G Q₁ := fun j => P.fderiv_aFun_apply hG hGs Q₁ hQ₁ j
  have e2 : ∀ j, fderiv ℝ P.aFun G Q₂ j = F (gramPlaneTau G) * pointCoord n (gramPlaneTau G) j *
      planeDTau G Q₂ := fun j => P.fderiv_aFun_apply hG hGs Q₂ hQ₂ j
  have s1 := fderiv_lFun_sum n μ hG hGs Q₁ hQ₁
  have s2 := fderiv_lFun_sum n μ hG hGs Q₂ hQ₂
  simp only [e1, e2]
  have : ∑ j, (F (gramPlaneTau G) * pointCoord n (gramPlaneTau G) j * planeDTau G Q₁ *
        fderiv ℝ (lFun n μ) G Q₂ j -
      F (gramPlaneTau G) * pointCoord n (gramPlaneTau G) j * planeDTau G Q₂ *
        fderiv ℝ (lFun n μ) G Q₁ j) =
      F (gramPlaneTau G) * planeDTau G Q₁ * ∑ j, pointCoord n (gramPlaneTau G) j *
        fderiv ℝ (lFun n μ) G Q₂ j -
      F (gramPlaneTau G) * planeDTau G Q₂ * ∑ j, pointCoord n (gramPlaneTau G) j *
        fderiv ℝ (lFun n μ) G Q₁ j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this, s1, s2]
  have hc : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by rw [← mul_pow]; simp
  linear_combination (-(((n + 1 : ℕ) : ℂ) * F (gramPlaneTau G) *
      (((pointPowerTernary (gramPlaneTau G) -
        MvPolynomial.C (((gramPlaneU G).1 : ℂ) - gramPlaneTau G * ((gramPlaneU G).2 : ℂ)) *
          MvPolynomial.X 2) ^ n).coeff μ) *
      (((planeTangent G Q₁ 0 : ℂ) - gramPlaneTau G * (planeTangent G Q₁ 1 : ℂ)) * planeDTau G Q₂ -
          ((planeTangent G Q₂ 0 : ℂ) - gramPlaneTau G * (planeTangent G Q₂ 1 : ℂ)) * planeDTau G Q₁))) * hc

end PotentialDatum

namespace PotentialDatum

variable {n : ℕ} {F : ℂ → ℂ} (P : PotentialDatum n F)

/-- The pairing `(a, ℓ) ↦ ∑ⱼ aⱼ ℓⱼ`. -/
def dotPairing (N : ℕ) : (Fin N → ℂ) →L[ℝ] (Fin N → ℂ) →L[ℝ] ℂ :=
  ∑ j : Fin N, ((ContinuousLinearMap.mul ℝ ℂ).bilinearComp (ContinuousLinearMap.proj j) (ContinuousLinearMap.proj j))

theorem dotPairing_apply (N : ℕ) (a ℓ : Fin N → ℂ) : dotPairing N a ℓ = ∑ j, a j * ℓ j := by
  simp [dotPairing, sum_apply]

/-- **The cup / triangle bridge for the plane source.** For symmetric Gram matrices `G₀, G₁, G₂` whose affine
triangle lies in the plane-chart domain: the integral over the triangle of the seed form `ω_h`,
`h = (-1)ⁿ (n+1) F`, equals the cup `∑ⱼ (a_j(G₁) - a_j(G₀)) (l_j(G₂) - l_j(G₁))` of the potential and the radical
(the plane source cochain) plus the coboundary of the edge cochain `B`. -/
theorem plane_cup_bridge (μ : Fin 3 →₀ ℕ) (G₀ G₁ G₂ : Mat3) (h₀ : G₀.IsSymm) (h₁ : G₁.IsSymm)
    (h₂ : G₂.IsSymm) (hT : ∀ p ∈ stdTriangle, affTri G₀ G₁ G₂ p ∈ gramDomain) :
    ∫ p in stdTriangle, (formPair
        (seedForm n (fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) * F z)) (affTri G₀ G₁ G₂ p) (G₁ - G₀) (G₂ - G₀)).coeff μ =
      ∑ j, (P.aFun G₁ j - P.aFun G₀ j) * (lFun n μ G₂ j - lFun n μ G₁ j) +
        cupEdge (dotPairing (n + 2)) P.aFun (lFun n μ) G₁ G₂ -
          cupEdge (dotPairing (n + 2)) P.aFun (lFun n μ) G₀ G₂ +
        cupEdge (dotPairing (n + 2)) P.aFun (lFun n μ) G₀ G₁ := by
  have key := cup_bridge (dotPairing (n + 2)) P.aFun (lFun n μ) gramDomain isOpen_gramDomain
    (P.contDiffOn_aFun.of_le (by simp)) ((contDiffOn_lFun n μ).of_le (by simp)) G₀ G₁ G₂ hT
  have hS : ∀ p ∈ stdTriangle, (affTri G₀ G₁ G₂ p).IsSymm := by
    intro p _
    unfold affTri Matrix.IsSymm at *
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sub, h₀, h₁, h₂]
  simp only [dotPairing_apply, Pi.sub_apply] at key
  rw [← key]
  refine setIntegral_congr_fun measurableSet_stdTriangle fun p hp => ?_
  have := P.cup_form_eq_seed μ (hT p hp) (hS p hp) (G₁ - G₀) (G₂ - G₀)
    (by unfold Matrix.IsSymm at *; simp [Matrix.transpose_sub, h₀, h₁]) (by unfold Matrix.IsSymm at *; simp [Matrix.transpose_sub, h₀, h₂])
  rw [← this, Finset.sum_sub_distrib]
  rfl

end PotentialDatum

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
