module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Uniform
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.IwasawaChart

@[expose] public section


/-!
# Joint continuity of the twisted pullback in the translation and the simplex parameter

`continuousOn_twPull_joint`: for a Gram triangle in the Cholesky domain, the coefficient
`(s,t,p) ↦ coeff_κ twPull ω L_{s,t} P_p Q₁ Q₂` is continuous on `ℝ² × Δ`.  The tangent coordinates `planeTangent`
are continuous on pairs of symmetric matrices (`continuousOn_planeTangent`, from the `C¹` smoothness of the chart),
the coefficients of the seed pair are explicit (`coeff_seedLinear_pow`, `continuousOn_coeff_formPair`), and the
coefficient action `ρ(L)⁻¹` is a finite combination (homogeneity) of continuous functions
(`RhoContinuity`).  This provides the measurability needed for the Fubini exchange.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- Pairs of symmetric matrices with the first in the plane-chart domain. -/
def pairDomain : Set (Mat3 × Mat3) := {x | x.1 ∈ gramDomain ∧ x.1ᵀ = x.1 ∧ x.2ᵀ = x.2}

theorem continuousOn_planeTangent (a : Fin 5) :
    ContinuousOn (fun x : Mat3 × Mat3 => planeTangent x.1 x.2 a) pairDomain := by
  have hfd : ContinuousOn (fderiv ℝ (fun G : Mat3 => gramChart G a)) gramDomain :=
    (contDiffOn_gramChart a).continuousOn_fderiv_of_isOpen isOpen_gramDomain (by simp)
  have h1 : ContinuousOn (fun x : Mat3 × Mat3 => fderiv ℝ (fun G : Mat3 => gramChart G a) x.1 x.2)
      (gramDomain ×ˢ Set.univ) :=
    ContinuousOn.clm_apply (hfd.comp continuousOn_fst (fun x hx => hx.1)) continuousOn_snd
  refine (h1.mono fun x hx => ⟨hx.1, Set.mem_univ _⟩).congr fun x hx => ?_
  exact (fderiv_gramChart_apply x.1 x.2 hx.2.1 hx.2.2 hx.1 a).symm

theorem coeff_seedLinear_pow (G : Mat3) (n : ℕ) (ν : Fin 3 →₀ ℕ) :
    (seedLinear (gramChart G) ^ n).coeff ν =
      if ν.sum (fun _ k => k) = n then
        (ν.multinomial : ℂ) * ((-1) ^ (ν 0) * gramPlaneTau G ^ (ν 1) *
          (((gramPlaneU G).1 : ℂ) - gramPlaneTau G * ((gramPlaneU G).2 : ℂ)) ^ (ν 2)) else 0 := by
  have h0 : gramChart G 0 = (gramPlaneU G).1 := by simp [gramChart]
  have h1 : gramChart G 1 = (gramPlaneU G).2 := by simp [gramChart]
  have hform : seedLinear (gramChart G) = C (-1 : ℂ) * X 0 + C (gramPlaneTau G) * X 1 +
      C (((gramPlaneU G).1 : ℂ) - gramPlaneTau G * ((gramPlaneU G).2 : ℂ)) * X 2 := by
    unfold seedLinear
    rw [seedTau_gramChart_eq, h0, h1]
    simp only [map_neg, map_one]
    ring
  rw [hform, coeff_linForm_pow]

theorem continuousOn_coeff_formPair (n : ℕ) (h : ℂ → ℂ)
    (hh : ContinuousOn h {z : ℂ | 0 < z.im}) (ν : Fin 3 →₀ ℕ) :
    ContinuousOn (fun x : Mat3 × Mat3 × Mat3 =>
      (formPair (seedForm n h) x.1 x.2.1 x.2.2).coeff ν)
      {x | (x.1, x.2.1) ∈ pairDomain ∧ x.2.2ᵀ = x.2.2} := by
  set S : Set (Mat3 × Mat3 × Mat3) := {x | (x.1, x.2.1) ∈ pairDomain ∧ x.2.2ᵀ = x.2.2} with hS
  have hG : ∀ x ∈ S, x.1 ∈ gramDomain := fun x hx => hx.1.1
  have hτ : ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => gramPlaneTau x.1) S :=
    contDiffOn_gramPlaneTau.continuousOn.comp continuousOn_fst hG
  have hu1 : ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => ((gramPlaneU x.1).1 : ℂ)) S := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact (contDiffOn_gramChart 0).continuousOn.comp continuousOn_fst hG
  have hu2 : ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => ((gramPlaneU x.1).2 : ℂ)) S := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact (contDiffOn_gramChart 1).continuousOn.comp continuousOn_fst hG
  have hT1 : ∀ a : Fin 5, ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => planeTangent x.1 x.2.1 a) S := by
    intro a
    refine (continuousOn_planeTangent a).comp (continuousOn_fst.prodMk (continuous_fst.comp continuous_snd).continuousOn)
      (fun x hx => hx.1)
  have hT2 : ∀ a : Fin 5, ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => planeTangent x.1 x.2.2 a) S := by
    intro a
    refine (continuousOn_planeTangent a).comp (continuousOn_fst.prodMk (continuous_snd.comp continuous_snd).continuousOn)
      (fun x hx => ⟨hx.1.1, hx.1.2.1, hx.2⟩)
  have hhτ : ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => h (gramPlaneTau x.1)) S :=
    hh.comp hτ (fun x hx => gramPlaneTau_im_pos_of_domain (hG x hx))
  have hre : ∀ a : Fin 5, ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => (planeTangent x.1 x.2.1 a : ℂ)) S :=
    fun a => Complex.continuous_ofReal.comp_continuousOn (hT1 a)
  have hre' : ∀ a : Fin 5, ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => (planeTangent x.1 x.2.2 a : ℂ)) S :=
    fun a => Complex.continuous_ofReal.comp_continuousOn (hT2 a)
  have hdτ1 : ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => planeDTau x.1 x.2.1) S := by
    simp_rw [planeDTau_eq]
    exact (hre 2).add (continuousOn_const.mul (hre 3))
  have hdτ2 : ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => planeDTau x.1 x.2.2) S := by
    simp_rw [planeDTau_eq]
    exact (hre' 2).add (continuousOn_const.mul (hre' 3))
  have hβ1 : ContinuousOn (fun x : Mat3 × Mat3 × Mat3 =>
      (planeTangent x.1 x.2.1 0 : ℂ) - gramPlaneTau x.1 * (planeTangent x.1 x.2.1 1 : ℂ)) S :=
    (hre 0).sub (hτ.mul (hre 1))
  have hβ2 : ContinuousOn (fun x : Mat3 × Mat3 × Mat3 =>
      (planeTangent x.1 x.2.2 0 : ℂ) - gramPlaneTau x.1 * (planeTangent x.1 x.2.2 1 : ℂ)) S :=
    (hre' 0).sub (hτ.mul (hre' 1))
  have hc : ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => h (gramPlaneTau x.1) *
      ((((planeTangent x.1 x.2.1 0 : ℂ) - gramPlaneTau x.1 * (planeTangent x.1 x.2.1 1 : ℂ)) *
        planeDTau x.1 x.2.2) -
        ((planeTangent x.1 x.2.2 0 : ℂ) - gramPlaneTau x.1 * (planeTangent x.1 x.2.2 1 : ℂ)) *
          planeDTau x.1 x.2.1)) S :=
    hhτ.mul ((hβ1.mul hdτ2).sub (hβ2.mul hdτ1))
  have hfun : (fun x : Mat3 × Mat3 × Mat3 => (formPair (seedForm n h) x.1 x.2.1 x.2.2).coeff ν) =
      fun x => h (gramPlaneTau x.1) *
      ((((planeTangent x.1 x.2.1 0 : ℂ) - gramPlaneTau x.1 * (planeTangent x.1 x.2.1 1 : ℂ)) *
        planeDTau x.1 x.2.2) -
        ((planeTangent x.1 x.2.2 0 : ℂ) - gramPlaneTau x.1 * (planeTangent x.1 x.2.2 1 : ℂ)) *
          planeDTau x.1 x.2.1) *
      (if ν.sum (fun _ k => k) = n then
        (ν.multinomial : ℂ) * ((-1) ^ (ν 0) * gramPlaneTau x.1 ^ (ν 1) *
          (((gramPlaneU x.1).1 : ℂ) - gramPlaneTau x.1 * ((gramPlaneU x.1).2 : ℂ)) ^ (ν 2)) else 0) := by
    funext x
    rw [formPair_seedForm, MvPolynomial.coeff_C_mul, coeff_seedLinear_pow]
  rw [hfun]
  refine hc.mul ?_
  split_ifs
  · exact continuousOn_const.mul (((continuousOn_const.pow _).mul (hτ.pow _)).mul
      ((hu1.sub (hτ.mul hu2)).pow _))
  · exact continuousOn_const

theorem continuousOn_coeff_formPair_comp {X : Type*} [TopologicalSpace X] {S : Set X} (n : ℕ) (h : ℂ → ℂ)
    (hh : ContinuousOn h {z : ℂ | 0 < z.im}) (G Q₁ Q₂ : X → Mat3) (hG : ContinuousOn G S)
    (hQ₁ : ContinuousOn Q₁ S) (hQ₂ : ContinuousOn Q₂ S)
    (hmem : ∀ x ∈ S, G x ∈ gramDomain ∧ (G x)ᵀ = G x ∧ (Q₁ x)ᵀ = Q₁ x ∧ (Q₂ x)ᵀ = Q₂ x)
    (ν : Fin 3 →₀ ℕ) :
    ContinuousOn (fun x => (formPair (seedForm n h) (G x) (Q₁ x) (Q₂ x)).coeff ν) S := by
  have hB := continuousOn_coeff_formPair n h hh ν
  have hA : ContinuousOn (fun x => (G x, Q₁ x, Q₂ x)) S := hG.prodMk (hQ₁.prodMk hQ₂)
  have hmap : Set.MapsTo (fun x => (G x, Q₁ x, Q₂ x)) S
      {x : Mat3 × Mat3 × Mat3 | (x.1, x.2.1) ∈ pairDomain ∧ x.2.2ᵀ = x.2.2} := by
    intro x hx
    obtain ⟨a, b, c, d⟩ := hmem x hx
    exact ⟨⟨a, b, c⟩, d⟩
  have hC := hB.comp hA hmap
  simpa only [Function.comp_def] using hC

theorem continuous_entryFrame : Continuous (fun st : ℝ × ℝ => entryFrame st.1 st.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [entryFrame, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one,
      Matrix.empty_val', Matrix.head_cons, Matrix.tail_cons] <;>
    first | exact continuous_const | exact continuous_fst | exact continuous_snd

theorem continuousOn_twPull_joint (n : ℕ) (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im})
    (Γ₀ Γ₁ Γ₂ : Mat3) (h₀ : Γ₀ᵀ = Γ₀) (h₁ : Γ₁ᵀ = Γ₁) (h₂ : Γ₂ᵀ = Γ₂)
    (hcond : ∀ p ∈ stdTriangle, affTri Γ₀ Γ₁ Γ₂ p ∈ cholDomain) (κ : Fin 3 →₀ ℕ) :
    ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (twPull (seedForm n h) (entryFrame z.1.1 z.1.2) (affTri Γ₀ Γ₁ Γ₂ z.2) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ)
      (Set.univ ×ˢ stdTriangle) := by
  set Pf : ℝ × ℝ → Mat3 := affTri Γ₀ Γ₁ Γ₂ with hPf
  have hQ₁ : (Γ₁ - Γ₀)ᵀ = Γ₁ - Γ₀ := by rw [Matrix.transpose_sub, h₀, h₁]
  have hQ₂ : (Γ₂ - Γ₀)ᵀ = Γ₂ - Γ₀ := by rw [Matrix.transpose_sub, h₀, h₂]
  have hPs : ∀ p, (Pf p)ᵀ = Pf p := by
    intro p
    simp only [hPf, affTri, Matrix.transpose_add, Matrix.transpose_smul, hQ₁, hQ₂, h₀]
  obtain ⟨L, hLdef⟩ : ∃ L : (ℝ × ℝ) × (ℝ × ℝ) → Mat3, L = fun z => entryFrame z.1.1 z.1.2 := ⟨_, rfl⟩
  have hLdet : ∀ z, (L z).det = 1 := fun z => by rw [hLdef]; exact entryFrame_det_eq z.1.1 z.1.2
  have hLc : Continuous L := by rw [hLdef]; exact continuous_entryFrame.comp (continuous_fst)
  have hLinv : ContinuousOn (fun z => (L z)⁻¹) (Set.univ ×ˢ stdTriangle) :=
    continuousOn_matInv.comp hLc.continuousOn (fun z _ => by simp [hLdet])
  have hPc : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => Pf z.2) :=
    (continuous_affTri Γ₀ Γ₁ Γ₂).comp continuous_snd
  have hcong : ∀ (A : Mat3), ContinuousOn (fun z => L z * A * (L z)ᵀ)
      (Set.univ ×ˢ stdTriangle) := fun A => by
    exact continuousOn_matrix_mul' (continuousOn_matrix_mul' hLc.continuousOn continuousOn_const)
      (continuousOn_matrix_transpose' hLc.continuousOn)
  have hG : ContinuousOn (fun z => L z * Pf z.2 * (L z)ᵀ) (Set.univ ×ˢ stdTriangle) :=
    continuousOn_matrix_mul' (continuousOn_matrix_mul' hLc.continuousOn hPc.continuousOn)
      (continuousOn_matrix_transpose' hLc.continuousOn)
  have hsymL : ∀ (A : Mat3), Aᵀ = A → ∀ z, (L z * A * (L z)ᵀ)ᵀ = L z * A * (L z)ᵀ := by
    intro A hA z
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA, Matrix.mul_assoc]
  have hGdom : ∀ z ∈ Set.univ ×ˢ stdTriangle, L z * Pf z.2 * (L z)ᵀ ∈ gramDomain := by
    intro z hz
    have hP := hcond z.2 hz.2
    obtain ⟨hs, hD, hdet⟩ := hP
    have hqP : cholLine (Pf z.2) * (cholLine (Pf z.2))ᵀ = Pf z.2 :=
      cholLine_mul_transpose _ (hPs _) hs hD hdet
    have hqne : (cholLine (Pf z.2)).det ≠ 0 := (cholLine_det_pos hs hD hdet).ne'
    have hg : (L z * cholLine (Pf z.2)).det ≠ 0 := by
      rw [Matrix.det_mul, hLdet]; simpa using hqne
    have := gram_mem_gramDomain _ hg
    have e : L z * Pf z.2 * (L z)ᵀ = (L z * cholLine (Pf z.2)) * (L z * cholLine (Pf z.2))ᵀ := by
      conv_lhs => rw [← hqP]
      rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    rw [e]; exact this
  have hform : ∀ ν, ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (formPair (seedForm n h) (L z * Pf z.2 * (L z)ᵀ) (L z * (Γ₁ - Γ₀) * (L z)ᵀ)
        (L z * (Γ₂ - Γ₀) * (L z)ᵀ)).coeff ν) (Set.univ ×ˢ stdTriangle) := by
    intro ν
    exact continuousOn_coeff_formPair_comp n h hh.continuousOn _ _ _ hG (hcong (Γ₁ - Γ₀))
      (hcong (Γ₂ - Γ₀)) (fun z hz => ⟨hGdom z hz, hsymL _ (hPs _) z, hsymL _ hQ₁ z, hsymL _ hQ₂ z⟩) ν
  have hsum : ∀ z : (ℝ × ℝ) × (ℝ × ℝ), (twPull (seedForm n h) (L z) (Pf z.2) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ =
      ∑ ν ∈ degSet n, (formPair (seedForm n h) (L z * Pf z.2 * (L z)ᵀ)
        (L z * (Γ₁ - Γ₀) * (L z)ᵀ) (L z * (Γ₂ - Γ₀) * (L z)ᵀ)).coeff ν *
        (SeedC3.rho (L z)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ := by
    intro z
    unfold twPull
    exact coeff_rho_eq_sum _ n _ (fun m' hm' => coeff_eq_zero_of_sum_ne
      (isHomogeneous_formPair_seed n h _ _ _) m' hm') κ
  have hfin : ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (twPull (seedForm n h) (L z) (Pf z.2) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ) (Set.univ ×ˢ stdTriangle) := by
    simp_rw [hsum]
    refine continuousOn_finsetSum _ fun ν _ => (hform ν).mul ?_
    exact (continuousOn_rho_coeff _ κ).comp hLinv (fun z _ => by simp [hLdet])
  rw [hLdef] at hfin
  exact hfin

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
