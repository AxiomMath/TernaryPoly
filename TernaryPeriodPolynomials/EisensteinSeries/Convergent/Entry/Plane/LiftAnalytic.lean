module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.JvecLift
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RhoContinuity

@[expose] public section


/-!
# Analyticity of the boundary combination of the plane integral cochain

`Bare O n m M Γ₀ Γ₁ Γ₂ = ∑_ν ρ(M⁻¹)_{mν} • (J_ν(Γ₁',Γ₂') - J_ν(Γ₀',Γ₂') + J_ν(Γ₀',Γ₁'))`, `Γᵢ' = M Γᵢ Mᵀ`, is the
**positive** boundary combination `J₁₂ - J₀₂ + J₀₁` of the single orbit-type integrals; by Stokes
(`planeIntG_stokes`, `planeHol_stokes`) the plane integral cochain is its **negative**:
`planeIntG = -(c_F/2) · Bare` (hence `OmegaVec = -(c/2)(B(M) + π(J_∞) B(εM))`).  `analyticAt_Bare`: `Bare` is jointly real
analytic in `(M, Γ₀, Γ₁, Γ₂)` at invertible `M` and positive definite `Γᵢ`, for an orbit-type `O` analytic on the upper
half plane; and the coefficients of `ρ(M⁻¹)` are polynomial in `M` (`rhoInv_coeff_eq`, `analyticAt_rhoInv_coeff`).

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory Set MvPolynomial Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- `ρ(M⁻¹)` has polynomial matrix coefficients in `M` (the entries and the determinant of `M`). -/
theorem rhoInv_coeff_eq {M : Mat3} (hM : M.det ≠ 0) (Q : Poly) (m : Fin 3 →₀ ℕ) :
    (SeedC3.rho M⁻¹ Q).coeff m =
      algebraMap ℝ ℂ M.det * (substitute (M.map (algebraMap ℝ ℂ)) Q).coeff m := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  rw [rho_eq_C_mul_substitute, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv', inv_inv, coeff_C_mul]
  rfl

theorem analyticAt_rhoInv_coeff {M : Mat3} (hM : M.det ≠ 0) (Q : Poly) (m : Fin 3 →₀ ℕ) :
    AnalyticAt ℝ (fun A : Mat3 => (SeedC3.rho A⁻¹ Q).coeff m) M := by
  have hS : ContDiff ℝ ⊤ (fun A : Mat3 =>
      algebraMap ℝ ℂ A.det * (substitute (A.map (algebraMap ℝ ℂ)) Q).coeff m) :=
    contDiff_det_cast.mul
      (contDiff_coeff_substitute (fun A : Mat3 => A.map (algebraMap ℝ ℂ)) contDiff_mapEntry Q m)
  refine hS.contDiffAt.analyticAt.congr ?_
  have hopen : IsOpen {A : Mat3 | A.det ≠ 0} := isOpen_ne.preimage (Continuous.matrix_det continuous_id)
  filter_upwards [hopen.mem_nhds hM] with A hA
  exact (rhoInv_coeff_eq hA Q m).symm


theorem contDiff_matMul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → Mat3}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) : ContDiff ℝ ⊤ (fun x => f x * g x) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (contDiff_pi.mp (contDiff_pi.mp hf i) k).mul (contDiff_pi.mp (contDiff_pi.mp hg k) j)

theorem contDiff_matTranspose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → Mat3}
    (hf : ContDiff ℝ ⊤ f) : ContDiff ℝ ⊤ (fun x => (f x)ᵀ) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  simp only [Matrix.transpose_apply]
  exact contDiff_pi.mp (contDiff_pi.mp hf j) i

theorem contDiff_conj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → Mat3}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) : ContDiff ℝ ⊤ (fun x => f x * g x * (f x)ᵀ) :=
  contDiff_matMul (contDiff_matMul hf hg) (contDiff_matTranspose hf)

section Bare

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [CompleteSpace G]

/-- The boundary combination of the `J`-integrals, mixed by the coefficients of `ρ(M⁻¹)`. -/
def Bare (O : ℂ → G) (n : ℕ) (m : Fin 3 →₀ ℕ) (M Γ₀ Γ₁ Γ₂ : Mat3) : G :=
  ∑ ν ∈ degSet n, (SeedC3.rho M⁻¹ (MvPolynomial.monomial ν 1)).coeff m •
    (JgenInt O n ν (M * Γ₁ * Mᵀ) (M * Γ₂ * Mᵀ) - JgenInt O n ν (M * Γ₀ * Mᵀ) (M * Γ₂ * Mᵀ) +
      JgenInt O n ν (M * Γ₀ * Mᵀ) (M * Γ₁ * Mᵀ))

theorem analyticAt_JgenInt_conj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (O : ℂ → G)
    (hO : ∀ z : ℂ, 0 < z.im → AnalyticAt ℝ O z) (n : ℕ) (μ : Fin 3 →₀ ℕ) {f g h : E → Mat3}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) (hh : ContDiff ℝ ⊤ h) {x₀ : E}
    (hdet : (f x₀).det ≠ 0) (hga : (g x₀).PosDef) (hha : (h x₀).PosDef) :
    AnalyticAt ℝ (fun x => JgenInt O n μ (f x * g x * (f x)ᵀ) (f x * h x * (f x)ᵀ)) x₀ := by
  have hpair : AnalyticAt ℝ (fun x => (f x * g x * (f x)ᵀ, f x * h x * (f x)ᵀ)) x₀ :=
    ((contDiff_conj hf hg).prodMk (contDiff_conj hf hh)).contDiffAt.analyticAt
  have h1 := analyticAt_JgenInt O hO n μ (posDef_congr hga hdet) (posDef_congr hha hdet)
  have h2 := AnalyticAt.comp_of_eq (g := fun q : Mat3 × Mat3 => JgenInt O n μ q.1 q.2) h1 hpair rfl
  exact h2

theorem analyticAt_Bare (O : ℂ → G) (hO : ∀ z : ℂ, 0 < z.im → AnalyticAt ℝ O z) (n : ℕ) (m : Fin 3 →₀ ℕ)
    {M Γ₀ Γ₁ Γ₂ : Mat3} (hM : M.det ≠ 0) (p₀ : Γ₀.PosDef) (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) :
    AnalyticAt ℝ (fun x : Mat3 × Mat3 × Mat3 × Mat3 => Bare O n m x.1 x.2.1 x.2.2.1 x.2.2.2) (M, Γ₀, Γ₁, Γ₂) := by
  have cM : ContDiff ℝ ⊤ (fun x : Mat3 × Mat3 × Mat3 × Mat3 => x.1) := by fun_prop
  have c0 : ContDiff ℝ ⊤ (fun x : Mat3 × Mat3 × Mat3 × Mat3 => x.2.1) := by fun_prop
  have c1 : ContDiff ℝ ⊤ (fun x : Mat3 × Mat3 × Mat3 × Mat3 => x.2.2.1) := by fun_prop
  have c2 : ContDiff ℝ ⊤ (fun x : Mat3 × Mat3 × Mat3 × Mat3 => x.2.2.2) := by fun_prop
  unfold Bare
  refine Finset.analyticAt_fun_sum _ (fun ν _ => ?_)
  have hr : AnalyticAt ℝ (fun x : Mat3 × Mat3 × Mat3 × Mat3 =>
      (SeedC3.rho x.1⁻¹ (MvPolynomial.monomial ν 1)).coeff m) (M, Γ₀, Γ₁, Γ₂) :=
    (analyticAt_rhoInv_coeff hM (MvPolynomial.monomial ν 1) m).comp_of_eq (cM.contDiffAt.analyticAt) rfl
  refine hr.smul (((analyticAt_JgenInt_conj O hO n ν cM c1 c2 hM p₁ p₂).sub
    (analyticAt_JgenInt_conj O hO n ν cM c0 c2 hM p₀ p₂)).add
    (analyticAt_JgenInt_conj O hO n ν cM c0 c1 hM p₀ p₁))

end Bare

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
