module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Fubini
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.PairEq
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.PosDefSimplex

@[expose] public section


/-!
# The real intertwining integral commutes with the simplex integral: the cochain level statement

`planeIntG n h M Γ κ` is the coefficient `κ` of the plane integral cochain of the seed `ω_h` over the Gram triangle
`[Γ₀, Γ₁, Γ₂]` at the group element `M` (the triangle integral of `ρ(M)⁻¹ ω_{MPMᵀ}(MQ₁Mᵀ, MQ₂Mᵀ)`), `lineIntG` the
same for the line seed `σ_h`.  `tcommute`: for an invertible `g` and positive definite `Γ_i`,
`(s,t) ↦ planeIntG n h (L_{s,t} g) Γ κ` is integrable and
`∫_{ℝ²} planeIntG n h (L_{s,t} g) Γ κ = c_∞ · lineIntG n h g Γ κ`, `c_∞ = -2πi/(n+1)`.
Proof: congruence by `g` (`twPull_mul`, `affTri_congr`), coefficient mixing under integrals (`integral_coeff_rho`),
`plane_fubini` on the congruent triangle and `linePairQ_eq_lineFormPair`.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem twPull_mul (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (M₁ M₂ P Q₁ Q₂ : Mat3) :
    twPull ω (M₁ * M₂) P Q₁ Q₂ =
      SeedC3.rho M₂⁻¹ (twPull ω M₁ (M₂ * P * M₂ᵀ) (M₂ * Q₁ * M₂ᵀ) (M₂ * Q₂ * M₂ᵀ)) := by
  unfold twPull
  rw [← rho_mul, Matrix.mul_inv_rev]
  have e : ∀ X : Mat3, M₁ * (M₂ * X * M₂ᵀ) * M₁ᵀ = M₁ * M₂ * X * (M₁ * M₂)ᵀ := by
    intro X; rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  simp only [e]

theorem continuousOn_slice {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {F : α × β → γ} {S : Set α} {T : Set β} (hF : ContinuousOn F (S ×ˢ T)) {a : α} (ha : a ∈ S) :
    ContinuousOn (fun b => F (a, b)) T :=
  hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hb => ⟨ha, hb⟩)

/-- The `ρ(M)⁻¹`-twisted pullback of the line pair. -/
def twPullLine (σ : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (M P Q₁ Q₂ : Mat3) :
    MvPolynomial (Fin 3) ℂ :=
  SeedC3.rho M⁻¹ (lineFormPair σ (M * P * Mᵀ) (M * Q₁ * Mᵀ) (M * Q₂ * Mᵀ))

/-- The plane integral cochain of the seed over a Gram triangle, at the group element `M`. -/
def planeIntG (n : ℕ) (h : ℂ → ℂ) (M Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) : ℂ :=
  ∫ p in stdTriangle, (twPull (seedForm n h) M (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ

/-- The line integral cochain of the line seed over a Gram triangle, at the group element `M`. -/
def lineIntG (n : ℕ) (h : ℂ → ℂ) (M Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) : ℂ :=
  ∫ p in stdTriangle, (twPullLine (lineSeedForm n h) M (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ

theorem affTri_congr (g Γ₀ Γ₁ Γ₂ : Mat3) (p : ℝ × ℝ) :
    affTri (g * Γ₀ * gᵀ) (g * Γ₁ * gᵀ) (g * Γ₂ * gᵀ) p = g * affTri Γ₀ Γ₁ Γ₂ p * gᵀ := by
  unfold affTri
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul]

theorem isHomogeneous_twPull_seed (n : ℕ) (h : ℂ → ℂ) (M P Q₁ Q₂ : Mat3) :
    (twPull (seedForm n h) M P Q₁ Q₂).IsHomogeneous n :=
  isHomogeneous_rho _ (isHomogeneous_formPair_seed n h _ _ _)

theorem isHomogeneous_lineFormPair_seed (n : ℕ) (h : ℂ → ℂ) (G Q₁ Q₂ : Mat3) :
    (lineFormPair (lineSeedForm n h) G Q₁ Q₂).IsHomogeneous n := by
  rw [lineFormPair_lineSeedForm]
  have hlin : (C (lineTauG G) * X 2 - X 1 : MvPolynomial (Fin 3) ℂ).IsHomogeneous 1 :=
    (isHomogeneous_C_mul_X _ _).sub (isHomogeneous_X _ _)
  have := hlin.pow n
  rw [one_mul] at this
  exact this.C_mul _

theorem isHomogeneous_twPullLine_seed (n : ℕ) (h : ℂ → ℂ) (M P Q₁ Q₂ : Mat3) :
    (twPullLine (lineSeedForm n h) M P Q₁ Q₂).IsHomogeneous n :=
  isHomogeneous_rho _ (isHomogeneous_lineFormPair_seed n h _ _ _)

/-- Coefficient mixing under an integral: the coefficients of `ρ(M) f(x)` integrate to the finite combination
of the integrated coefficients of `f`. -/
theorem integral_coeff_rho {X : Type*} [MeasurableSpace X] (μ : Measure X) (n : ℕ) (M : Mat3)
    (f : X → MvPolynomial (Fin 3) ℂ) (hf : ∀ x, (f x).IsHomogeneous n)
    (hi : ∀ ν : Fin 3 →₀ ℕ, Integrable (fun x => (f x).coeff ν) μ) (κ : Fin 3 →₀ ℕ) :
    ∫ x, (SeedC3.rho M (f x)).coeff κ ∂μ =
      ∑ ν ∈ degSet n, (∫ x, (f x).coeff ν ∂μ) *
        (SeedC3.rho M (MvPolynomial.monomial ν 1)).coeff κ := by
  have hpt : ∀ x, (SeedC3.rho M (f x)).coeff κ =
      ∑ ν ∈ degSet n, (f x).coeff ν *
        (SeedC3.rho M (MvPolynomial.monomial ν 1)).coeff κ := fun x =>
    coeff_rho_eq_sum M n _ (fun m' hm' => coeff_eq_zero_of_sum_ne (hf x) m' hm') κ
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun ν _ => (hi ν).mul_const _)]
  simp_rw [integral_mul_const]

theorem posDef_transpose {P : Mat3} (hP : P.PosDef) : Pᵀ = P := by
  have := hP.isHermitian.eq
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

/-- **The real intertwining integral of the plane integral cochain is `c_∞` times the line integral cochain.** -/
theorem tcommute (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im})
    (M : ℝ) (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (g : Mat3) (hg : g.det ≠ 0) (Γ₀ Γ₁ Γ₂ : Mat3) (hΓ₀ : Γ₀.PosDef) (hΓ₁ : Γ₁.PosDef) (hΓ₂ : Γ₂.PosDef)
    (κ : Fin 3 →₀ ℕ) :
    Integrable (fun u : ℝ × ℝ => planeIntG n h (entryFrame u.1 u.2 * g) Γ₀ Γ₁ Γ₂ κ) ∧
    ∫ u : ℝ × ℝ, planeIntG n h (entryFrame u.1 u.2 * g) Γ₀ Γ₁ Γ₂ κ =
      (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) * lineIntG n h g Γ₀ Γ₁ Γ₂ κ := by
  set Γ'₀ := g * Γ₀ * gᵀ with hΓ'₀
  set Γ'₁ := g * Γ₁ * gᵀ with hΓ'₁
  set Γ'₂ := g * Γ₂ * gᵀ with hΓ'₂
  have p₀ : Γ'₀.PosDef := posDef_congr hΓ₀ hg
  have p₁ : Γ'₁.PosDef := posDef_congr hΓ₁ hg
  have p₂ : Γ'₂.PosDef := posDef_congr hΓ₂ hg
  have hcond := affTri_mem_cholDomain p₀ p₁ p₂
  have hQ1 : Γ'₁ - Γ'₀ = g * (Γ₁ - Γ₀) * gᵀ := by
    simp only [hΓ'₁, hΓ'₀, Matrix.mul_sub, Matrix.sub_mul]
  have hQ2 : Γ'₂ - Γ'₀ = g * (Γ₂ - Γ₀) * gᵀ := by
    simp only [hΓ'₂, hΓ'₀, Matrix.mul_sub, Matrix.sub_mul]
  have hLdet : ∀ u : ℝ × ℝ, (entryFrame u.1 u.2).det ≠ 0 := fun u => by
    rw [entryFrame_det_eq]; exact one_ne_zero
  have hF := fun ν => plane_fubini n hn h hh M hM Γ'₀ Γ'₁ Γ'₂ (posDef_transpose p₀) (posDef_transpose p₁)
    (posDef_transpose p₂) hcond ν
  have hcont := fun ν => continuousOn_twPull_joint n h hh Γ'₀ Γ'₁ Γ'₂ (posDef_transpose p₀)
    (posDef_transpose p₁) (posDef_transpose p₂) hcond ν
  -- the pointwise expansion of the plane cochain
  set r : (Fin 3 →₀ ℕ) → ℂ := fun ν => (SeedC3.rho g⁻¹ (MvPolynomial.monomial ν 1)).coeff κ with hr
  have hexp : ∀ u : ℝ × ℝ, planeIntG n h (entryFrame u.1 u.2 * g) Γ₀ Γ₁ Γ₂ κ =
      ∑ ν ∈ degSet n, (∫ p in stdTriangle, (twPull (seedForm n h) (entryFrame u.1 u.2) (affTri Γ'₀ Γ'₁ Γ'₂ p) (Γ'₁ - Γ'₀) (Γ'₂ - Γ'₀)).coeff ν) * r ν := by
    intro u
    unfold planeIntG
    have e : ∀ p : ℝ × ℝ, twPull (seedForm n h) (entryFrame u.1 u.2 * g) (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀) =
        SeedC3.rho g⁻¹ (twPull (seedForm n h) (entryFrame u.1 u.2) (affTri Γ'₀ Γ'₁ Γ'₂ p) (Γ'₁ - Γ'₀) (Γ'₂ - Γ'₀)) := by
      intro p
      rw [twPull_mul, affTri_congr, hQ1, hQ2]
    simp_rw [e]
    refine integral_coeff_rho _ n g⁻¹ _ (fun p => isHomogeneous_twPull_seed n h _ _ _ _) (fun ν => ?_) κ
    have hc := continuousOn_slice (hcont ν) (Set.mem_univ u)
    exact hc.integrableOn_compact isCompact_stdTriangle
  simp_rw [hexp]
  refine ⟨integrable_finsetSum _ (fun ν _ => (hF ν).1.mul_const _), ?_⟩
  rw [integral_finsetSum _ (fun ν _ => (hF ν).1.mul_const _)]
  simp_rw [integral_mul_const, (hF _).2.1]
  unfold lineIntG
  have eL : ∀ p : ℝ × ℝ, twPullLine (lineSeedForm n h) g (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀) =
      SeedC3.rho g⁻¹ (lineFormPair (lineSeedForm n h) (affTri Γ'₀ Γ'₁ Γ'₂ p) (Γ'₁ - Γ'₀) (Γ'₂ - Γ'₀)) := by
    intro p
    unfold twPullLine
    rw [affTri_congr, hQ1, hQ2]
  simp_rw [eL]
  have hLP : ∀ p ∈ stdTriangle, ∀ ν : Fin 3 →₀ ℕ, (linePairQ (lineSeedForm n h)
      (affTri Γ'₀ Γ'₁ Γ'₂ p) (Γ'₁ - Γ'₀) (Γ'₂ - Γ'₀)).coeff ν = (lineFormPair (lineSeedForm n h) (affTri Γ'₀ Γ'₁ Γ'₂ p) (Γ'₁ - Γ'₀) (Γ'₂ - Γ'₀)).coeff ν := by
    intro p hp ν
    have hpd := posDef_affTri p₀ p₁ p₂ hp
    have hq1 : (Γ'₁ - Γ'₀)ᵀ = Γ'₁ - Γ'₀ := by
      rw [Matrix.transpose_sub, posDef_transpose p₁, posDef_transpose p₀]
    have hq2 : (Γ'₂ - Γ'₀)ᵀ = Γ'₂ - Γ'₀ := by
      rw [Matrix.transpose_sub, posDef_transpose p₂, posDef_transpose p₀]
    rw [linePairQ_eq_lineFormPair _ _ _ _ (posDef_transpose hpd) (hcond p hp) hq1 hq2]
  rw [integral_coeff_rho _ n g⁻¹ _ (fun p => isHomogeneous_lineFormPair_seed n h _ _ _) ?_ κ]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have : ∫ p in stdTriangle, (linePairQ (lineSeedForm n h) (affTri Γ'₀ Γ'₁ Γ'₂ p)
        (Γ'₁ - Γ'₀) (Γ'₂ - Γ'₀)).coeff ν = ∫ p in stdTriangle, (lineFormPair (lineSeedForm n h) (affTri Γ'₀ Γ'₁ Γ'₂ p) (Γ'₁ - Γ'₀) (Γ'₂ - Γ'₀)).coeff ν :=
      setIntegral_congr_fun measurableSet_stdTriangle fun p hp => hLP p hp ν
    rw [← this]
    ring
  · intro ν
    have h3 := (hF ν).2.2
    exact (IntegrableOn.congr_fun h3 (fun p hp => hLP p hp ν) measurableSet_stdTriangle)

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
