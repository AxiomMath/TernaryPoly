module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.JointContinuity

@[expose] public section


/-!
# The real intertwining integral commutes with the integral over a Gram triangle

`plane_fubini`: for a Gram triangle `[Γ₀, Γ₁, Γ₂]` (symmetric matrices) whose affine hull lies in the Cholesky domain
(e.g. the Gram matrices of three invertible matrices), the function
`(s,t) ↦ ∫_Δ coeff_κ twPull ω L_{s,t} P_p Q₁ Q₂ dp` is integrable and
`∫_{ℝ²} ∫_Δ coeff_κ twPull ω L_{s,t} P_p Q₁ Q₂ = c_∞ ∫_Δ coeff_κ linePairQ σ P_p Q₁ Q₂`, `c_∞ = -2πi/(n+1)`,
where `ω = ω_h` is the plane seed and `σ = σ_h` the line seed.  Proof: Fubini on `ℝ² × Δ`: joint continuity
(`PlaneJointContinuity`), the uniform `L¹` bound (`PlaneUniform`) and the pointwise form identity at each Gram
point (`twPull_integral`).

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- **The exchange of the real intertwining integral with the integral over a Gram triangle.** -/
theorem plane_fubini (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im})
    (M : ℝ) (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (Γ₀ Γ₁ Γ₂ : Mat3) (h₀ : Γ₀ᵀ = Γ₀) (h₁ : Γ₁ᵀ = Γ₁) (h₂ : Γ₂ᵀ = Γ₂)
    (hcond : ∀ p ∈ stdTriangle, affTri Γ₀ Γ₁ Γ₂ p ∈ cholDomain) (κ : Fin 3 →₀ ℕ) :
    Integrable (fun u : ℝ × ℝ => ∫ p in stdTriangle, (twPull (seedForm n h) (entryFrame u.1 u.2) (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ) ∧
    (∫ u : ℝ × ℝ, ∫ p in stdTriangle, (twPull (seedForm n h) (entryFrame u.1 u.2) (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ) =
    (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) * (∫ p in stdTriangle, (linePairQ (lineSeedForm n h) (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ) ∧
    IntegrableOn (fun p : ℝ × ℝ => (linePairQ (lineSeedForm n h) (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ) stdTriangle := by
  have hQ₁ : (Γ₁ - Γ₀)ᵀ = Γ₁ - Γ₀ := by rw [Matrix.transpose_sub, h₀, h₁]
  have hQ₂ : (Γ₂ - Γ₀)ᵀ = Γ₂ - Γ₀ := by rw [Matrix.transpose_sub, h₀, h₂]
  have hPs : ∀ p, (affTri Γ₀ Γ₁ Γ₂ p)ᵀ = affTri Γ₀ Γ₁ Γ₂ p := by
    intro p
    simp only [affTri, Matrix.transpose_add, Matrix.transpose_smul, hQ₁, hQ₂, h₀]
  set F : (ℝ × ℝ) × (ℝ × ℝ) → ℂ := fun z => (twPull (seedForm n h) (entryFrame z.1.1 z.1.2) (affTri Γ₀ Γ₁ Γ₂ z.2) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ with hF
  have hFc : ContinuousOn F (Set.univ ×ˢ stdTriangle) :=
    continuousOn_twPull_joint n h hh Γ₀ Γ₁ Γ₂ h₀ h₁ h₂ hcond κ
  set ν : Measure (ℝ × ℝ) := volume.restrict stdTriangle with hν
  have hprod : (volume : Measure (ℝ × ℝ)).prod ν = ((volume : Measure (ℝ × ℝ)).prod volume).restrict
      (Set.univ ×ˢ stdTriangle) := by
    rw [hν, ← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : AEStronglyMeasurable F ((volume : Measure (ℝ × ℝ)).prod ν) := by
    rw [hprod]
    exact hFc.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_stdTriangle)
  obtain ⟨B, hB⟩ := uniform_l1_twPull n hn h hh M hM Γ₀ Γ₁ Γ₂ h₀ h₁ h₂ hcond κ
  have hfin : ν Set.univ < ⊤ := by
    rw [hν, Measure.restrict_apply_univ]
    exact isCompact_stdTriangle.measure_lt_top
  have hint1 : ∀ᵐ p ∂ν, Integrable (fun u : ℝ × ℝ => F (u, p)) := by
    rw [hν]
    filter_upwards [ae_restrict_mem measurableSet_stdTriangle] with p hp
    obtain ⟨hs, hD, hdet⟩ := hcond p hp
    exact (twPull_integral n hn h hh M hM (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀) (hPs p) hs hD hdet
      hQ₁ hQ₂ κ).1
  have : IsFiniteMeasure ν := ⟨hfin⟩
  have hint2 : Integrable (fun p : ℝ × ℝ => ∫ u : ℝ × ℝ, ‖F (u, p)‖) ν := by
    refine Integrable.mono' (integrable_const B) ?_ ?_
    · have := (hmeas.norm).prod_swap.integral_prod_right'
      exact this
    · rw [hν]
      filter_upwards [ae_restrict_mem measurableSet_stdTriangle] with p hp
      rw [Real.norm_of_nonneg (integral_nonneg fun u => norm_nonneg _)]
      exact hB p hp
  have hFint : Integrable F ((volume : Measure (ℝ × ℝ)).prod ν) :=
    (integrable_prod_iff' hmeas).mpr ⟨hint1, hint2⟩
  have hcong : ∀ p ∈ stdTriangle, ∫ u : ℝ × ℝ, F (u, p) = (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) *
      (linePairQ (lineSeedForm n h) (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ := by
    intro p hp
    obtain ⟨hs, hD, hdet⟩ := hcond p hp
    exact (twPull_integral n hn h hh M hM (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀) (hPs p) hs hD hdet
      hQ₁ hQ₂ κ).2
  refine ⟨hFint.integral_prod_left, ?_, ?_⟩
  · have hswap := integral_integral_swap (f := fun u p => F (u, p)) hFint
    simp only [hF] at hswap hcong ⊢
    rw [hν] at hswap
    rw [hswap, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_stdTriangle hcong
  · have hint3 : Integrable (fun p : ℝ × ℝ => ∫ u : ℝ × ℝ, F (u, p)) ν := hFint.integral_prod_right
    have hint4 : IntegrableOn (fun p : ℝ × ℝ => ∫ u : ℝ × ℝ, F (u, p)) stdTriangle := hint3
    have hint5 := hint4.congr_fun hcong measurableSet_stdTriangle
    have hc : (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) ≠ 0 := by
      have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      simp [Real.pi_ne_zero, this]
    have h6 : IntegrableOn (fun p : ℝ × ℝ => (-2 * Real.pi * Complex.I / ((n : ℂ) + 1))⁻¹ *
        ((-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) * (linePairQ (lineSeedForm n h) (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ)) stdTriangle :=
      hint5.const_mul _
    exact IntegrableOn.congr_fun h6 (fun p _ => inv_mul_cancel_left₀ hc _) measurableSet_stdTriangle

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
