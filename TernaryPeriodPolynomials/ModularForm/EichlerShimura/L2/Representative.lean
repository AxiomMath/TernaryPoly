module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Regular

@[expose] public section


/-!
# The harmonic representative of a cocycle datum

Given a smooth `Φ₁` with `Φ₁(γ z) = ρ(γ) Φ₁(z) + c(γ)` whose differential is supported compactly
modulo `Γ`, the vector `u₀ = ω - P_B ω` (`ω = dΦ₁`) is harmonic (`harmonic_u0`), and Weyl's lemma gives
a smooth equivariant form `L₀` of finite energy representing it (`exists_representative`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex UpperHalfPlane
open scoped ContDiff InnerProductSpace MatrixGroups ENNReal NNReal

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_mul mob_one IsCover cutoff cutoff_nonneg)
open TernaryPeriodPolynomials.Argument.ESFoundations.Weyl (XP mkX dir IsTest)

variable {Γ : Subgroup SL(2, ℤ)} {d : ℕ}

namespace HodgeDatum

variable (D : HodgeDatum Γ d) (W : Weights Γ)

theorem ctestVec_orth_bSub {ψ : ℂ → ℝ} (hψ : IsTest ψ) (hψU : tsupport ψ ⊆ U) (e : Wd d) :
    ∀ y ∈ D.bSub W, ⟪D.ctestVec W hψ hψU e, y⟫_ℝ = 0 := by
  have h : D.bSub W ≤ (ℝ ∙ D.ctestVec W hψ hψU e)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    rintro y ⟨φ, hφ, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact D.ctestVec_orth W hψ hψU e hφ.1 (Approx.good D W hφ)
  intro y hy
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (h hy)

/-- The vector `u₀ = ω - P_B ω` is harmonic for a good equivariant `ω = dΦ₁` with `Φ₁` smooth on `U`. -/
theorem harmonic_sub_proj {Φ₁ : ℂ → Wd d} (hΦ : ContDiffOn ℝ ∞ Φ₁ U)
    (hω : Good D W (fun z => fderiv ℝ Φ₁ z)) (hE : D.Eqv (fun z => fderiv ℝ Φ₁ z)) :
    Harmonic D W (D.xvec W hω - D.projB W (D.xvec W hω)) where
  eqv := Submodule.sub_mem _ (D.xvec_mem_eqvSub W hω hE)
    (D.bSub_le_eqvSub W (D.projB_mem W _))
  orth := D.sub_projB_mem_orthogonal W _
  closed := by
    intro ψ hψ hψU e
    rw [inner_sub_right, D.ctestVec_orth W hψ hψU e hΦ hω, D.ctestVec_orth_bSub W hψ hψU e _
      (D.projB_mem W _), sub_zero]

theorem good_of_cocycle {Φ₁ : ℂ → Wd d} (c : Γ → Wd d) (hΦ : ContDiffOn ℝ ∞ Φ₁ U)
    (hcoc : ∀ δ : Γ, ∀ z ∈ U, Φ₁ (mob (δ : SL(2, ℤ)) z) = D.ρ δ (Φ₁ z) + c δ)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    (h0 : ∀ z ∈ U, (∀ γ : Γ, mob (γ : SL(2, ℤ)) z ∉ K) → fderiv ℝ Φ₁ z = 0) :
    Good D W (fun z => fderiv ℝ Φ₁ z) :=
  ⟨continuousOn_fderiv hΦ, W.lintegral_θ_edens_lt_top D (continuousOn_fderiv hΦ)
    (D.eqv_fderiv_cocycle c (hΦ.differentiableOn (by simp)) hcoc) hK hKU h0⟩

/-- **The smooth equivariant harmonic representative.** -/
theorem exists_representative {Φ₁ : ℂ → Wd d} (c : Γ → Wd d) (hΦ : ContDiffOn ℝ ∞ Φ₁ U)
    (hcoc : ∀ δ : Γ, ∀ z ∈ U, Φ₁ (mob (δ : SL(2, ℤ)) z) = D.ρ δ (Φ₁ z) + c δ)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    (h0 : ∀ z ∈ U, (∀ γ : Γ, mob (γ : SL(2, ℤ)) z ∉ K) → fderiv ℝ Φ₁ z = 0) :
    ∃ a' b' : ℂ → Wd d, ContDiffOn ℝ ∞ a' U ∧ ContDiffOn ℝ ∞ b' U ∧
      (∀ z ∈ U, fderiv ℝ b' z (dir 0) = fderiv ℝ a' z (dir 1)) ∧
      (∀ z ∈ U, fderiv ℝ (fun z => D.H z (a' z)) z (dir 0) +
        fderiv ℝ (fun z => D.H z (b' z)) z (dir 1) = 0) ∧
      D.Eqv (formOf a' b') ∧ Good D W (formOf a' b') ∧
      ∀ hω : Good D W (fun z => fderiv ℝ Φ₁ z),
        ((D.xvec W hω - D.projB W (D.xvec W hω) : Hs d) : ℂ → XP (Wd d)) =ᵐ[volume.restrict U]
          D.wcoord W (formOf a' b') := by
  have hω := good_of_cocycle D W c hΦ hcoc hK hKU h0
  have hE : D.Eqv (fun z => fderiv ℝ Φ₁ z) :=
    D.eqv_fderiv_cocycle c (hΦ.differentiableOn (by simp)) hcoc
  have hu := harmonic_sub_proj D W hΦ hω hE
  obtain ⟨a', b', ha', hb', hae1, hae2, hcl, hco⟩ := exists_smooth D W hu
  have hae := wcoord_formOf_ae D W hae1 hae2
  have hc : ContinuousOn (formOf a' b') U := (contDiffOn_formOf ha' hb').continuousOn
  refine ⟨a', b', ha', hb', hcl, hco, eqv_of_mem_eqvSub D W hc hae hu.eqv,
    good_of_ae D W hc hae, fun hω' => hae⟩

end HodgeDatum

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
