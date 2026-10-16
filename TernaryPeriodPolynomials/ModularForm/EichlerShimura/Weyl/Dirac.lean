module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.Main

@[expose] public section


/-!
# Weyl's lemma for Dirac-type systems with a smooth zero order term

`weyl_dirac`: a locally square integrable weak solution of `P₀ ∂₀ u + P₁ ∂₁ u + Q u = 0` on an
open subset of `ℂ ≅ ℝ²` (`P₀, P₁` symmetric involutions that anticommute, `Q` a smooth field of
linear maps) agrees almost everywhere with a smooth function.  The weak form of the equation is
`∑ⱼ Pⱼ (∫ ∂ⱼφ • u) = ∫ φ • Q u` for scalar test functions `φ` (integration by parts turns
`∫ ∂ⱼφ • u` into `- ∫ φ • ∂ⱼ u`, so this says `P · ∂u + Q u = 0`; the sign of `Q` is that of
the `+ Q u` term).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace ENNReal

section General

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {P : Fin 2 → X →L[ℝ] X}

/-- A smooth field of linear maps is a finite combination of fixed linear maps with smooth
coefficients (matrix units of an orthonormal basis). -/
theorem exists_expansion {U : Set ℂ} {Q : ℂ → X →L[ℝ] X} (hQ : ContDiffOn ℝ ∞ Q U) :
    ∃ (n : ℕ) (T : Fin n × Fin n → X →L[ℝ] X) (q : Fin n × Fin n → ℂ → ℝ),
      (∀ s, ContDiffOn ℝ ∞ (q s) U) ∧ ∀ z x, Q z x = ∑ s, q s z • T s x := by
  let b := stdOrthonormalBasis ℝ X
  refine ⟨Module.finrank ℝ X, fun s => (innerSL ℝ (b s.2)).smulRight (b s.1),
    fun s z => ⟪b s.1, Q z (b s.2)⟫_ℝ, fun s => ?_, fun z x => ?_⟩
  · exact (innerSL ℝ (b s.1)).contDiff.comp_contDiffOn (hQ.clm_apply contDiffOn_const)
  · conv_lhs => rw [← b.sum_repr' x]
    simp only [map_sum, map_smul, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← b.sum_repr' (Q z (b j)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [smul_smul, mul_comm, real_inner_comm]

/-- **Weyl's lemma for Dirac-type systems in the plane.**  A locally square integrable weak
solution of `P₀ ∂₀ u + P₁ ∂₁ u + Q u = 0` on an open set (`Q` a smooth field of linear maps,
`P₀, P₁` symmetric involutions that anticommute) agrees almost everywhere with a smooth function.
The hypothesis `h` is the weak form `∑ⱼ Pⱼ (∫ ∂ⱼφ • u) = ∫ φ • Q u`, i.e. `P · ∂u + Q u = 0` after
integrating by parts. -/
theorem weyl_dirac (hP : DiracPair P) {U : Set ℂ} (hU : IsOpen U) {Q : ℂ → X →L[ℝ] X}
    (hQ : ContDiffOn ℝ ∞ Q U) {u : ℂ → X}
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ U → MemLp u 2 (volume.restrict K))
    (h : ∀ φ : ℂ → ℝ, IsTest φ → tsupport φ ⊆ U →
      ∑ j, P j (∫ z, fderiv ℝ φ z (dir j) • u z) = ∫ z, φ z • Q z (u z)) :
    ∃ w : ℂ → X, ContDiffOn ℝ ∞ w U ∧ u =ᵐ[volume.restrict U] w := by
  obtain ⟨n, T, q, hq, hQe⟩ := exists_expansion hQ
  have hs : WeakSol U P T q u := ⟨hU, hP, hq, hu, fun φ hφ hφU => by
    rw [h φ hφ hφU]
    exact integral_congr_ae (Eventually.of_forall fun z => by
      simp only [hQe z (u z)])⟩
  exact hs.exists_smooth

end General

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
