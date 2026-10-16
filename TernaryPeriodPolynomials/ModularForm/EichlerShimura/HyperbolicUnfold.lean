module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.PartitionOfUnity

@[expose] public section


/-!
# Hyperbolic integrals and unfolding along the partition of unity

Foundation file of the unconditional Eichler--Shimura route.  A flat Lebesgue integral of a function supported in the upper half plane equals the
hyperbolic integral of `F(z) y²` (`integral_flat_eq_hyp`); the hyperbolic measure is invariant
under `SL(2, ℤ)` (`integral_smul_hyp`, from Mathlib's invariance under `GL(2, ℝ)`); and
for a continuous compactly supported `f` on `ℍ`
`∫ f = Σ_{γ ∈ S} ∫ cutoff · f(γ •)` for any finite `S ⊆ Γ` containing the relevant translates
(`unfold_cutoff`), where `cutoff` is the `Γ`-partition of unity of `Partition`.  No fundamental
domain is needed: the partition of unity takes its role.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory UpperHalfPlane Complex
open scoped NNReal ENNReal MatrixGroups

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.Global

theorem integral_flat_eq_hyp (F : ℂ → ℂ) (hF : ∀ x, x ∉ U → F x = 0) :
    ∫ x : ℂ, F x = ∫ z : ℍ, F (z : ℂ) * (z.im : ℂ) ^ 2 ∂volume := by
  have hcont : Continuous fun z : ℍ => (((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) :
      ℝ≥0∞) := by
    refine ENNReal.continuous_coe.comp (Continuous.pow (Continuous.div₀ continuous_const ?_ ?_) _)
    · exact continuous_im.subtype_mk _
    · exact fun x ↦ NNReal.ne_iff.mp x.im_ne_zero
  rw [UpperHalfPlane.volume_def,
    integral_withDensity_eq_integral_toReal_smul hcont.measurable
      (Filter.Eventually.of_forall fun _ => by simp)]
  have h1 : ∀ x : ℍ, (↑((1 / NNReal.mk x.im x.im_pos.le) ^ 2 : ℝ≥0) : ℝ≥0∞).toReal •
      (F (x : ℂ) * (x.im : ℂ) ^ 2) = F (x : ℂ) := by
    intro x
    have hy : (x.im : ℝ) ≠ 0 := x.im_pos.ne'
    rw [ENNReal.coe_toReal]
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, Complex.real_smul]
    push_cast
    have hy' : (x.im : ℂ) ≠ 0 := by exact_mod_cast hy
    field_simp
  simp_rw [h1]
  have h2 := (measurableEmbedding_coe.integral_map (μ := Measure.comap UpperHalfPlane.coe volume) F)
  rw [measurableEmbedding_coe.map_comap] at h2
  rw [← h2]
  have hrange : Set.range UpperHalfPlane.coe = U := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩; exact z.im_pos
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro x hx
  exact hF x hx

/-- The hyperbolic measure is invariant under `SL(2, ℤ)`. -/
theorem integral_smul_hyp (γ : SL(2, ℤ)) (f : ℍ → ℂ) :
    ∫ z : ℍ, f (γ • z) ∂volume = ∫ z : ℍ, f z ∂volume := by
  have h := measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ) (volume : Measure ℍ)
  have h2 := h.integral_comp (measurableEmbedding_const_smul
    (Matrix.SpecialLinearGroup.mapGL ℝ γ)) f
  convert h2 using 2
  funext z
  rfl

variable (Γ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ))

theorem continuous_cutoff_comp (hR : IsCover Γ R) (g : SL(2, ℤ)) :
    Continuous fun z : ℍ => cutoff Γ R ((g • z : ℍ) : ℂ) := by
  have h1 : ContinuousOn (cutoff Γ R) U := (contDiffOn_cutoff Γ R hR).continuousOn
  have h2 : Continuous fun z : ℍ => (g • z : ℍ) :=
    (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ g) : Continuous fun z : ℍ =>
      (Matrix.SpecialLinearGroup.mapGL ℝ g) • z)
  exact h1.comp_continuous ((UpperHalfPlane.continuous_coe).comp h2) (fun z => (g • z).im_pos)

theorem mob_inv_smul (g : SL(2, ℤ)) (z : ℍ) : mob g⁻¹ (g • z : ℍ) = z := by
  rw [mob_coe, inv_smul_smul]

variable {Γ R}

theorem integrable_cutoff_mul (hR : IsCover Γ R) (g : SL(2, ℤ)) {f : ℍ → ℂ}
    (hf : Continuous f) (hcs : HasCompactSupport f) :
    Integrable (fun z : ℍ => (cutoff Γ R ((g • z : ℍ) : ℂ) : ℂ) * f z) volume := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (hcs.mul_left)
  exact (Complex.continuous_ofReal.comp (continuous_cutoff_comp Γ R hR g)).mul hf

/-- **Unfolding along the partition of unity**: for a continuous compactly supported `f` on `ℍ`
and a finite set `S ⊆ Γ` containing all `γ` with `cutoff (γ⁻¹ z) f(z) ≠ 0` for some `z`,
`∫ f = Σ_{γ ∈ S} ∫ cutoff · f(γ •)`. -/
theorem unfold_cutoff (hR : IsCover Γ R) {f : ℍ → ℂ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (S : Finset Γ) (hS : ∀ γ : Γ, γ ∉ S → ∀ z : ℍ,
      cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) * f z = 0) :
    ∫ z : ℍ, f z ∂volume =
      ∑ γ ∈ S, ∫ z : ℍ, (cutoff Γ R (z : ℂ) : ℂ) * f ((γ : SL(2, ℤ)) • z) ∂volume := by
  have h1 : ∀ z : ℍ, f z = ∑ γ ∈ S, (cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) : ℂ) * f z := by
    intro z
    have hz : (z : ℂ) ∈ U := z.im_pos
    by_cases hfz : f z = 0
    · simp [hfz]
    · have hzero : ∀ γ : Γ, γ ∉ S → cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) = 0 := fun γ hγ => by
        have h := hS γ hγ z
        have h' := (mul_eq_zero.mp h).resolve_right hfz
        exact_mod_cast h'
      have h2 := finsum_cutoff (Γ := Γ) (R := R) hR hz
      rw [finsum_eq_sum_of_support_subset _ (s := S) (fun γ hγ => by
        by_contra hnot
        exact hγ (hzero γ hnot))] at h2
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, h2]
      simp
  have h3 : ∀ γ : Γ, Integrable (fun z : ℍ => (cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) : ℂ) * f z)
      volume := by
    intro γ
    have := integrable_cutoff_mul hR (γ : SL(2, ℤ))⁻¹ hf hcs
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [mob_coe]
  calc ∫ z : ℍ, f z ∂volume
      = ∫ z : ℍ, ∑ γ ∈ S, (cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) : ℂ) * f z ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ∑ γ ∈ S, ∫ z : ℍ, (cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) : ℂ) * f z ∂volume :=
        integral_finsetSum _ fun γ _ => h3 γ
    _ = _ := by
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [← integral_smul_hyp (γ : SL(2, ℤ))]
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        simp only [mob_inv_smul]

end TernaryPeriodPolynomials.Argument.ESFoundations.Global
