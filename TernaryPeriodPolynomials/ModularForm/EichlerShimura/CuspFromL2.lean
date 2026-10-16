module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CuspDecay

@[expose] public section


/-!
# `L²` holomorphic modular forms are cusp forms

Foundation file of the unconditional Eichler--Shimura route.  `cuspForm_of_L2`: a function `f` holomorphic on the upper half plane, of weight
`m + 2 ≥ 3` for a finite-index subgroup `Λ ≤ SL(2, ℤ)` not containing `-1`, whose cutoff-weighted
`L²` norm `∫ cutoff · y^m |f|²` is finite, is a Mathlib `CuspForm` of weight `m + 2` for the image
of `Λ` in `GL₂(ℝ)` (the type used by `holCocycle`).  Slash invariance is the transformation law;
vanishing at every cusp follows from `CuspDecay.decay_bound` (`isZeroAtImInfty_hs`), no Fourier
expansion needed.

Formalized by Claude Sonnet 5.5.
-/

open Complex MeasureTheory UpperHalfPlane ModularForm
open scoped ContDiff MatrixGroups NNReal ENNReal Real
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition
open TernaryPeriodPolynomials.Argument.ESFoundations.Global
open TernaryPeriodPolynomials.Argument.ESFoundations.CuspL2

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.ESFoundations.CuspL2

variable {Λ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)} {m : ℕ} {f : ℂ → ℂ}

theorem slash_eq_hs (g : SL(2, ℤ)) (z : ℍ) :
    ((fun w : ℍ => f (w : ℂ)) ∣[((m + 2 : ℕ) : ℤ)] g) z = hs m f g (z : ℂ) := by
  rw [SL_slash_apply]
  unfold hs
  rw [mob_coe, zpow_neg, zpow_natCast]
  rfl

theorem tendsto_im_atImInfty' : Filter.Tendsto (fun z : ℍ => z.im) UpperHalfPlane.atImInfty
    Filter.atTop := Filter.tendsto_comap

theorem isZeroAtImInfty_hs [Λ.FiniteIndex] (hm : 1 ≤ m) (hneg : (-1 : SL(2, ℤ)) ∉ Λ)
    (hR : IsCover Λ R) (hf : DifferentiableOn ℂ f U)
    (hmod : ∀ γ ∈ Λ, ∀ z ∈ U, f (mob γ z) = den γ z ^ (m + 2) * f z)
    (hL2 : Integrable (L2dens Λ R m f)) (g : SL(2, ℤ)) :
    IsZeroAtImInfty ((fun w : ℍ => f (w : ℂ)) ∣[((m + 2 : ℕ) : ℤ)] g) := by
  obtain ⟨r, hr, hb⟩ := decay_bound hneg hR hf hmod g
  set E : ℝ := (∫⁻ z : ℂ, ENNReal.ofReal (L2dens Λ R m f z)).toReal with hE
  have hfin : ∫⁻ z : ℂ, ENNReal.ofReal (L2dens Λ R m f z) ≠ ⊤ := hL2.lintegral_lt_top.ne
  have hbound : ∀ z : ℍ, 1 + r < z.im →
      ‖hs m f g (z : ℂ)‖ ^ 2 ≤ (3 * E / (π * r ^ 2)) * ((z.im - r) ^ m)⁻¹ := by
    intro z hz
    have h1 := hb (z : ℂ) hz
    have hpos : 0 < z.im - r := by linarith
    have hpos' : 0 < (z : ℂ).im - r := hpos
    have h2 := (ENNReal.ofReal_le_iff_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)).1 h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
    have hpi : 0 < π * r ^ 2 := by positivity
    have h3 : (z : ℂ).im = z.im := rfl
    rw [h3, ← hE] at h2
    have h4 : ‖hs m f g (z : ℂ)‖ ^ 2 * (π * r ^ 2) ≤ 3 * E * ((z.im - r) ^ m)⁻¹ := by
      nlinarith [h2]
    rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
    linarith
  rw [IsZeroAtImInfty, Filter.ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero]
  have hev : ∀ᶠ z : ℍ in UpperHalfPlane.atImInfty, 1 + r < z.im :=
    tendsto_im_atImInfty'.eventually (Filter.eventually_gt_atTop _)
  have hlim : Filter.Tendsto (fun z : ℍ => Real.sqrt (3 * E / (π * r ^ 2) * ((z.im - r) ^ m)⁻¹))
      UpperHalfPlane.atImInfty (nhds 0) := by
    have h1 : Filter.Tendsto (fun z : ℍ => z.im - r) UpperHalfPlane.atImInfty Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ (-r) tendsto_im_atImInfty'
    have h2 : Filter.Tendsto (fun z : ℍ => (z.im - r) ^ m) UpperHalfPlane.atImInfty Filter.atTop :=
      (Filter.tendsto_pow_atTop (by omega)).comp h1
    have h3 := (h2.inv_tendsto_atTop).const_mul (3 * E / (π * r ^ 2))
    have h5 : Real.sqrt 0 = 0 := Real.sqrt_zero
    rw [mul_zero] at h3
    have h4 := (Real.continuous_sqrt.tendsto 0).comp h3
    rwa [h5] at h4
  refine squeeze_zero' (Filter.Eventually.of_forall fun z => norm_nonneg _) ?_ hlim
  filter_upwards [hev] with z hz
  rw [slash_eq_hs]
  exact Real.le_sqrt_of_sq_le (hbound z hz)

/-- **An `L²` holomorphic modular form is a cusp form.** If `Λ ≤ SL(2, ℤ)` has finite index and
does not contain `-1`, `m ≥ 1`, and `f` is holomorphic on the upper half plane, of weight `m + 2`
for `Λ`, with finite energy `∫ cutoff · y^m |f|² < ∞` (`cutoff` the partition of unity of `Λ`),
then `f` is a Mathlib `CuspForm` of weight `m + 2` for the image of `Λ` in `GL₂(ℝ)`. -/
theorem cuspForm_of_L2 [Λ.FiniteIndex] (hm : 1 ≤ m) (hneg : (-1 : SL(2, ℤ)) ∉ Λ)
    (hR : IsCover Λ R) (hf : DifferentiableOn ℂ f U)
    (hmod : ∀ γ ∈ Λ, ∀ z ∈ U, f (mob γ z) = den γ z ^ (m + 2) * f z)
    (hL2 : Integrable (L2dens Λ R m f)) :
    ∃ F : CuspForm (Λ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) ((m + 2 : ℕ) : ℤ),
      ∀ z : ℍ, F z = f (z : ℂ) := by
  refine ⟨{ toFun := fun z : ℍ => f (z : ℂ)
            slash_action_eq' := ?_
            holo' := ?_
            zero_at_cusps' := ?_ }, fun z => rfl⟩
  · intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hg
    funext z
    refine (slash_action_eq'_iff ((m + 2 : ℕ) : ℤ) (fun w : ℍ => f (w : ℂ)) γ z).2 ?_
    have hz : (z : ℂ) ∈ U := z.im_pos
    have := hmod γ hγ z hz
    rw [mob_coe] at this
    rw [this, zpow_natCast]
    rfl
  · rw [UpperHalfPlane.mdifferentiable_iff]
    refine hf.congr fun w hw => ?_
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  · intro c hc
    have hc' := IsCusp.mono (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) Λ) hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc']
    intro g _
    exact isZeroAtImInfty_hs hm hneg hR hf hmod hL2 g

end TernaryPeriodPolynomials.Argument.ESFoundations.CuspL2
