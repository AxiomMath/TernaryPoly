module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HyperbolicUnfold

@[expose] public section


/-!
# Hyperbolic `lintegral`s and unfolding along the partition of unity

Foundation file of the unconditional Eichler--Shimura route.  `lintegral` versions, for `ℝ≥0∞`-valued functions, of the flat/hyperbolic
conversion (`lintegral_flat_eq_hyp`), of the `SL(2, ℤ)`-invariance (`lintegral_smul_hyp`) and of
the unfolding along the partition of unity (`lintegral_unfold_cutoff`):
`∫ g = ∫ cutoff · Σ_{γ ∈ Γ} g(γ •)`.  No finiteness or integrability hypotheses are needed.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory UpperHalfPlane Complex
open scoped NNReal ENNReal MatrixGroups

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.ESFoundations.Global

/-- Flat Lebesgue `lintegral` of a function supported in `U` as a hyperbolic `lintegral`. -/
theorem lintegral_flat_eq_hyp (F : ℂ → ℝ≥0∞) (hm : Measurable F) (hF : ∀ x, x ∉ U → F x = 0) :
    ∫⁻ x : ℂ, F x = ∫⁻ z : ℍ, F (z : ℂ) * ENNReal.ofReal ((z.im : ℝ) ^ 2) ∂volume := by
  have hcont : Continuous fun z : ℍ => (((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) :
      ℝ≥0∞) := by
    refine ENNReal.continuous_coe.comp (Continuous.pow (Continuous.div₀ continuous_const ?_ ?_) _)
    · exact continuous_im.subtype_mk _
    · exact fun x ↦ NNReal.ne_iff.mp x.im_ne_zero
  have hg : Measurable fun z : ℍ => F (z : ℂ) * ENNReal.ofReal ((z.im : ℝ) ^ 2) :=
    (hm.comp UpperHalfPlane.measurable_coe).mul
      (ENNReal.measurable_ofReal.comp ((UpperHalfPlane.continuous_im.measurable).pow_const 2))
  rw [UpperHalfPlane.volume_def,
    lintegral_withDensity_eq_lintegral_mul _ hcont.measurable hg]
  have h1 : ∀ x : ℍ, ((↑((1 / NNReal.mk x.im x.im_pos.le) ^ 2 : ℝ≥0) : ℝ≥0∞) *
      (F (x : ℂ) * ENNReal.ofReal ((x.im : ℝ) ^ 2))) = F (x : ℂ) := by
    intro x
    have hy : (x.im : ℝ) ≠ 0 := x.im_pos.ne'
    have hpos : 0 < (x.im : ℝ) := x.im_pos
    have e1 : (↑((1 / NNReal.mk x.im x.im_pos.le) ^ 2 : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (1 / (x.im : ℝ) ^ 2) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      simp [one_div, inv_pow]
    rw [e1, mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
    have : 1 / (x.im : ℝ) ^ 2 * (x.im : ℝ) ^ 2 = 1 := by field_simp
    rw [this, ENNReal.ofReal_one, mul_one]
  simp_rw [Pi.mul_apply, h1]
  have hmeas2 : MeasurableEmbedding UpperHalfPlane.coe := UpperHalfPlane.measurableEmbedding_coe
  have h2 := hmeas2.lintegral_map (μ := Measure.comap UpperHalfPlane.coe volume) F
  rw [hmeas2.map_comap] at h2
  rw [← h2]
  have hrange : Set.range UpperHalfPlane.coe = U := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩; exact z.im_pos
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange]
  have : ∫⁻ x in U, F x = ∫⁻ x, F x := by
    rw [← lintegral_indicator isOpen_U.measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ U
    · simp [Set.indicator, hx]
    · simp [Set.indicator, hx, hF x hx]
  rw [this]

theorem lintegral_smul_hyp (γ : SL(2, ℤ)) (g : ℍ → ℝ≥0∞) :
    ∫⁻ z : ℍ, g (γ • z) ∂volume = ∫⁻ z : ℍ, g z ∂volume := by
  have h := measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ) (volume : Measure ℍ)
  exact h.lintegral_comp_emb (measurableEmbedding_const_smul
    (Matrix.SpecialLinearGroup.mapGL ℝ γ)) g

variable {Γ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)}

theorem measurable_cutoff_coe (hR : IsCover Γ R) :
    Measurable fun z : ℍ => cutoff Γ R (z : ℂ) := by
  have h1 : ContinuousOn (cutoff Γ R) U := (contDiffOn_cutoff Γ R hR).continuousOn
  exact (h1.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)).measurable

theorem measurable_smul_hyp (γ : SL(2, ℤ)) : Measurable fun z : ℍ => γ • z := by
  have : Continuous fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ) • z :=
    continuous_const_smul _
  exact this.measurable

theorem tsum_ofReal_cutoff (hR : IsCover Γ R) (z : ℍ) :
    ∑' γ : Γ, ENNReal.ofReal (cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z)) = 1 := by
  have hz : (z : ℂ) ∈ U := z.im_pos
  have hfs := hasFiniteSupport_cutoff Γ R hz
  have h1 := finsum_cutoff (Γ := Γ) (R := R) hR hz
  have hsum : Summable fun γ : Γ => cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) :=
    summable_of_hasFiniteSupport hfs
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun γ => cutoff_nonneg Γ R _) hsum,
    tsum_eq_finsum hfs, h1, ENNReal.ofReal_one]

/-- **Unfolding along the partition of unity for `lintegral`s.** -/
theorem lintegral_unfold_cutoff (hR : IsCover Γ R) (g : ℍ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z : ℍ, g z ∂volume =
      ∫⁻ z : ℍ, ENNReal.ofReal (cutoff Γ R (z : ℂ)) * ∑' γ : Γ, g ((γ : SL(2, ℤ)) • z) ∂volume := by
  have hmat : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  have hcnt : Countable (SL(2, ℤ)) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  have : Countable Γ := inferInstance
  have hcut : Measurable fun z : ℍ => ENNReal.ofReal (cutoff Γ R (z : ℂ)) :=
    ENNReal.measurable_ofReal.comp (measurable_cutoff_coe hR)
  have hterm : ∀ γ : Γ, Measurable fun z : ℍ =>
      ENNReal.ofReal (cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z)) * g z := fun γ => by
    have : Measurable fun z : ℍ => cutoff Γ R ((((γ : SL(2, ℤ))⁻¹ • z : ℍ)) : ℂ) :=
      (measurable_cutoff_coe hR).comp (measurable_smul_hyp _)
    simp only [mob_coe]
    exact (ENNReal.measurable_ofReal.comp this).mul hg
  have h1 : ∀ z : ℍ, g z = ∑' γ : Γ,
      ENNReal.ofReal (cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z)) * g z := fun z => by
    rw [ENNReal.tsum_mul_right, tsum_ofReal_cutoff hR z, one_mul]
  calc ∫⁻ z : ℍ, g z ∂volume
      = ∫⁻ z : ℍ, ∑' γ : Γ, ENNReal.ofReal (cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z)) * g z ∂volume :=
        lintegral_congr fun z => h1 z
    _ = ∑' γ : Γ, ∫⁻ z : ℍ, ENNReal.ofReal (cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z)) * g z ∂volume :=
        lintegral_tsum fun γ => (hterm γ).aemeasurable
    _ = ∑' γ : Γ, ∫⁻ z : ℍ, ENNReal.ofReal (cutoff Γ R (z : ℂ)) *
          g ((γ : SL(2, ℤ)) • z) ∂volume := by
        refine tsum_congr fun γ => ?_
        rw [← lintegral_smul_hyp (γ : SL(2, ℤ))]
        refine lintegral_congr fun w => ?_
        simp only [mob_inv_smul]
    _ = ∫⁻ z : ℍ, ∑' γ : Γ, ENNReal.ofReal (cutoff Γ R (z : ℂ)) *
          g ((γ : SL(2, ℤ)) • z) ∂volume :=
        (lintegral_tsum fun γ =>
          (hcut.mul (hg.comp (measurable_smul_hyp _))).aemeasurable).symm
    _ = _ := by
        refine lintegral_congr fun z => ?_
        rw [ENNReal.tsum_mul_left]

end TernaryPeriodPolynomials.Argument.ESFoundations.Global
