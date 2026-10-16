module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Slash
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HyperbolicUnfold

@[expose] public section


/-!
# The hyperbolic measure and the weight `ϑ`

`hmeas` is the hyperbolic measure on `ℂ` (supported on the upper half plane).  For a finite-index
subgroup `Γ`, a cover radius `R` and positive weights `a γ` summing to `1`, the weight
`ϑ = ∑ a γ · χ(γ⁻¹ ·)` is continuous and positive on the upper half plane and bounded by `1`, and
integrating a `Γ`-invariant function against `ϑ` is the same as integrating it against the cutoff `χ`
(`lintegral_theta_mul`).  This lets the Hilbert space of `L²` forms be defined without a
fundamental domain.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex UpperHalfPlane
open scoped ContDiff InnerProductSpace MatrixGroups ENNReal NNReal

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_mul mob_one)

/-- The hyperbolic measure `dx dy / y²` on the upper half plane, as a measure on `ℂ`. -/
def hmeas : Measure ℂ := Measure.map UpperHalfPlane.coe (volume : Measure ℍ)

theorem measurable_mob (γ : SL(2, ℤ)) : Measurable (mob γ) := by
  classical
  have hU : MeasurableSet U := isOpen_U.measurableSet
  have h1 : ContinuousOn (mob γ) U := (Partition.contDiffOn_mob γ (n := 0)).continuousOn
  have h2 : ContinuousOn (mob γ) Uᶜ := by
    have hc : ∀ z ∈ Uᶜ, mob γ z = mob γ 0 := fun z hz => by
      unfold mob
      rw [UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos (w := z) (w' := 0) (by simpa [U] using hz) (by simp)]
    exact continuousOn_const.congr hc
  have := ContinuousOn.measurable_piecewise (f := mob γ) (g := mob γ) (s := U) h1 h2 hU
  simpa using this

theorem hmeas_apply {s : Set ℂ} (hs : MeasurableSet s) :
    hmeas s = ∫⁻ z in s ∩ U, ENNReal.ofReal (1 / z.im ^ 2) := by
  unfold hmeas
  rw [Measure.map_apply UpperHalfPlane.measurable_coe hs, UpperHalfPlane.volume_eq_lintegral,
    Set.image_preimage_eq_inter_range]
  have hrange : Set.range UpperHalfPlane.coe = U := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩; exact z.im_pos
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange]
  refine setLIntegral_congr_fun (hs.inter isOpen_U.measurableSet) fun z hz => ?_
  have hy : 0 < z.im := hz.2
  rw [ENNReal.ofReal, Real.toNNReal]
  congr 1
  ext
  simp [abs_of_pos hy]
  positivity

theorem hmeas_compl : hmeas Uᶜ = 0 := by
  rw [hmeas_apply isOpen_U.measurableSet.compl]
  simp

theorem ae_hmeas_mem : ∀ᵐ z ∂hmeas, z ∈ U := by
  rw [ae_iff]
  exact hmeas_compl

theorem measurePreserving_mob (γ : SL(2, ℤ)) : MeasurePreserving (mob γ) hmeas hmeas := by
  refine ⟨measurable_mob γ, ?_⟩
  unfold hmeas
  rw [Measure.map_map (measurable_mob γ) UpperHalfPlane.measurable_coe]
  have h : (mob γ ∘ UpperHalfPlane.coe) = UpperHalfPlane.coe ∘ (fun w : ℍ => γ • w) := by
    funext w
    exact Partition.mob_coe γ w
  have hsm : Measurable (fun w : ℍ => γ • w) :=
    (measurableEmbedding_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ)).measurable
  have hp : MeasurePreserving (fun w : ℍ => γ • w) volume volume :=
    measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ) (volume : Measure ℍ)
  rw [h, ← Measure.map_map UpperHalfPlane.measurable_coe hsm, hp.map_eq]

theorem lintegral_mob (γ : SL(2, ℤ)) {f : ℂ → ℝ≥0∞} (hf : AEMeasurable f hmeas) :
    ∫⁻ z, f (mob γ z) ∂hmeas = ∫⁻ z, f z ∂hmeas := by
  have h := (measurePreserving_mob γ).map_eq
  conv_rhs => rw [← h]
  exact (lintegral_map' (by rwa [h]) (measurable_mob γ).aemeasurable).symm

/-! ### The weight `ϑ` -/

section Theta

open TernaryPeriodPolynomials.Argument.ESFoundations.Partition
  (cutoff IsCover seed mass cutoff_nonneg contDiffOn_cutoff mass_pos hasFiniteSupport_seed
    seed_nonneg finsum_cutoff)

instance countableSL : Countable SL(2, ℤ) :=
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  (Subtype.val_injective (p := fun A : Matrix (Fin 2) (Fin 2) ℤ => A.det = 1)).countable

variable (Γ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ))

theorem cutoff_le_one (hR : IsCover Γ R) {z : ℂ} (hz : z ∈ U) : cutoff Γ R z ≤ 1 := by
  have hm := mass_pos Γ R hR hz
  have h : seed R z ≤ mass Γ R z := by
    have := single_le_finsum (1 : Γ) (hasFiniteSupport_seed Γ R hz) fun γ => seed_nonneg R _
    simpa [Partition.mass, Partition.mob_one hz] using this
  rw [Partition.cutoff, div_le_one hm]
  exact h

/-- Positive weights on `Γ` which sum to `1`. -/
theorem exists_weights [Countable Γ] [Nonempty Γ] :
    ∃ a : Γ → ℝ, (∀ γ, 0 < a γ) ∧ HasSum a 1 := by
  obtain ⟨f, hf⟩ := exists_injective_nat Γ
  have hp : Summable fun γ : Γ => ((1 : ℝ) / 2) ^ (f γ + 1) := by
    have h0 : Summable fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 1) := by
      simpa [pow_succ] using (summable_geometric_two).mul_right (1 / 2 : ℝ) 
    exact h0.comp_injective hf
  have hpos : ∀ γ : Γ, 0 < ((1 : ℝ) / 2) ^ (f γ + 1) := fun γ => by positivity
  have hs : 0 < ∑' γ : Γ, ((1 : ℝ) / 2) ^ (f γ + 1) := hp.tsum_pos (fun γ => (hpos γ).le)
    (Classical.arbitrary Γ) (hpos _)
  refine ⟨fun γ => ((1 : ℝ) / 2) ^ (f γ + 1) / ∑' γ : Γ, ((1 : ℝ) / 2) ^ (f γ + 1),
    fun γ => div_pos (hpos γ) hs, ?_⟩
  have := hp.hasSum.div_const (∑' γ : Γ, ((1 : ℝ) / 2) ^ (f γ + 1))
  rwa [div_self hs.ne'] at this

theorem hmeas_ac : hmeas ≪ volume.restrict U := by
  have h : hmeas = (volume.restrict U).withDensity (fun z => ENNReal.ofReal (1 / z.im ^ 2)) := by
    ext s hs
    rw [hmeas_apply hs, withDensity_apply _ hs, Measure.restrict_restrict hs]
  rw [h]
  exact withDensity_absolutelyContinuous _ _

theorem aemeasurable_hmeas {β : Type*} [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β]
    {f : ℂ → β} (hf : ContinuousOn f U) : AEMeasurable f hmeas :=
  (hf.aemeasurable isOpen_U.measurableSet).mono_ac hmeas_ac

variable {Γ R}

/-- The weight `ϑ = ∑_γ a_γ cutoff ∘ γ⁻¹`. -/
def theta (Γ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ)) (a : Γ → ℝ) (z : ℂ) : ℝ :=
  ∑' γ : Γ, a γ * cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z)

variable {a : Γ → ℝ}

theorem summable_theta (hR : IsCover Γ R) (ha : ∀ γ, 0 < a γ) (hs : HasSum a 1) (z : ℂ) :
    Summable fun γ : Γ => a γ * cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) :=
  Summable.of_nonneg_of_le (fun γ => mul_nonneg (ha γ).le (cutoff_nonneg Γ R _))
    (fun γ => mul_le_of_le_one_right (ha γ).le
      (cutoff_le_one Γ R hR (Partition.mob_mem _ _))) hs.summable

theorem theta_nonneg (ha : ∀ γ, 0 < a γ) (z : ℂ) : 0 ≤ theta Γ R a z :=
  tsum_nonneg fun γ => mul_nonneg (ha γ).le (cutoff_nonneg Γ R _)

theorem theta_pos (hR : IsCover Γ R) (ha : ∀ γ, 0 < a γ) (hs : HasSum a 1) {z : ℂ} (hz : z ∈ U) :
    0 < theta Γ R a z := by
  have h1 := finsum_cutoff (Γ := Γ) (R := R) hR hz
  have hex : ∃ γ : Γ, cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) ≠ 0 := by
    by_contra hno
    push Not at hno
    rw [finsum_eq_zero_of_forall_eq_zero hno] at h1
    exact zero_ne_one h1
  obtain ⟨γ, hγ⟩ := hex
  exact (summable_theta hR ha hs z).tsum_pos
    (fun γ => mul_nonneg (ha γ).le (cutoff_nonneg Γ R _)) γ
    (mul_pos (ha γ) (lt_of_le_of_ne (cutoff_nonneg Γ R _) (Ne.symm hγ)))

theorem continuousOn_theta (hR : IsCover Γ R) (ha : ∀ γ, 0 < a γ) (hs : HasSum a 1) :
    ContinuousOn (theta Γ R a) U := by
  refine continuousOn_tsum (u := a) (fun γ => ?_) hs.summable (fun γ z hz => ?_)
  · refine continuousOn_const.mul ?_
    refine (contDiffOn_cutoff Γ R hR).continuousOn.comp
      (Partition.contDiffOn_mob (((γ : SL(2, ℤ))⁻¹)) (n := 0)).continuousOn
      (Partition.mapsTo_mob _)
  · rw [Real.norm_of_nonneg (mul_nonneg (ha γ).le (cutoff_nonneg Γ R _))]
    exact mul_le_of_le_one_right (ha γ).le (cutoff_le_one Γ R hR (Partition.mob_mem _ _))

theorem theta_le_one (hR : IsCover Γ R) (ha : ∀ γ, 0 < a γ) (hs : HasSum a 1) (z : ℂ) :
    theta Γ R a z ≤ 1 := by
  rw [← hs.tsum_eq]
  exact (summable_theta hR ha hs z).tsum_le_tsum
    (fun γ => mul_le_of_le_one_right (ha γ).le (cutoff_le_one Γ R hR (Partition.mob_mem _ _)))
    hs.summable

/-- **Unfolding with the weight `ϑ`** (lintegral form): for a `Γ`-invariant `n`, integrating against
`ϑ` is the same as integrating against the cutoff. -/
theorem lintegral_theta_mul (hR : IsCover Γ R) (ha : ∀ γ, 0 < a γ) (hs : HasSum a 1)
    {n : ℂ → ℝ≥0∞} (hn : AEMeasurable n hmeas)
    (hinv : ∀ γ : Γ, ∀ z ∈ U, n (mob (γ : SL(2, ℤ)) z) = n z) :
    ∫⁻ z, ENNReal.ofReal (theta Γ R a z) * n z ∂hmeas =
      ∫⁻ z, ENNReal.ofReal (cutoff Γ R z) * n z ∂hmeas := by
  have hU : ∀ᵐ z ∂hmeas, z ∈ U := ae_hmeas_mem
  -- the integrand of the `γ`-th term
  have hterm : ∀ γ : Γ, ∫⁻ z, ENNReal.ofReal (a γ * cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z)) * n z ∂hmeas =
      ENNReal.ofReal (a γ) * ∫⁻ z, ENNReal.ofReal (cutoff Γ R z) * n z ∂hmeas := by
    intro γ
    set F : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (a γ) * (ENNReal.ofReal (cutoff Γ R w) * n w)
      with hF
    have hcut : AEMeasurable (fun w => ENNReal.ofReal (cutoff Γ R w)) hmeas :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (aemeasurable_hmeas (contDiffOn_cutoff Γ R hR).continuousOn)
    have hFm : AEMeasurable F hmeas := (hcut.mul hn).const_mul _
    have hpt : ∀ᵐ z ∂hmeas, ENNReal.ofReal (a γ * cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z)) * n z =
        F (mob (γ : SL(2, ℤ))⁻¹ z) := by
      filter_upwards [hU] with z hz
      have h1 : n (mob (γ : SL(2, ℤ))⁻¹ z) = n z := by
        have := hinv γ⁻¹ z hz
        rwa [Subgroup.coe_inv] at this
      rw [hF]
      simp only
      rw [h1, ENNReal.ofReal_mul (ha γ).le, mul_assoc]
    rw [lintegral_congr_ae hpt, lintegral_mob _ hFm, hF]
    simp only
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hae : ∀ᵐ z ∂hmeas, ENNReal.ofReal (theta Γ R a z) * n z =
      ∑' γ : Γ, ENNReal.ofReal (a γ * cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z)) * n z := by
    filter_upwards [hU] with z hz
    unfold theta
    rw [ENNReal.ofReal_tsum_of_nonneg (fun γ => mul_nonneg (ha γ).le (cutoff_nonneg Γ R _))
      (summable_theta hR ha hs z), ENNReal.tsum_mul_right]
  rw [lintegral_congr_ae hae, lintegral_tsum, ]
  · simp only [hterm]
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun γ => (ha γ).le) hs.summable,
      hs.tsum_eq]
    simp
  · intro γ
    have hc : AEMeasurable (fun z => ENNReal.ofReal (cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z))) hmeas :=
      ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_hmeas
        ((contDiffOn_cutoff Γ R hR).continuousOn.comp
          (Partition.contDiffOn_mob ((γ : SL(2, ℤ))⁻¹) (n := 0)).continuousOn (Partition.mapsTo_mob _)))
    have : AEMeasurable (fun z => ENNReal.ofReal (a γ) *
        ENNReal.ofReal (cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z))) hmeas := hc.const_mul _
    refine (this.mul hn).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (ha γ).le]

end Theta

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
