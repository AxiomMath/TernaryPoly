module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Locfin

@[expose] public section


/-!
# Averaging a compactly supported field over `Γ`

For a smooth field `ψ : ℂ → ℂ^d` with compact support in the upper half plane, the locally finite sum
`avg ψ = ∑_{γ ∈ Γ} ρ(γ) ψ(γ⁻¹ ·)` is a smooth equivariant function with support compact modulo `Γ`
(`avg_mob`, `contDiffOn_avg`, `fderiv_avg_eq_zero`), and its differential is the locally finite sum of
the slashes `slash γ⁻¹ dψ` (`fderiv_avg`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex UpperHalfPlane
open scoped ContDiff InnerProductSpace MatrixGroups ENNReal NNReal

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_mul mob_one IsCover cutoff cutoff_nonneg)

variable {Γ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)} {d : ℕ}

/-- A smooth `ℂ^d`-valued field with compact support in the upper half plane. -/
def IsTestW (ψ : ℂ → Wd d) : Prop :=
  ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U

namespace HodgeDatum

variable (D : HodgeDatum Γ d)

/-- The `γ`-th translate `ρ(γ) ψ(γ⁻¹ ·)`. -/
def term (ψ : ℂ → Wd d) (γ : Γ) (w : ℂ) : Wd d := D.ρ γ (ψ (mob (γ : SL(2, ℤ))⁻¹ w))

/-- The average `∑_γ ρ(γ) ψ(γ⁻¹ ·)`. -/
def avg (ψ : ℂ → Wd d) (w : ℂ) : Wd d := ∑ᶠ γ : Γ, D.term ψ γ w

variable {D}

/-- Local finiteness: near each point of `U` only finitely many translates are nonzero. -/
theorem exists_local_finite (hR : IsCover Γ R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) {z : ℂ} (hz : z ∈ U) :
    ∃ V : Set ℂ, V ∈ 𝓝 z ∧ ∃ T : Finset Γ, ∀ w ∈ V, ∀ γ : Γ,
      (mob (γ : SL(2, ℤ))⁻¹ w ∈ tsupport ψ) → γ ∈ T := by
  set r := z.im / 2 with hr
  have hr0 : 0 < r := by have : 0 < z.im := hz; positivity
  have hCU : Metric.closedBall z r ⊆ U := by
    intro w hw
    have h1 : |w.im - z.im| ≤ r := (Complex.abs_im_le_norm (w - z)).trans (by simpa [dist_eq_norm] using hw)
    have h2 := (abs_le.mp h1).1
    show 0 < w.im
    have : 0 < z.im := hz
    simp only [hr] at h2
    linarith
  have hfin := finite_moving hR (isCompact_closedBall z r) hCU hψ.2.1 hψ.2.2
  have hfin' : {γ : Γ | ∃ w ∈ Metric.closedBall z r, mob (γ : SL(2, ℤ))⁻¹ w ∈ tsupport ψ}.Finite := by
    refine (hfin.preimage (inv_injective.injOn)).subset ?_
    rintro γ ⟨w, hw, hk⟩
    exact ⟨w, hw, by simpa using hk⟩
  refine ⟨Metric.closedBall z r, Metric.closedBall_mem_nhds z hr0, hfin'.toFinset, fun w hw γ hk => ?_⟩
  exact hfin'.mem_toFinset.mpr ⟨w, hw, hk⟩

theorem term_eq_zero_of_notMem {ψ : ℂ → Wd d} {γ : Γ} {w : ℂ}
    (h : mob (γ : SL(2, ℤ))⁻¹ w ∉ tsupport ψ) : D.term ψ γ w = 0 := by
  unfold term
  rw [image_eq_zero_of_notMem_tsupport h, map_zero]

theorem finite_support_term (hR : IsCover Γ R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) {z : ℂ} (hz : z ∈ U) :
    (Function.support fun γ : Γ => D.term ψ γ z).Finite := by
  obtain ⟨V, hV, T, hT⟩ := exists_local_finite hR hψ hz
  refine T.finite_toSet.subset fun γ hγ => hT z (mem_of_mem_nhds hV) γ ?_
  by_contra h
  exact hγ (term_eq_zero_of_notMem h)

theorem avg_eventually (hR : IsCover Γ R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) {z : ℂ} (hz : z ∈ U) :
    ∃ T : Finset Γ, ∀ᶠ w in 𝓝 z, D.avg ψ w = ∑ γ ∈ T, D.term ψ γ w := by
  obtain ⟨V, hV, T, hT⟩ := exists_local_finite hR hψ hz
  refine ⟨T, ?_⟩
  filter_upwards [hV] with w hw
  unfold avg
  refine finsum_eq_sum_of_support_subset _ fun γ hγ => ?_
  refine T.mem_coe.mpr (hT w hw γ ?_)
  by_contra h
  exact hγ (term_eq_zero_of_notMem h)

theorem contDiff_term (ψ : ℂ → Wd d) (hψ : ContDiff ℝ ∞ ψ) (γ : Γ) :
    ContDiffOn ℝ ∞ (D.term ψ γ) U :=
  (D.ρR γ).contDiff.comp_contDiffOn
    (hψ.comp_contDiffOn (Partition.contDiffOn_mob ((γ : SL(2, ℤ))⁻¹)))

theorem contDiffOn_avg (hR : IsCover Γ R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) :
    ContDiffOn ℝ ∞ (D.avg ψ) U := by
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  obtain ⟨T, hT⟩ := avg_eventually (D := D) hR hψ hz
  obtain ⟨V, hVsub, hVo, hzV⟩ := mem_nhds_iff.mp hT
  refine ⟨V, hVo, hzV, ?_⟩
  have : ContDiffOn ℝ ∞ (fun w => ∑ γ ∈ T, D.term ψ γ w) (U ∩ V) :=
    ContDiffOn.sum fun γ _ => (contDiff_term ψ hψ.1 γ).mono inter_subset_left
  exact this.congr fun w hw => hVsub hw.2

theorem avg_mob (hR : IsCover Γ R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) (δ : Γ) {z : ℂ} (hz : z ∈ U) :
    D.avg ψ (mob (δ : SL(2, ℤ)) z) = D.ρ δ (D.avg ψ z) := by
  have e : ∀ γ : Γ, D.term ψ (δ * γ) (mob (δ : SL(2, ℤ)) z) = D.ρ δ (D.term ψ γ z) := by
    intro γ
    unfold term
    rw [map_mul, ← mob_mul]
    have h : (((δ * γ : Γ) : SL(2, ℤ))⁻¹ * (δ : SL(2, ℤ))) = (γ : SL(2, ℤ))⁻¹ := by simp
    rw [h]
    rfl
  unfold avg
  rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
  simp only [Equiv.coe_mulLeft, e]
  exact (map_finsum (D.ρ δ) (finite_support_term hR hψ hz)).symm

theorem eqvFun_avg (hR : IsCover Γ R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) : D.EqvFun (D.avg ψ) :=
  fun δ _ hz => avg_mob hR hψ δ hz

/-- The average vanishes near points not in the orbit of the support. -/
theorem avg_eventually_zero (hR : IsCover Γ R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) {z : ℂ} (hz : z ∈ U)
    (hfree : ∀ γ : Γ, mob (γ : SL(2, ℤ)) z ∉ tsupport ψ) : D.avg ψ =ᶠ[𝓝 z] 0 := by
  obtain ⟨V, hV, T, hT⟩ := exists_local_finite hR hψ hz
  have hzU : U ∈ 𝓝 z := isOpen_U.mem_nhds hz
  have hT' : ∀ γ : Γ, ∀ᶠ w in 𝓝 z, mob (γ : SL(2, ℤ))⁻¹ w ∉ tsupport ψ := by
    intro γ
    have hc : ContinuousAt (mob ((γ : SL(2, ℤ))⁻¹)) z :=
      (Partition.contDiffOn_mob ((γ : SL(2, ℤ))⁻¹) (n := 0)).continuousOn.continuousAt hzU
    exact hc.eventually_mem ((isClosed_tsupport ψ).isOpen_compl.mem_nhds (by simpa using hfree γ⁻¹))
  filter_upwards [hV, (Filter.eventually_all_finset T).mpr fun γ _ => hT' γ] with w hw hwT
  unfold avg
  refine finsum_eq_zero_of_forall_eq_zero fun γ => term_eq_zero_of_notMem fun hk => ?_
  exact hwT γ (hT w hw γ hk) hk

theorem fderiv_avg_eq_zero (hR : IsCover Γ R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) {z : ℂ} (hz : z ∈ U)
    (hfree : ∀ γ : Γ, mob (γ : SL(2, ℤ)) z ∉ tsupport ψ) : fderiv ℝ (D.avg ψ) z = 0 := by
  have := (avg_eventually_zero (D := D) hR hψ hz hfree).fderiv_eq (𝕜 := ℝ)
  rw [this]
  simp

theorem fderiv_term {ψ : ℂ → Wd d} (hψ : ContDiff ℝ ∞ ψ) (γ : Γ) {w : ℂ} (hw : w ∈ U) :
    fderiv ℝ (D.term ψ γ) w = D.slash γ⁻¹ (fun w => fderiv ℝ ψ w) w := by
  rw [D.slash_fderiv γ⁻¹ (hψ.differentiable (by simp)).differentiableOn hw]
  simp only [inv_inv, Subgroup.coe_inv]
  rfl

theorem fderiv_avg (hR : IsCover Γ R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) {z : ℂ} (hz : z ∈ U) :
    fderiv ℝ (D.avg ψ) z = ∑ᶠ γ : Γ, D.slash γ⁻¹ (fun w => fderiv ℝ ψ w) z := by
  obtain ⟨V, hV, T, hT⟩ := exists_local_finite hR hψ hz
  have hev : D.avg ψ =ᶠ[𝓝 z] fun w => ∑ γ ∈ T, D.term ψ γ w := by
    filter_upwards [hV] with w hw
    unfold avg
    refine finsum_eq_sum_of_support_subset _ fun γ hγ => ?_
    refine T.mem_coe.mpr (hT w hw γ ?_)
    by_contra h
    exact hγ (term_eq_zero_of_notMem h)
  have hdiff : ∀ γ ∈ T, DifferentiableAt ℝ (D.term ψ γ) z := fun γ _ =>
    ((contDiff_term (D := D) ψ hψ.1 γ).differentiableOn (by simp)).differentiableAt
      (isOpen_U.mem_nhds hz)
  rw [hev.fderiv_eq, fderiv_fun_sum hdiff]
  have hzero : ∀ γ : Γ, γ ∉ T → D.slash γ⁻¹ (fun w => fderiv ℝ ψ w) z = 0 := by
    intro γ hγ
    rw [← fderiv_term hψ.1 γ hz]
    have : D.term ψ γ =ᶠ[𝓝 z] 0 := by
      filter_upwards [hV] with w hw
      exact term_eq_zero_of_notMem fun h => hγ (hT w hw γ h)
    rw [this.fderiv_eq]
    simp
  rw [finsum_eq_sum_of_support_subset _ (s := T)]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    exact fderiv_term hψ.1 γ hz
  · intro γ hγ
    by_contra h
    exact hγ (hzero γ h)

end HodgeDatum

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
