module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.System

@[expose] public section


/-!
# Pointwise equations for smooth weak solutions

A smooth pair satisfying the weak closedness and co-closedness equations satisfies the system
pointwise (`strong_closed`, `strong_coclosed`); `weyl_closed_coclosed_strong` combines this with
Weyl's lemma.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace ENNReal

section Strong

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Set ℂ} {Hm : ℂ → E →L[ℝ] E}

/-- Integration by parts for a test function against a function smooth on the open set. -/
theorem ibp_testU (hU : IsOpen U) {ψ : ℂ → ℝ} (hψ : IsTest ψ) (hψU : tsupport ψ ⊆ U)
    {g : ℂ → E} (hg : ContDiffOn ℝ ∞ g U) (j : Fin 2) :
    ∫ z, ψ z • fderiv ℝ g z (dir j) = - ∫ z, fderiv ℝ ψ z (dir j) • g z := by
  have hgl : LocallyIntegrableOn g U volume := hg.continuousOn.locallyIntegrableOn hU.measurableSet
  have hdg : ContDiffOn ℝ ∞ (fun z => fderiv ℝ g z (dir j)) U :=
    (hg.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hdgl : LocallyIntegrableOn (fun z => fderiv ℝ g z (dir j)) U volume :=
    hdg.continuousOn.locallyIntegrableOn hU.measurableSet
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (integrable_cutoff_smul hgl (hψ.fderiv_apply _) (hψ.fderiv_compact _)
      ((tsupport_fderiv_apply_subset _).trans hψU))
    (integrable_cutoff_smul hdgl hψ.continuous hψ.2 hψU)
    (integrable_cutoff_smul hgl hψ.continuous hψ.2 hψU)
    (fun x _ => hψ.1.differentiable (by simp) x)
    (fun x hx => ((hg x (hψU hx)).contDiffAt (hU.mem_nhds (hψU hx))).differentiableAt (by simp))

theorem strong_closed (hU : IsOpen U) {a b : ℂ → E} (ha : ContDiffOn ℝ ∞ a U)
    (hb : ContDiffOn ℝ ∞ b U)
    (hcl : ∀ ψ : ℂ → ℝ, IsTest ψ → tsupport ψ ⊆ U →
      ∫ z, fderiv ℝ ψ z (dir 0) • b z = ∫ z, fderiv ℝ ψ z (dir 1) • a z) :
    ∀ z ∈ U, fderiv ℝ b z (dir 0) = fderiv ℝ a z (dir 1) := by
  set F : ℂ → E := fun z => fderiv ℝ b z (dir 0) - fderiv ℝ a z (dir 1) with hF
  have hFc : ContinuousOn F U :=
    (((hb.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const).sub
      ((ha.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const)).continuousOn
  have hFl : LocallyIntegrableOn F U volume := hFc.locallyIntegrableOn hU.measurableSet
  have hae : ∀ᵐ z, z ∈ U → F z = 0 :=
    hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hFl fun ψ hψd hψc hψU => by
      have hψ : IsTest ψ := ⟨hψd, hψc⟩
      have i0 : Integrable fun z => ψ z • fderiv ℝ b z (dir 0) := by
        have hdg : ContDiffOn ℝ ∞ (fun z => fderiv ℝ b z (dir 0)) U :=
          (hb.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
        exact integrable_cutoff_smul (hdg.continuousOn.locallyIntegrableOn hU.measurableSet)
          hψ.continuous hψ.2 hψU
      have i1 : Integrable fun z => ψ z • fderiv ℝ a z (dir 1) := by
        have hdg : ContDiffOn ℝ ∞ (fun z => fderiv ℝ a z (dir 1)) U :=
          (ha.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
        exact integrable_cutoff_smul (hdg.continuousOn.locallyIntegrableOn hU.measurableSet)
          hψ.continuous hψ.2 hψU
      have e : (fun z => ψ z • F z) = fun z =>
          ψ z • fderiv ℝ b z (dir 0) - ψ z • fderiv ℝ a z (dir 1) := funext fun z => smul_sub _ _ _
      rw [e, integral_sub i0 i1, ibp_testU hU hψ hψU hb, ibp_testU hU hψ hψU ha, hcl ψ hψ hψU]
      simp
  have hF0 : F =ᵐ[volume.restrict U] 0 := by
    rw [EventuallyEq, ae_restrict_iff' hU.measurableSet]
    filter_upwards [hae] with z hz hzU using hz hzU
  intro z hz
  have := Measure.eqOn_open_of_ae_eq hF0 hU hFc continuousOn_const hz
  exact sub_eq_zero.mp this

theorem strong_coclosed (hH : HField U Hm) {a b : ℂ → E} (ha : ContDiffOn ℝ ∞ a U)
    (hb : ContDiffOn ℝ ∞ b U)
    (hco : ∀ φ : ℂ → E, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, (⟪fderiv ℝ φ z (dir 0), Hm z (a z)⟫_ℝ + ⟪fderiv ℝ φ z (dir 1), Hm z (b z)⟫_ℝ) = 0) :
    ∀ z ∈ U, fderiv ℝ (fun z => Hm z (a z)) z (dir 0) +
      fderiv ℝ (fun z => Hm z (b z)) z (dir 1) = 0 := by
  have hU := hH.isOpen
  have hHa : ContDiffOn ℝ ∞ (fun z => Hm z (a z)) U := hH.smooth.clm_apply ha
  have hHb : ContDiffOn ℝ ∞ (fun z => Hm z (b z)) U := hH.smooth.clm_apply hb
  set V : ℂ → E := fun z => fderiv ℝ (fun z => Hm z (a z)) z (dir 0) +
    fderiv ℝ (fun z => Hm z (b z)) z (dir 1) with hV
  have hVc : ContinuousOn V U :=
    (((hHa.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const).add
      ((hHb.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const)).continuousOn
  have hVl : LocallyIntegrableOn V U volume := hVc.locallyIntegrableOn hU.measurableSet
  have hae : ∀ᵐ z, z ∈ U → V z = 0 :=
    hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hVl fun ψ hψd hψc hψU => by
      have hψ : IsTest ψ := ⟨hψd, hψc⟩
      have hdHa : ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fun z => Hm z (a z)) z (dir 0)) U :=
        (hHa.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
      have hdHb : ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fun z => Hm z (b z)) z (dir 1)) U :=
        (hHb.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
      have i0 := integrable_cutoff_smul (hdHa.continuousOn.locallyIntegrableOn hU.measurableSet)
        hψ.continuous hψ.2 hψU
      have i1 := integrable_cutoff_smul (hdHb.continuousOn.locallyIntegrableOn hU.measurableSet)
        hψ.continuous hψ.2 hψU
      have j0 := integrable_cutoff_smul (hHa.continuousOn.locallyIntegrableOn hU.measurableSet)
        (hψ.fderiv_apply (dir 0)) (hψ.fderiv_compact (dir 0))
        ((tsupport_fderiv_apply_subset _).trans hψU)
      have j1 := integrable_cutoff_smul (hHb.continuousOn.locallyIntegrableOn hU.measurableSet)
        (hψ.fderiv_apply (dir 1)) (hψ.fderiv_compact (dir 1))
        ((tsupport_fderiv_apply_subset _).trans hψU)
      have hweak : ∫ z, (fderiv ℝ ψ z (dir 0) • Hm z (a z) + fderiv ℝ ψ z (dir 1) • Hm z (b z)) = 0 := by
        refine integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ (j0.add j1) fun e => ?_
        have hφd : ContDiff ℝ ∞ fun z => ψ z • e := hψ.1.smul contDiff_const
        have hφc : HasCompactSupport fun z => ψ z • e :=
          hψ.2.mono' fun z hz => subset_tsupport ψ fun h0 => hz (by simp [h0])
        have hφU : tsupport (fun z => ψ z • e) ⊆ U := (tsupport_smul_subset_left _ _).trans hψU
        have := hco _ hφd hφc hφU
        refine Eq.trans (integral_congr_ae (Eventually.of_forall fun z => ?_)) this
        simp only [fderiv_smul_const (hψ.1.differentiable (by simp) z),
          ContinuousLinearMap.smulRight_apply, inner_add_right, inner_smul_right,
          inner_smul_left, RCLike.conj_to_real]
      have e : (fun z => ψ z • V z) = fun z =>
          ψ z • fderiv ℝ (fun z => Hm z (a z)) z (dir 0) +
            ψ z • fderiv ℝ (fun z => Hm z (b z)) z (dir 1) := funext fun z => smul_add _ _ _
      rw [e, integral_add i0 i1, ibp_testU hU hψ hψU hHa, ibp_testU hU hψ hψU hHb,
        ← neg_add, ← integral_add j0 j1, hweak]
      simp
  have hV0 : V =ᵐ[volume.restrict U] 0 := by
    rw [EventuallyEq, ae_restrict_iff' hU.measurableSet]
    filter_upwards [hae] with z hz hzU using hz hzU
  intro z hz
  exact Measure.eqOn_open_of_ae_eq hV0 hU hVc continuousOn_const hz

/-- **Weyl's lemma for the closed and co-closed system, with the pointwise equations.** -/
theorem weyl_closed_coclosed_strong (hH : HField U Hm) {a b : ℂ → E}
    (ha : ∀ K : Set ℂ, IsCompact K → K ⊆ U → MemLp a 2 (volume.restrict K))
    (hb : ∀ K : Set ℂ, IsCompact K → K ⊆ U → MemLp b 2 (volume.restrict K))
    (hcl : ∀ ψ : ℂ → ℝ, IsTest ψ → tsupport ψ ⊆ U →
      ∫ z, fderiv ℝ ψ z (dir 0) • b z = ∫ z, fderiv ℝ ψ z (dir 1) • a z)
    (hco : ∀ φ : ℂ → E, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, (⟪fderiv ℝ φ z (dir 0), Hm z (a z)⟫_ℝ + ⟪fderiv ℝ φ z (dir 1), Hm z (b z)⟫_ℝ) = 0) :
    ∃ a' b' : ℂ → E, ContDiffOn ℝ ∞ a' U ∧ ContDiffOn ℝ ∞ b' U ∧
      a =ᵐ[volume.restrict U] a' ∧ b =ᵐ[volume.restrict U] b' ∧
      (∀ z ∈ U, fderiv ℝ b' z (dir 0) = fderiv ℝ a' z (dir 1)) ∧
      (∀ z ∈ U, fderiv ℝ (fun z => Hm z (a' z)) z (dir 0) +
        fderiv ℝ (fun z => Hm z (b' z)) z (dir 1) = 0) := by
  have hU := hH.isOpen
  obtain ⟨a', b', ha', hb', hae, hbe⟩ := weyl_closed_coclosed hH ha hb hcl hco
  have hae' : ∀ᵐ z, z ∈ U → a z = a' z := (ae_restrict_iff' hU.measurableSet).mp hae
  have hbe' : ∀ᵐ z, z ∈ U → b z = b' z := (ae_restrict_iff' hU.measurableSet).mp hbe
  have hcl' : ∀ ψ : ℂ → ℝ, IsTest ψ → tsupport ψ ⊆ U →
      ∫ z, fderiv ℝ ψ z (dir 0) • b' z = ∫ z, fderiv ℝ ψ z (dir 1) • a' z := by
    intro ψ hψ hψU
    have e0 : ∫ z, fderiv ℝ ψ z (dir 0) • b' z = ∫ z, fderiv ℝ ψ z (dir 0) • b z := by
      refine integral_congr_ae ?_
      filter_upwards [hbe'] with z hz
      by_cases hzU : z ∈ U
      · rw [hz hzU]
      · simp [fderiv_of_notMem_tsupport ℝ fun h => hzU (hψU h)]
    have e1 : ∫ z, fderiv ℝ ψ z (dir 1) • a z = ∫ z, fderiv ℝ ψ z (dir 1) • a' z := by
      refine integral_congr_ae ?_
      filter_upwards [hae'] with z hz
      by_cases hzU : z ∈ U
      · rw [hz hzU]
      · simp [fderiv_of_notMem_tsupport ℝ fun h => hzU (hψU h)]
    rw [e0, hcl ψ hψ hψU, e1]
  have hco' : ∀ φ : ℂ → E, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, (⟪fderiv ℝ φ z (dir 0), Hm z (a' z)⟫_ℝ + ⟪fderiv ℝ φ z (dir 1), Hm z (b' z)⟫_ℝ) = 0 := by
    intro φ hφ hφc hφU
    rw [← hco φ hφ hφc hφU]
    refine integral_congr_ae ?_
    filter_upwards [hae', hbe'] with z h1 h2
    by_cases hzU : z ∈ U
    · rw [h1 hzU, h2 hzU]
    · simp [fderiv_of_notMem_tsupport ℝ fun h => hzU (hφU h)]
  exact ⟨a', b', ha', hb', hae, hbe, strong_closed hU ha' hb' hcl',
    strong_coclosed hH ha' hb' hco'⟩

end Strong

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
