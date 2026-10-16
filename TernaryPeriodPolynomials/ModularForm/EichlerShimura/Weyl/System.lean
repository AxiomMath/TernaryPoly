module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.Coclosed

@[expose] public section


/-!
# Weyl's lemma for weakly closed and co-closed pairs

`weyl_closed_coclosed`: locally square integrable `(a, b)` with `∂₀ b = ∂₁ a` and
`∂₀ (H a) + ∂₁ (H b) = 0` in the weak sense (`H` a smooth field of invertible symmetric operators)
agree almost everywhere with smooth functions.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace ENNReal

section Red

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem smul_mkX (c : ℝ) (a b : E) : c • mkX a b = mkX (c • a) (c • b) := rfl
theorem add_mkX (a b c d : E) : mkX a b + mkX c d = mkX (a + c) (b + d) := rfl

/-- The embedding `a ↦ (a, 0)`. -/
def inlX : E →L[ℝ] XP E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.inl ℝ E E)

@[simp] theorem inlX_apply (a : E) : inlX a = mkX a 0 := rfl

theorem mkX_eq_add (a b : E) : mkX a b = inlX a + inrX b := by
  simp [add_mkX]

theorem norm_mkX_le (a b : E) : ‖mkX a b‖ ≤ ‖a‖ + ‖b‖ := by
  have h : ‖mkX a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    simp [mkX, WithLp.prod_norm_sq_eq_of_L2]
  nlinarith [norm_nonneg (mkX a b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖mkX a b‖ - ‖a‖ - ‖b‖)]

theorem memLp_mkX {μ : Measure ℂ} {a b : ℂ → E} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    MemLp (fun z => mkX (a z) (b z)) 2 μ := by
  have hm : AEStronglyMeasurable (fun z => mkX (a z) (b z)) μ :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.continuous.comp_aestronglyMeasurable
      (ha.aestronglyMeasurable.prodMk hb.aestronglyMeasurable)
  exact (ha.norm.add hb.norm).mono' hm (Eventually.of_forall fun z => by
    simpa using norm_mkX_le (a z) (b z))

theorem integral_mkX [FiniteDimensional ℝ E] {f g : ℂ → E} (hf : Integrable f) (hg : Integrable g) :
    ∫ z, mkX (f z) (g z) = mkX (∫ z, f z) (∫ z, g z) := by
  have e : (fun z => mkX (f z) (g z)) = fun z => inlX (f z) + inrX (g z) :=
    funext fun z => mkX_eq_add _ _
  rw [e, integral_add (inlX.integrable_comp hf) (inrX.integrable_comp hg),
    ContinuousLinearMap.integral_comp_comm inlX hf,
    ContinuousLinearMap.integral_comp_comm inrX hg, mkX_eq_add]

theorem locInt_of_locL2 {X : Type*} [NormedAddCommGroup X] {u : ℂ → X} {V : Set ℂ}
    (hV : IsOpen V) (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp u 2 (volume.restrict K)) :
    LocallyIntegrableOn u V volume := by
  rw [locallyIntegrableOn_iff hV.isLocallyClosed]
  intro K hKV hK
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact (hu K hK hKV).integrable one_le_two

variable [FiniteDimensional ℝ E] {U : Set ℂ} {Hm : ℂ → E →L[ℝ] E}

/-- **Regularity of weakly closed and co-closed forms.**  Locally square integrable `(a, b)` with
`∂₀ b = ∂₁ a` and `∂₀ (H a) + ∂₁ (H b) = 0` weakly, `H` a smooth field of invertible symmetric
operators, agree almost everywhere with smooth functions. -/
theorem weyl_closed_coclosed (hH : HField U Hm) {a b : ℂ → E}
    (ha : ∀ K : Set ℂ, IsCompact K → K ⊆ U → MemLp a 2 (volume.restrict K))
    (hb : ∀ K : Set ℂ, IsCompact K → K ⊆ U → MemLp b 2 (volume.restrict K))
    (hcl : ∀ ψ : ℂ → ℝ, IsTest ψ → tsupport ψ ⊆ U →
      ∫ z, fderiv ℝ ψ z (dir 0) • b z = ∫ z, fderiv ℝ ψ z (dir 1) • a z)
    (hco : ∀ φ : ℂ → E, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, (⟪fderiv ℝ φ z (dir 0), Hm z (a z)⟫_ℝ + ⟪fderiv ℝ φ z (dir 1), Hm z (b z)⟫_ℝ) = 0) :
    ∃ a' b' : ℂ → E, ContDiffOn ℝ ∞ a' U ∧ ContDiffOn ℝ ∞ b' U ∧
      a =ᵐ[volume.restrict U] a' ∧ b =ᵐ[volume.restrict U] b' := by
  have hal := locInt_of_locL2 hH.isOpen ha
  have hbl := locInt_of_locL2 hH.isOpen hb
  have hu : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      MemLp (fun z => mkX (a z) (b z)) 2 (volume.restrict K) := fun K hK hKU =>
    memLp_mkX (ha K hK hKU) (hb K hK hKU)
  have heq : ∀ ψ : ℂ → ℝ, IsTest ψ → tsupport ψ ⊆ U →
      ∑ j, Pdirac j (∫ z, fderiv ℝ ψ z (dir j) • mkX (a z) (b z)) =
        ∫ z, ψ z • Qsys Hm z (mkX (a z) (b z)) := by
    intro ψ hψ hψU
    have iA : ∀ j, Integrable fun z => fderiv ℝ ψ z (dir j) • a z := fun j =>
      integrable_cutoff_smul hal (hψ.fderiv_apply _) (hψ.fderiv_compact _)
        ((tsupport_fderiv_apply_subset _).trans hψU)
    have iB : ∀ j, Integrable fun z => fderiv ℝ ψ z (dir j) • b z := fun j =>
      integrable_cutoff_smul hbl (hψ.fderiv_apply _) (hψ.fderiv_compact _)
        ((tsupport_fderiv_apply_subset _).trans hψU)
    have hLHS : ∀ j, ∫ z, fderiv ℝ ψ z (dir j) • mkX (a z) (b z) =
        mkX (∫ z, fderiv ℝ ψ z (dir j) • a z) (∫ z, fderiv ℝ ψ z (dir j) • b z) := by
      intro j
      simp only [smul_mkX]
      exact integral_mkX (iA j) (iB j)
    have hM : ∀ j, ContDiffOn ℝ ∞ (fun z => Gd Hm j z ∘L Hm z) U := fun j =>
      (smooth_Gd hH j).clm_comp hH.smooth
    have i0 := integrable_cutoff_clm hH.isOpen (hM 0) hal hψ.1 hψ.2 hψU
    have i1 := integrable_cutoff_clm hH.isOpen (hM 1) hbl hψ.1 hψ.2 hψU
    have i2 : Integrable fun z => ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z))) := by
      refine (i0.add i1).congr (Eventually.of_forall fun z => ?_)
      simp [smul_add]
    have hQ : (fun z => ψ z • Qsys Hm z (mkX (a z) (b z))) = fun z =>
        inrX (-(ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z))))) := by
      funext z
      simp [Qsys_apply, smul_mkX, smul_neg, smul_add, sub_eq_add_neg]
      rw [add_comm]
    have hRHS : ∫ z, ψ z • Qsys Hm z (mkX (a z) (b z)) =
        mkX 0 (-∫ z, ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z)))) := by
      have i3 : Integrable fun z => -(ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z)))) :=
        i2.neg
      rw [hQ, ContinuousLinearMap.integral_comp_comm inrX i3, integral_neg]
      rfl
    have hco' := coclosed_vec hH hal hbl hco hψ hψU
    have hcl' := hcl ψ hψ hψU
    rw [Fin.sum_univ_two, hLHS 0, hLHS 1, hRHS]
    simp only [Pdirac, Matrix.cons_val_zero, Matrix.cons_val_one, P0_apply, P1_apply, mkX_fst,
      mkX_snd, add_mkX]
    have e1 : (∫ z, fderiv ℝ ψ z (dir 0) • b z) + -∫ z, fderiv ℝ ψ z (dir 1) • a z = 0 := by
      rw [hcl']; simp
    have e2 : (∫ z, fderiv ℝ ψ z (dir 0) • a z) + (∫ z, fderiv ℝ ψ z (dir 1) • b z) =
        -∫ z, ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z))) :=
      eq_neg_of_add_eq_zero_left hco'
    rw [e1, e2]
  obtain ⟨w, hw, huw⟩ := weyl_dirac diracPair_Pdirac hH.isOpen (smooth_Qsys hH) hu heq
  refine ⟨fun z => (w z).fst, fun z => (w z).snd, (fstX (E := E)).contDiff.comp_contDiffOn hw,
    (sndX (E := E)).contDiff.comp_contDiffOn hw, ?_, ?_⟩
  · filter_upwards [huw] with z hz
    exact congrArg (fun x : XP E => x.fst) hz
  · filter_upwards [huw] with z hz
    exact congrArg (fun x : XP E => x.snd) hz

end Red

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
