module

public import Mathlib
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HeightCutoff

@[expose] public section


/-!
# Step 4 of the Eichler–Shimura route: continuity of periods

If `Ψ` is a smooth function on the upper half plane `U` transforming by the cocycle law
`Ψ(δ z) = ρ(δ) Ψ(z) + c(δ)` and `Γ`-equivariant smooth `φ_j` (`φ_j(δ z) = ρ(δ) φ_j(z)`) have
differentials converging to `dΨ` in `L²` on every compact subset of `U`, then `c` is a coboundary
(`isCoboundary_of_tendsto`). This is step 4 of the Eichler–Shimura route: `ω - ω₀` has
coboundary periods.

The proof uses
* a Poincaré inequality with base point on rectangles (`exists_poincare`), by integrating the
  differential along L-shaped paths through a vertical line of minimal energy;
* the change of variables along a translate `z ↦ δ z` with Jacobian `|cz + d|⁻⁴`
  (`exists_integral_comp_mob_le`);
* `exists_coboundary_near`: finitely many values of `c` are within `C ‖Du‖_{L¹(E)}` of a
  coboundary, for a rectangle `E` and constant `C` independent of `u`;
* closedness of the finite-dimensional space of coboundaries in `Γ → W`.

The rectangle integration lemmas (`Rect`, `integral_Rect`, `integral_Rect_swap`,
`integral_Rect_xy`, `integral_Rect_yx`) are by Claude Sonnet 5.5; the rest was written by Claude Opus 5.5.
-/

open MeasureTheory Set Complex intervalIntegral

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.PeriodContinuity

/-- The closed rectangle `[a, b] × [c, d]` in the complex plane. -/
def Rect (a b c d : ℝ) : Set ℂ := {z | z.re ∈ Icc a b ∧ z.im ∈ Icc c d}

theorem Rect_eq_preimage (a b c d : ℝ) :
    Rect a b c d = Complex.measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Icc c d) := rfl

theorem isCompact_Rect (a b c d : ℝ) : IsCompact (Rect a b c d) := by
  have : Rect a b c d = Complex.equivRealProdCLM.toHomeomorph ⁻¹' (Icc a b ×ˢ Icc c d) := rfl
  rw [this, Homeomorph.isCompact_preimage]
  exact isCompact_Icc.prod isCompact_Icc

theorem measurableSet_Rect (a b c d : ℝ) : MeasurableSet (Rect a b c d) :=
  (isCompact_Rect a b c d).measurableSet

theorem mk_mem_Rect {a b c d x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    (⟨x, y⟩ : ℂ) ∈ Rect a b c d := ⟨hx, hy⟩

theorem integral_Rect {h : ℂ → ℝ} {a b c d : ℝ} (hh : ContinuousOn h (Rect a b c d)) :
    ∫ z in Rect a b c d, h z = ∫ x in Icc a b, ∫ y in Icc c d, h ⟨x, y⟩ := by
  have hcomp : ContinuousOn (fun p : ℝ × ℝ => h (Complex.measurableEquivRealProd.symm p))
      (Icc a b ×ˢ Icc c d) := by
    refine hh.comp ?_ ?_
    · exact (Complex.equivRealProdCLM.symm.continuous).continuousOn
    · intro p hp
      exact hp
  have hint : IntegrableOn (fun p : ℝ × ℝ => h (Complex.measurableEquivRealProd.symm p))
      (Icc a b ×ˢ Icc c d) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hcomp.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have h1 := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => h (Complex.measurableEquivRealProd.symm p)) (Icc a b ×ˢ Icc c d)
  simp only [MeasurableEquiv.symm_apply_apply] at h1
  rw [Rect_eq_preimage, h1, Measure.volume_eq_prod, setIntegral_prod _ hint]
  rfl

theorem integral_Rect_swap {h : ℂ → ℝ} {a b c d : ℝ} (hh : ContinuousOn h (Rect a b c d)) :
    ∫ x in Icc a b, ∫ y in Icc c d, h ⟨x, y⟩ = ∫ y in Icc c d, ∫ x in Icc a b, h ⟨x, y⟩ := by
  have hcomp : ContinuousOn (fun p : ℝ × ℝ => h (Complex.measurableEquivRealProd.symm p))
      (Icc a b ×ˢ Icc c d) := by
    refine hh.comp ?_ ?_
    · exact (Complex.equivRealProdCLM.symm.continuous).continuousOn
    · intro p hp
      exact hp
  have hint : IntegrableOn (fun p : ℝ × ℝ => h (Complex.measurableEquivRealProd.symm p))
      (Icc a b ×ˢ Icc c d) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hcomp.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact integral_integral_swap (μ := volume.restrict (Icc a b)) (ν := volume.restrict (Icc c d))
    (f := fun x y => h ⟨x, y⟩) (by
      rw [Measure.prod_restrict]
      exact hint)

theorem integral_Rect_xy {h : ℂ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hh : ContinuousOn h (Rect a b c d)) :
    ∫ z in Rect a b c d, h z = ∫ x in a..b, ∫ y in c..d, h ⟨x, y⟩ := by
  rw [integral_Rect hh, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc]

theorem integral_Rect_yx {h : ℂ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hh : ContinuousOn h (Rect a b c d)) :
    ∫ z in Rect a b c d, h z = ∫ y in c..d, ∫ x in a..b, h ⟨x, y⟩ := by
  rw [integral_Rect hh, integral_Rect_swap hh, intervalIntegral.integral_of_le hcd,
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]

theorem continuousOn_param_im {G : ℂ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hG : ContinuousOn G (Rect a b c d)) :
    ContinuousOn (fun x => ∫ t in c..d, G ⟨x, t⟩) (Icc a b) := by
  set f : ℝ → ℝ → ℝ := fun x t => G ⟨projIcc a b hab x, projIcc c d hcd t⟩
  have hf : Continuous (Function.uncurry f) := by
    refine hG.comp_continuous ?_ fun p => mk_mem_Rect (Subtype.mem _) (Subtype.mem _)
    have h1 : Continuous fun p : ℝ × ℝ => ((projIcc a b hab p.1 : ℝ)) :=
      continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)
    have h2 : Continuous fun p : ℝ × ℝ => ((projIcc c d hcd p.2 : ℝ)) :=
      continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)
    exact (Complex.equivRealProdCLM.symm.continuous).comp (h1.prodMk h2)
  have hc := continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hf c d
  refine hc.continuousOn.congr fun x hx => ?_
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le hcd] at ht
  simp only [f, projIcc_of_mem _ hx, projIcc_of_mem _ ht]

theorem continuousOn_param_re {G : ℂ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hG : ContinuousOn G (Rect a b c d)) :
    ContinuousOn (fun y => ∫ s in a..b, G ⟨s, y⟩) (Icc c d) := by
  set f : ℝ → ℝ → ℝ := fun y s => G ⟨projIcc a b hab s, projIcc c d hcd y⟩
  have hf : Continuous (Function.uncurry f) := by
    refine hG.comp_continuous ?_ fun p => mk_mem_Rect (Subtype.mem _) (Subtype.mem _)
    have h1 : Continuous fun p : ℝ × ℝ => ((projIcc a b hab p.2 : ℝ)) :=
      continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)
    have h2 : Continuous fun p : ℝ × ℝ => ((projIcc c d hcd p.1 : ℝ)) :=
      continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)
    exact (Complex.equivRealProdCLM.symm.continuous).comp (h1.prodMk h2)
  have hc := continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hf a b
  refine hc.continuousOn.congr fun y hy => ?_
  refine integral_congr fun s hs => ?_
  rw [uIcc_of_le hab] at hs
  simp only [f, projIcc_of_mem _ hy, projIcc_of_mem _ hs]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem bound_along {F : ℝ → W} {G : ℝ → ℝ} {a b x0 x' : ℝ} (hab : a ≤ b)
    (hx0 : x0 ∈ Icc a b) (hx' : x' ∈ Icc a b) (hF : ContinuousOn F (Icc a b))
    (hG : ContinuousOn G (Icc a b)) (hFG : ∀ s ∈ Icc a b, ‖F s‖ ≤ G s) :
    ‖∫ s in x0..x', F s‖ ≤ ∫ s in a..b, G s := by
  have hsub : uIoc x0 x' ⊆ Icc a b :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc hx0 hx')
  refine le_trans norm_integral_le_integral_norm_uIoc ?_
  rw [integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have hG0 : ∀ s ∈ Icc a b, 0 ≤ G s := fun s hs => le_trans (norm_nonneg _) (hFG s hs)
  calc ∫ s in uIoc x0 x', ‖F s‖ ≤ ∫ s in uIoc x0 x', G s :=
        setIntegral_mono_on (hF.norm.integrableOn_compact isCompact_Icc |>.mono_set hsub)
          (hG.integrableOn_compact isCompact_Icc |>.mono_set hsub) measurableSet_uIoc
          fun s hs => hFG s (hsub hs)
    _ ≤ ∫ s in Icc a b, G s :=
        setIntegral_mono_set (hG.integrableOn_compact isCompact_Icc)
          (Filter.eventually_of_mem (self_mem_ae_restrict measurableSet_Icc) hG0)
          (Filter.Eventually.of_forall hsub)

theorem hasDerivAt_horiz (y s : ℝ) : HasDerivAt (fun s : ℝ => (⟨s, y⟩ : ℂ)) 1 s := by
  have h : (fun s : ℝ => (⟨s, y⟩ : ℂ)) = fun s : ℝ => (s : ℂ) + y * I := by
    funext s; apply Complex.ext <;> simp
  rw [h]
  simpa using ((hasDerivAt_id s).ofReal_comp).add_const ((y : ℂ) * I)

theorem hasDerivAt_vert (x t : ℝ) : HasDerivAt (fun t : ℝ => (⟨x, t⟩ : ℂ)) I t := by
  have h : (fun t : ℝ => (⟨x, t⟩ : ℂ)) = fun t : ℝ => (x : ℂ) + t * I := by
    funext t; apply Complex.ext <;> simp
  rw [h]
  simpa using (((hasDerivAt_id t).ofReal_comp).mul_const I).const_add (x : ℂ)

variable [CompleteSpace W]

theorem norm_sub_horiz {u : ℂ → W} {S : Set ℂ} (hS : IsOpen S) (hu : ContDiffOn ℝ 1 u S)
    {a b c d : ℝ} (hab : a ≤ b) (hR : Rect a b c d ⊆ S) {x0 x' y : ℝ} (hx0 : x0 ∈ Icc a b)
    (hx' : x' ∈ Icc a b) (hy : y ∈ Icc c d) :
    ‖u ⟨x', y⟩ - u ⟨x0, y⟩‖ ≤ ∫ s in a..b, ‖fderiv ℝ u ⟨s, y⟩‖ := by
  have hfd := hu.continuousOn_fderiv_of_isOpen hS le_rfl
  have hmaps : ∀ s ∈ Icc a b, (⟨s, y⟩ : ℂ) ∈ S := fun s hs => hR (mk_mem_Rect hs hy)
  have hgc : Continuous fun s : ℝ => (⟨s, y⟩ : ℂ) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_horiz y s).continuousAt
  have hd : ∀ s ∈ uIcc x0 x', HasDerivAt (fun s : ℝ => u ⟨s, y⟩) (fderiv ℝ u ⟨s, y⟩ 1) s := by
    intro s hs
    have hs' : s ∈ Icc a b := uIcc_subset_Icc hx0 hx' hs
    have hdiff : DifferentiableAt ℝ u ⟨s, y⟩ :=
      (hu.differentiableOn one_ne_zero _ (hmaps s hs')).differentiableAt
        (hS.mem_nhds (hmaps s hs'))
    exact hdiff.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_horiz y s)
  have hFc : ContinuousOn (fun s : ℝ => fderiv ℝ u ⟨s, y⟩ 1) (Icc a b) :=
    (hfd.comp hgc.continuousOn hmaps).clm_apply continuousOn_const
  rw [← integral_eq_sub_of_hasDerivAt hd
    ((hFc.mono (uIcc_subset_Icc hx0 hx')).intervalIntegrable)]
  refine bound_along hab hx0 hx' hFc (hfd.comp hgc.continuousOn hmaps).norm fun s _ => ?_
  calc ‖fderiv ℝ u ⟨s, y⟩ 1‖ ≤ ‖fderiv ℝ u ⟨s, y⟩‖ * ‖(1 : ℂ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ u ⟨s, y⟩‖ := by simp

theorem norm_sub_vert {u : ℂ → W} {S : Set ℂ} (hS : IsOpen S) (hu : ContDiffOn ℝ 1 u S)
    {a b c d : ℝ} (hcd : c ≤ d) (hR : Rect a b c d ⊆ S) {x y0 y' : ℝ} (hx : x ∈ Icc a b)
    (hy0 : y0 ∈ Icc c d) (hy' : y' ∈ Icc c d) :
    ‖u ⟨x, y'⟩ - u ⟨x, y0⟩‖ ≤ ∫ t in c..d, ‖fderiv ℝ u ⟨x, t⟩‖ := by
  have hfd := hu.continuousOn_fderiv_of_isOpen hS le_rfl
  have hmaps : ∀ t ∈ Icc c d, (⟨x, t⟩ : ℂ) ∈ S := fun t ht => hR (mk_mem_Rect hx ht)
  have hgc : Continuous fun t : ℝ => (⟨x, t⟩ : ℂ) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_vert x t).continuousAt
  have hd : ∀ t ∈ uIcc y0 y', HasDerivAt (fun t : ℝ => u ⟨x, t⟩) (fderiv ℝ u ⟨x, t⟩ I) t := by
    intro t ht
    have ht' : t ∈ Icc c d := uIcc_subset_Icc hy0 hy' ht
    have hdiff : DifferentiableAt ℝ u ⟨x, t⟩ :=
      (hu.differentiableOn one_ne_zero _ (hmaps t ht')).differentiableAt
        (hS.mem_nhds (hmaps t ht'))
    exact hdiff.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_vert x t)
  have hFc : ContinuousOn (fun t : ℝ => fderiv ℝ u ⟨x, t⟩ I) (Icc c d) :=
    (hfd.comp hgc.continuousOn hmaps).clm_apply continuousOn_const
  rw [← integral_eq_sub_of_hasDerivAt hd
    ((hFc.mono (uIcc_subset_Icc hy0 hy')).intervalIntegrable)]
  refine bound_along hcd hy0 hy' hFc (hfd.comp hgc.continuousOn hmaps).norm fun t _ => ?_
  calc ‖fderiv ℝ u ⟨x, t⟩ I‖ ≤ ‖fderiv ℝ u ⟨x, t⟩‖ * ‖I‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ u ⟨x, t⟩‖ := by simp

/-- **Poincaré inequality on a rectangle** (`L¹` form, with a base point): a `C¹` function on a
neighbourhood of a rectangle is within `((b - a) + (d - c)) ‖Du‖₁` of one of its values. -/
theorem exists_poincare {u : ℂ → W} {S : Set ℂ} (hS : IsOpen S) (hu : ContDiffOn ℝ 1 u S)
    {a b c d : ℝ} (hab : a < b) (hcd : c ≤ d) (hR : Rect a b c d ⊆ S) :
    ∃ p ∈ Rect a b c d, ∫ z in Rect a b c d, ‖u z - u p‖ ≤
      ((b - a) + (d - c)) * ∫ z in Rect a b c d, ‖fderiv ℝ u z‖ := by
  have hfd := hu.continuousOn_fderiv_of_isOpen hS le_rfl
  have hGc : ContinuousOn (fun z => ‖fderiv ℝ u z‖) (Rect a b c d) := (hfd.mono hR).norm
  have hIc := continuousOn_param_im hab.le hcd hGc
  have hHc := continuousOn_param_re hab.le hcd hGc
  obtain ⟨x0, hx0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hIc
  have hc : c ∈ Icc c d := ⟨le_rfl, hcd⟩
  refine ⟨⟨x0, c⟩, mk_mem_Rect hx0 hc, ?_⟩
  set I : ℝ → ℝ := fun x => ∫ t in c..d, ‖fderiv ℝ u ⟨x, t⟩‖ with hI
  set H : ℝ → ℝ := fun y => ∫ s in a..b, ‖fderiv ℝ u ⟨s, y⟩‖ with hH
  have hpt : ∀ z ∈ Rect a b c d, ‖u z - u ⟨x0, c⟩‖ ≤ H z.im + I x0 := by
    intro z hz
    have h1 := norm_sub_horiz hS hu hab.le hR hx0 hz.1 hz.2
    have h2 := norm_sub_vert hS hu hcd hR hx0 hc hz.2
    have hz' : (⟨z.re, z.im⟩ : ℂ) = z := Complex.eta z
    rw [hz'] at h1
    calc ‖u z - u ⟨x0, c⟩‖ = ‖(u z - u ⟨x0, z.im⟩) + (u ⟨x0, z.im⟩ - u ⟨x0, c⟩)‖ := by
          congr 1; abel
      _ ≤ ‖u z - u ⟨x0, z.im⟩‖ + ‖u ⟨x0, z.im⟩ - u ⟨x0, c⟩‖ := norm_add_le _ _
      _ ≤ H z.im + I x0 := add_le_add h1 h2
  have hcont_lhs : ContinuousOn (fun z => ‖u z - u ⟨x0, c⟩‖) (Rect a b c d) :=
    ((hu.continuousOn.mono hR).sub continuousOn_const).norm
  have hcont_rhs : ContinuousOn (fun z : ℂ => H z.im + I x0) (Rect a b c d) :=
    (hHc.comp Complex.continuous_im.continuousOn fun z hz => hz.2).add continuousOn_const
  have step1 : ∫ z in Rect a b c d, ‖u z - u ⟨x0, c⟩‖ ≤ ∫ z in Rect a b c d, (H z.im + I x0) :=
    setIntegral_mono_on (hcont_lhs.integrableOn_compact (isCompact_Rect _ _ _ _))
      (hcont_rhs.integrableOn_compact (isCompact_Rect _ _ _ _)) (measurableSet_Rect _ _ _ _) hpt
  have hHi : IntervalIntegrable H volume c d := (hHc.mono (uIcc_of_le hcd).subset).intervalIntegrable
  have step2 : ∫ z in Rect a b c d, (H z.im + I x0) =
      (b - a) * (∫ y in c..d, H y) + (b - a) * ((d - c) * I x0) := by
    rw [integral_Rect_yx hab.le hcd hcont_rhs]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hHi
      intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have step3 : ∫ y in c..d, H y = ∫ z in Rect a b c d, ‖fderiv ℝ u z‖ :=
    (integral_Rect_yx hab.le hcd hGc).symm
  have step4 : (b - a) * I x0 ≤ ∫ z in Rect a b c d, ‖fderiv ℝ u z‖ := by
    rw [integral_Rect_xy hab.le hcd hGc]
    calc (b - a) * I x0 = ∫ _ in a..b, I x0 := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ ∫ x in a..b, I x :=
          intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
            ((hIc.mono (uIcc_of_le hab.le).subset).intervalIntegrable) fun x hx => hmin hx
  have hdc : 0 ≤ d - c := by linarith
  calc ∫ z in Rect a b c d, ‖u z - u ⟨x0, c⟩‖
      ≤ (b - a) * (∫ y in c..d, H y) + (b - a) * ((d - c) * I x0) := step2 ▸ step1
    _ = (b - a) * (∫ y in c..d, H y) + (d - c) * ((b - a) * I x0) := by ring
    _ ≤ (b - a) * (∫ z in Rect a b c d, ‖fderiv ℝ u z‖) +
        (d - c) * ∫ z in Rect a b c d, ‖fderiv ℝ u z‖ := by
          rw [step3]; gcongr
    _ = ((b - a) + (d - c)) * ∫ z in Rect a b c d, ‖fderiv ℝ u z‖ := by ring


open UpperHalfPlane ModularGroup
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition
open TernaryPeriodPolynomials.Argument.ESFoundations.Height (hasDerivAt_mob)

theorem det_toSpanSingleton_real (w : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ w).restrictScalars ℝ).det = Complex.normSq w := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  have : (((ContinuousLinearMap.toSpanSingleton ℂ w) : ℂ →ₗ[ℂ] ℂ)).det = w := by
    have := ContinuousLinearMap.det_toSpanSingleton (𝕜 := ℂ) w
    simpa only [ContinuousLinearMap.det] using this
  rw [this]
  rfl

theorem mob_injOn (g : SL(2, ℤ)) : Set.InjOn (mob g) U := by
  intro z hz w hw h
  have := congrArg (mob g⁻¹) h
  rwa [← mob_mul, ← mob_mul, inv_mul_cancel, mob_one hz, mob_one hw] at this

/-- Change of variables along a translate: on a compact `R ⊆ U`, the integral of `g ∘ (g₀ ·)`
is controlled by the integral of `g` over the image, with a constant independent of `g`. -/
theorem exists_integral_comp_mob_le (g₀ : SL(2, ℤ)) {R : Set ℂ} (hRc : IsCompact R)
    (hRU : R ⊆ U) : ∃ M : ℝ, 0 ≤ M ∧ ∀ g : ℂ → ℝ, ContinuousOn g U → (∀ z, 0 ≤ g z) →
      ∫ z in R, g (mob g₀ z) ≤ M * ∫ w in mob g₀ '' R, g w := by
  set e : ℂ → ℂ := fun z => ((g₀ 1 0 : ℤ) : ℂ) * z + ((g₀ 1 1 : ℤ) : ℂ)
  have he : Continuous e := by fun_prop
  obtain ⟨K, hK⟩ := hRc.exists_bound_of_continuousOn he.continuousOn
  set M : ℝ := max K 1 ^ 4
  refine ⟨M, by positivity, fun g hg hg0 => ?_⟩
  have hRm : MeasurableSet R := hRc.measurableSet
  set D : ℂ → (ℂ →L[ℝ] ℂ) := fun z =>
    (ContinuousLinearMap.toSpanSingleton ℂ (1 / e z ^ 2)).restrictScalars ℝ
  have hD : ∀ z ∈ R, HasFDerivWithinAt (mob g₀) (D z) R z := fun z hz =>
    ((hasDerivAt_mob g₀ (hRU hz)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume hRm hD
    ((mob_injOn g₀).mono hRU) g
  rw [hcov]
  have hne : ∀ z ∈ R, e z ≠ 0 := fun z hz => denom_ne_zero' g₀ (hRU hz)
  have hdet : ∀ z ∈ R, |(D z).det| = 1 / ‖e z‖ ^ 4 := by
    intro z hz
    rw [det_toSpanSingleton_real, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _),
      norm_div, norm_one, norm_pow]
    have : ‖e z‖ ≠ 0 := norm_ne_zero_iff.mpr (hne z hz)
    field_simp
  have hcomp : ContinuousOn (fun z => g (mob g₀ z)) R :=
    (hg.comp (contDiffOn_mob g₀ (n := 0)).continuousOn (mapsTo_mob g₀)).mono hRU
  have hdetc : ContinuousOn (fun z => 1 / ‖e z‖ ^ 4) R :=
    (continuousOn_const.div (he.continuousOn.norm.pow 4) fun z hz =>
      pow_ne_zero 4 (norm_ne_zero_iff.mpr (hne z hz)))
  calc ∫ z in R, g (mob g₀ z) ≤ ∫ z in R, M * (|(D z).det| • g (mob g₀ z)) := by
        refine setIntegral_mono_on (hcomp.integrableOn_compact hRc) ?_ hRm fun z hz => ?_
        · have hint : ContinuousOn (fun z => M * (1 / ‖e z‖ ^ 4 * g (mob g₀ z))) R :=
            continuousOn_const.mul (hdetc.mul hcomp)
          exact (hint.congr fun z hz => by rw [hdet z hz, smul_eq_mul]).integrableOn_compact hRc
        · rw [hdet z hz, smul_eq_mul]
          have hez : 0 < ‖e z‖ := norm_pos_iff.mpr (hne z hz)
          have hK' : ‖e z‖ ≤ max K 1 := le_trans (hK z hz) (le_max_left _ _)
          have h4 : ‖e z‖ ^ 4 ≤ M := pow_le_pow_left₀ hez.le hK' 4
          have : 1 ≤ M * (1 / ‖e z‖ ^ 4) := by
            rw [mul_one_div, le_div_iff₀ (by positivity), one_mul]
            exact h4
          calc g (mob g₀ z) = 1 * g (mob g₀ z) := (one_mul _).symm
            _ ≤ M * (1 / ‖e z‖ ^ 4) * g (mob g₀ z) := mul_le_mul_of_nonneg_right this (hg0 _)
            _ = M * (1 / ‖e z‖ ^ 4 * g (mob g₀ z)) := by ring
    _ = M * ∫ z in R, |(D z).det| • g (mob g₀ z) := integral_const_mul _ _


theorem integral_Rect_const {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (k : ℝ) :
    ∫ _ in Rect a b c d, k = (b - a) * (d - c) * k := by
  rw [integral_Rect_xy hab hcd continuousOn_const]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- A compact subset of `U` lies in a closed rectangle inside `U`. -/
theorem exists_Rect_of_isCompact {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ a b c d : ℝ, a < b ∧ c < d ∧ K ⊆ Rect a b c d ∧ Rect a b c d ⊆ U := by
  rcases K.eq_empty_or_nonempty with h | hne
  · refine ⟨0, 1, 1, 2, by norm_num, by norm_num, by simp [h], fun z hz => ?_⟩
    show 0 < z.im
    linarith [hz.2.1]
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  have hm : 0 < z₀.im := hKU hz₀
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB z₀ hz₀)
  refine ⟨-B - 1, B + 1, z₀.im / 2, B + 1 + z₀.im, by linarith, by linarith, fun z hz => ?_,
    fun z hz => ?_⟩
  · have h1 : ‖z‖ ≤ B := hB z hz
    have h2 := Complex.abs_re_le_norm z
    have h3 := Complex.abs_im_le_norm z
    have h4 : z₀.im ≤ z.im := hmin hz
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · linarith [neg_abs_le z.re]
    · linarith [le_abs_self z.re]
    · linarith
    · linarith [le_abs_self z.im]
  · show 0 < z.im
    linarith [hz.2.1]

section Heart

variable {Γ : Subgroup SL(2, ℤ)} [FiniteDimensional ℝ W]

/-- The heart of step 4: for finitely many `δ`, a function `u` with the cocycle transformation
law has a coboundary within `C ‖Du‖_{L¹(E)}` of `c`, with `E` and `C` independent of `u`. -/
theorem exists_coboundary_near (ρ : Γ → W →ₗ[ℝ] W) (c : Γ → W) (F : Finset Γ) :
    ∃ E : Set ℂ, ∃ C : ℝ, IsCompact E ∧ E ⊆ U ∧ 0 ≤ C ∧ ∀ u : ℂ → W, ContDiffOn ℝ 1 u U →
      (∀ δ ∈ F, ∀ z ∈ U, u (mob δ z) = ρ δ (u z) + c δ) →
      ∃ w : W, ∀ δ ∈ F, ‖c δ - (ρ δ w - w)‖ ≤ C * ∫ z in E, ‖fderiv ℝ u z‖ := by
  set R : Set ℂ := Rect (-1 / 2) (1 / 2) 1 2 with hR
  have hRc : IsCompact R := isCompact_Rect _ _ _ _
  have hRU : R ⊆ U := fun z hz => by
    show 0 < z.im
    linarith [hz.2.1]
  have hcov : ∀ δ : Γ, ∃ M : ℝ, 0 ≤ M ∧ ∀ g : ℂ → ℝ, ContinuousOn g U → (∀ z, 0 ≤ g z) →
      ∫ z in R, g (mob δ z) ≤ M * ∫ w in mob δ '' R, g w :=
    fun δ => exists_integral_comp_mob_le δ hRc hRU
  choose M hM0 hM using hcov
  set Kset : Set ℂ := R ∪ ⋃ δ ∈ F, mob δ '' R
  have hKc : IsCompact Kset := hRc.union (F.isCompact_biUnion fun δ _ =>
    hRc.image_of_continuousOn ((contDiffOn_mob _ (n := 0)).continuousOn.mono hRU))
  have hKU : Kset ⊆ U := Set.union_subset hRU (Set.iUnion₂_subset fun δ _ => by
    rintro _ ⟨z, -, rfl⟩; exact mob_mem _ z)
  obtain ⟨a, b, c', d, hab, hcd, hKE, hEU⟩ := exists_Rect_of_isCompact hKc hKU
  set E : Set ℂ := Rect a b c' d
  set L : ℝ := (b - a) + (d - c')
  have hL : 0 ≤ L := by simp only [L]; linarith
  set Cρ : Γ → ℝ := fun δ => ‖LinearMap.toContinuousLinearMap (ρ δ)‖
  set C : ℝ := (∑ δ ∈ F, (M δ + Cρ δ)) * L
  have hC0 : 0 ≤ C := mul_nonneg (Finset.sum_nonneg fun δ _ => add_nonneg (hM0 δ) (norm_nonneg _)) hL
  refine ⟨E, C, isCompact_Rect _ _ _ _, hEU, hC0, fun u hu hueq => ?_⟩
  obtain ⟨p, hpE, hpoin⟩ := exists_poincare isOpen_U hu hab hcd.le hEU
  refine ⟨-u p, fun δ hδ => ?_⟩
  set g : ℂ → ℝ := fun z => ‖u z - u p‖
  have hg : ContinuousOn g U := (hu.continuousOn.sub continuousOn_const).norm
  have hg0 : ∀ z, 0 ≤ g z := fun z => norm_nonneg _
  have hgE : IntegrableOn g E := (hg.mono hEU).integrableOn_compact (isCompact_Rect _ _ _ _)
  have hpt : ∀ z ∈ R, ‖c δ - (ρ δ (-u p) - -u p)‖ ≤ g (mob δ z) + Cρ δ * g z := by
    intro z hz
    have heq := hueq δ hδ z (hRU hz)
    have hid : c δ - (ρ δ (-u p) - -u p) = (u (mob δ z) - u p) - ρ δ (u z - u p) := by
      rw [heq, map_neg, map_sub]
      abel
    rw [hid]
    refine le_trans (norm_sub_le _ _) (add_le_add le_rfl ?_)
    exact (LinearMap.toContinuousLinearMap (ρ δ)).le_opNorm (u z - u p)
  have hcompc : ContinuousOn (fun z => g (mob δ z)) R :=
    (hg.comp (contDiffOn_mob _ (n := 0)).continuousOn (mapsTo_mob _)).mono hRU
  have hR1 : ∫ _ in R, ‖c δ - (ρ δ (-u p) - -u p)‖ = ‖c δ - (ρ δ (-u p) - -u p)‖ := by
    rw [hR, integral_Rect_const (by norm_num) (by norm_num)]
    ring
  have hsubE : mob (δ : SL(2, ℤ)) '' R ⊆ E :=
    fun w hw => hKE (Or.inr (Set.mem_biUnion hδ hw))
  have hRE : R ⊆ E := fun z hz => hKE (Or.inl hz)
  have hint1 : ∫ w in mob (δ : SL(2, ℤ)) '' R, g w ≤ ∫ w in E, g w :=
    setIntegral_mono_set hgE (Filter.Eventually.of_forall hg0) (Filter.Eventually.of_forall hsubE)
  have hint2 : ∫ z in R, g z ≤ ∫ z in E, g z :=
    setIntegral_mono_set hgE (Filter.Eventually.of_forall hg0) (Filter.Eventually.of_forall hRE)
  have hle_sum : M δ + Cρ δ ≤ ∑ δ ∈ F, (M δ + Cρ δ) :=
    Finset.single_le_sum (f := fun δ => M δ + Cρ δ)
      (fun δ _ => add_nonneg (hM0 δ) (norm_nonneg _)) hδ
  have hDu0 : 0 ≤ ∫ z in E, ‖fderiv ℝ u z‖ := setIntegral_nonneg (measurableSet_Rect _ _ _ _)
    fun z _ => norm_nonneg _
  calc ‖c δ - (ρ δ (-u p) - -u p)‖ = ∫ _ in R, ‖c δ - (ρ δ (-u p) - -u p)‖ := hR1.symm
    _ ≤ ∫ z in R, (g (mob δ z) + Cρ δ * g z) :=
        setIntegral_mono_on (continuousOn_const.integrableOn_compact hRc)
          ((hcompc.add (continuousOn_const.mul (hg.mono hRU))).integrableOn_compact hRc)
          hRc.measurableSet hpt
    _ = (∫ z in R, g (mob δ z)) + Cρ δ * ∫ z in R, g z := by
        rw [integral_add (hcompc.integrableOn_compact hRc)
          (((hg.mono hRU).integrableOn_compact hRc).const_mul (Cρ δ)),
          MeasureTheory.integral_const_mul]
    _ ≤ M δ * (∫ w in E, g w) + Cρ δ * ∫ z in E, g z := by
        exact add_le_add (le_trans (hM δ g hg hg0) (mul_le_mul_of_nonneg_left hint1 (hM0 δ)))
          (mul_le_mul_of_nonneg_left hint2 (show 0 ≤ Cρ δ from norm_nonneg _))
    _ = (M δ + Cρ δ) * ∫ z in E, g z := by rw [add_mul]
    _ ≤ (M δ + Cρ δ) * (L * ∫ z in E, ‖fderiv ℝ u z‖) :=
        mul_le_mul_of_nonneg_left hpoin (add_nonneg (hM0 δ) (norm_nonneg _))
    _ ≤ (∑ δ ∈ F, (M δ + Cρ δ)) * (L * ∫ z in E, ‖fderiv ℝ u z‖) :=
        mul_le_mul_of_nonneg_right hle_sum (mul_nonneg hL hDu0)
    _ = C * ∫ z in E, ‖fderiv ℝ u z‖ := by ring


private theorem le_amgm (t : ℝ) {η : ℝ} (hη : 0 < η) : t ≤ η / 2 + t ^ 2 / (2 * η) := by
  have h : η / 2 + t ^ 2 / (2 * η) = (η ^ 2 + t ^ 2) / (2 * η) := by field_simp
  rw [h, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (t - η)]

/-- `L²` convergence to zero on a compact set gives `L¹` convergence to zero. -/
theorem tendsto_integral_of_tendsto_integral_sq {E : Set ℂ} (hE : IsCompact E)
    {f : ℕ → ℂ → ℝ} (hf : ∀ j, ContinuousOn (f j) E) (hf0 : ∀ j z, 0 ≤ f j z)
    (h : Filter.Tendsto (fun j => ∫ z in E, f j z ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun j => ∫ z in E, f j z) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  set V : ℝ := volume.real E
  have hV : 0 ≤ V := measureReal_nonneg
  set η : ℝ := ε / (V + 1)
  have hη : 0 < η := by positivity
  obtain ⟨N, hN⟩ := h (η * ε) (by positivity)
  refine ⟨N, fun j hj => ?_⟩
  have hsq := hN j hj
  rw [Real.dist_eq, sub_zero] at hsq ⊢
  have hint : IntegrableOn (f j) E := (hf j).integrableOn_compact hE
  have hint2 : IntegrableOn (fun z => f j z ^ 2) E := ((hf j).pow 2).integrableOn_compact hE
  have hnn : 0 ≤ ∫ z in E, f j z := setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall fun z => hf0 j z) |> fun h => h
  have hsq0 : 0 ≤ ∫ z in E, f j z ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  rw [abs_of_nonneg hsq0] at hsq
  rw [abs_of_nonneg hnn]
  have hconst : IntegrableOn (fun _ : ℂ => η / 2) E :=
    integrableOn_const hE.measure_lt_top.ne
  have hle : ∫ z in E, f j z ≤ ∫ z in E, (η / 2 + f j z ^ 2 / (2 * η)) :=
    setIntegral_mono_on hint (hconst.add (hint2.div_const _)) hE.measurableSet
      fun z _ => le_amgm (f j z) hη
  rw [integral_add hconst (hint2.div_const _), setIntegral_const, MeasureTheory.integral_div,
    smul_eq_mul] at hle
  have h1 : V * (η / 2) < ε / 2 := by
    have : V * (ε / (V + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    simp only [η]
    nlinarith
  have h2 : (∫ z in E, f j z ^ 2) / (2 * η) < ε / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Step 4 (period continuity).** If `Ψ` has the cocycle transformation law for `c` and
`Γ`-equivariant `φ_j` have differentials converging to `dΨ` in `L²` on compact subsets of `U`,
then `c` is a coboundary. -/
theorem isCoboundary_of_tendsto {Γ : Subgroup SL(2, ℤ)}
    (ρ : Γ → W →ₗ[ℝ] W) (c : Γ → W) {Ψ : ℂ → W} (hΨ : ContDiffOn ℝ 1 Ψ U)
    (hΨeq : ∀ δ : Γ, ∀ z ∈ U, Ψ (mob δ z) = ρ δ (Ψ z) + c δ) {φ : ℕ → ℂ → W}
    (hφ : ∀ j, ContDiffOn ℝ 1 (φ j) U)
    (hφeq : ∀ j, ∀ δ : Γ, ∀ z ∈ U, φ j (mob δ z) = ρ δ (φ j z))
    (hconv : ∀ K : Set ℂ, IsCompact K → K ⊆ U → Filter.Tendsto
      (fun j => ∫ z in K, ‖fderiv ℝ (φ j) z - fderiv ℝ Ψ z‖ ^ 2) Filter.atTop (nhds 0)) :
    ∃ w : W, ∀ δ : Γ, c δ = ρ δ w - w := by
  set Lmap : W →ₗ[ℝ] (Γ → W) := LinearMap.pi fun δ => ρ δ - LinearMap.id with hLmap
  have hLapply : ∀ w δ, Lmap w δ = ρ δ w - w := fun w δ => by simp [Lmap]
  have hclosed : IsClosed (LinearMap.range Lmap : Set (Γ → W)) :=
    Submodule.closed_of_finiteDimensional _
  suffices hc : c ∈ closure (LinearMap.range Lmap : Set (Γ → W)) by
    rw [hclosed.closure_eq] at hc
    obtain ⟨w, hw⟩ := hc
    exact ⟨w, fun δ => by rw [← hw, hLapply]⟩
  rw [mem_closure_iff]
  intro O hO hcO
  obtain ⟨I, u, hu, hIO⟩ := isOpen_pi_iff.mp hO c hcO
  have hrad : ∀ δ ∈ I, ∃ ε > 0, Metric.ball (c δ) ε ⊆ u δ := fun δ hδ =>
    Metric.isOpen_iff.mp (hu δ hδ).1 (c δ) (hu δ hδ).2
  choose! ε hε hεsub using hrad
  obtain ⟨ε₀, hε₀, hε₀le⟩ : ∃ ε₀ > 0, ∀ δ ∈ I, ε₀ ≤ ε δ := by
    rcases I.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨I.inf' h ε, (Finset.lt_inf'_iff h).mpr fun δ hδ => hε δ hδ,
        fun δ hδ => Finset.inf'_le _ hδ⟩
  obtain ⟨E, C, hEc, hEU, hC0, hheart⟩ := exists_coboundary_near ρ c I
  have hcontD : ∀ j, ContinuousOn (fun z => ‖fderiv ℝ (φ j) z - fderiv ℝ Ψ z‖) E := fun j =>
    ((((hφ j).continuousOn_fderiv_of_isOpen isOpen_U le_rfl).sub
      (hΨ.continuousOn_fderiv_of_isOpen isOpen_U le_rfl)).norm).mono hEU
  have hL1 := tendsto_integral_of_tendsto_integral_sq hEc hcontD (fun _ _ => norm_nonneg _)
    (hconv E hEc hEU)
  obtain ⟨j, hj⟩ : ∃ j, C * ∫ z in E, ‖fderiv ℝ (φ j) z - fderiv ℝ Ψ z‖ < ε₀ := by
    have h := hL1.const_mul C
    rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds hε₀)).exists
  set v : ℂ → W := fun z => Ψ z - φ j z with hv
  have hvd : ContDiffOn ℝ 1 v U := hΨ.sub (hφ j)
  have hveq : ∀ δ ∈ I, ∀ z ∈ U, v (mob δ z) = ρ δ (v z) + c δ := by
    intro δ _ z hz
    simp only [v, hΨeq δ z hz, hφeq j δ z hz, map_sub]
    abel
  have hDv : ∀ z ∈ E, ‖fderiv ℝ v z‖ = ‖fderiv ℝ (φ j) z - fderiv ℝ Ψ z‖ := by
    intro z hz
    have hzU := hEU hz
    have h1 : DifferentiableAt ℝ Ψ z :=
      (hΨ.differentiableOn one_ne_zero z hzU).differentiableAt (isOpen_U.mem_nhds hzU)
    have h2 : DifferentiableAt ℝ (φ j) z :=
      ((hφ j).differentiableOn one_ne_zero z hzU).differentiableAt (isOpen_U.mem_nhds hzU)
    rw [hv, fderiv_fun_sub h1 h2, norm_sub_rev]
  obtain ⟨w, hw⟩ := hheart v hvd hveq
  refine ⟨Lmap w, hIO fun δ hδ => ?_, ⟨w, rfl⟩⟩
  have hδ' : δ ∈ I := Finset.mem_coe.mp hδ
  apply hεsub δ hδ'
  rw [Metric.mem_ball, dist_eq_norm, hLapply, norm_sub_rev]
  calc ‖c δ - (ρ δ w - w)‖ ≤ C * ∫ z in E, ‖fderiv ℝ v z‖ := hw δ hδ'
    _ = C * ∫ z in E, ‖fderiv ℝ (φ j) z - fderiv ℝ Ψ z‖ := by
        rw [setIntegral_congr_fun hEc.measurableSet hDv]
    _ < ε₀ := hj
    _ ≤ ε δ := hε₀le δ hδ'

end Heart

end TernaryPeriodPolynomials.Argument.ESFoundations.PeriodContinuity
