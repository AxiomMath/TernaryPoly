module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Representative
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

@[expose] public section


/-!
# The Poincaré primitive of the harmonic form and its cocycle

A smooth closed form `formOf a b` on the (convex) upper half plane has a smooth primitive `Φ₀`
(`exists_primitive`, from Mathlib's Poincaré lemma).  If the form is equivariant, `Φ₀` transforms
by a cocycle: `Φ₀ (γ z) = ρ(γ) Φ₀ z + c₀ γ` (`exists_cocycle`).

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

theorem convex_U : Convex ℝ U := convex_halfSpace_im_gt 0

theorem fderiv_formOf_apply {a b : ℂ → Wd d} {z : ℂ} (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z) (x y : ℂ) :
    fderiv ℝ (formOf a b) z x y = y.re • fderiv ℝ a z x + y.im • fderiv ℝ b z x := by
  have h1 := (ContinuousLinearMap.smulRightL ℝ ℂ (Wd d) Complex.reCLM).hasFDerivAt.comp z
    ha.hasFDerivAt
  have h2 := (ContinuousLinearMap.smulRightL ℝ ℂ (Wd d) Complex.imCLM).hasFDerivAt.comp z
    hb.hasFDerivAt
  have h := h1.add h2
  have e : formOf a b = fun w =>
      (ContinuousLinearMap.smulRightL ℝ ℂ (Wd d) Complex.reCLM ∘ a) w +
        (ContinuousLinearMap.smulRightL ℝ ℂ (Wd d) Complex.imCLM ∘ b) w := rfl
  have h' : HasFDerivAt (fun w => (ContinuousLinearMap.smulRightL ℝ ℂ (Wd d) Complex.reCLM ∘ a) w +
        (ContinuousLinearMap.smulRightL ℝ ℂ (Wd d) Complex.imCLM ∘ b) w) _ z := h
  rw [e, h'.fderiv]
  simp

theorem formOf_symm {a b : ℂ → Wd d} {z : ℂ} (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z) (hcl : fderiv ℝ b z (dir 0) = fderiv ℝ a z (dir 1)) (x y : ℂ) :
    fderiv ℝ (formOf a b) z x y = fderiv ℝ (formOf a b) z y x := by
  rw [fderiv_formOf_apply ha hb, fderiv_formOf_apply ha hb]
  have hx : ∀ w : ℂ, fderiv ℝ a z w = w.re • fderiv ℝ a z 1 + w.im • fderiv ℝ a z Complex.I := by
    intro w
    conv_lhs => rw [show w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I from by
      apply Complex.ext <;> simp]
    rw [(fderiv ℝ a z).map_add, (fderiv ℝ a z).map_smul, (fderiv ℝ a z).map_smul]
  have hy : ∀ w : ℂ, fderiv ℝ b z w = w.re • fderiv ℝ b z 1 + w.im • fderiv ℝ b z Complex.I := by
    intro w
    conv_lhs => rw [show w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I from by
      apply Complex.ext <;> simp]
    rw [(fderiv ℝ b z).map_add, (fderiv ℝ b z).map_smul, (fderiv ℝ b z).map_smul]
  have hcl' : fderiv ℝ b z 1 = fderiv ℝ a z Complex.I := by simpa [dir] using hcl
  rw [hx x, hx y, hy x, hy y, hcl']
  module

theorem exists_primitive {a b : ℂ → Wd d} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hcl : ∀ z ∈ U, fderiv ℝ b z (dir 0) = fderiv ℝ a z (dir 1)) :
    ∃ Φ₀ : ℂ → Wd d, ContDiffOn ℝ ∞ Φ₀ U ∧ ∀ z ∈ U, HasFDerivAt Φ₀ (formOf a b z) z := by
  have hf := contDiffOn_formOf ha hb
  obtain ⟨Φ₀, hΦ⟩ := convex_U.exists_forall_hasFDerivAt_of_fderiv_symmetric isOpen_U
    (hf.differentiableOn (by simp)) (fun z hz x y => by
      have hda : DifferentiableAt ℝ a z :=
        (ha.differentiableOn (by simp)).differentiableAt (isOpen_U.mem_nhds hz)
      have hdb : DifferentiableAt ℝ b z :=
        (hb.differentiableOn (by simp)).differentiableAt (isOpen_U.mem_nhds hz)
      exact formOf_symm hda hdb (hcl z hz) x y)
  refine ⟨Φ₀, ?_, hΦ⟩
  rw [contDiffOn_infty_iff_fderiv_of_isOpen isOpen_U]
  exact ⟨fun z hz => (hΦ z hz).differentiableAt.differentiableWithinAt,
    hf.congr fun z hz => (hΦ z hz).fderiv⟩

theorem HodgeDatum.exists_cocycle (D : HodgeDatum Γ d) {Φ₀ : ℂ → Wd d} {L : Form d}
    (hΦ : ∀ z ∈ U, HasFDerivAt Φ₀ (L z) z) (hE : D.Eqv L) :
    ∃ c₀ : Γ → Wd d, ∀ δ : Γ, ∀ z ∈ U, Φ₀ (mob (δ : SL(2, ℤ)) z) = D.ρ δ (Φ₀ z) + c₀ δ := by
  have hdiff : DifferentiableOn ℝ Φ₀ U := fun z hz => (hΦ z hz).differentiableAt.differentiableWithinAt
  have hper : ∀ δ : Γ, ∃ k : Wd d, ∀ z ∈ U, D.ρR δ⁻¹ (Φ₀ (mob (δ : SL(2, ℤ)) z)) = Φ₀ z + k := by
    intro δ
    set ψ : ℂ → Wd d := fun z => D.ρR δ⁻¹ (Φ₀ (mob (δ : SL(2, ℤ)) z)) with hψ
    have hψd : DifferentiableOn ℝ ψ U := by
      intro w hw
      have hm : DifferentiableAt ℝ (mob (δ : SL(2, ℤ))) w :=
        ((Height.hasDerivAt_mob _ hw).differentiableAt).restrictScalars ℝ
      have hφ' : DifferentiableAt ℝ Φ₀ (mob (δ : SL(2, ℤ)) w) :=
        (hΦ _ (Partition.mob_mem _ _)).differentiableAt
      exact (((D.ρR δ⁻¹).differentiableAt).comp w (hφ'.comp w hm)).differentiableWithinAt
    have hψ' : U.EqOn (fderiv ℝ ψ) (fderiv ℝ Φ₀) := by
      intro x hx
      have h1 := D.slash_fderiv δ hdiff hx
      have h2 : D.slash δ (fun z => fderiv ℝ Φ₀ z) x = D.slash δ L x := by
        unfold HodgeDatum.slash
        beta_reduce
        rw [(hΦ _ (Partition.mob_mem _ _)).fderiv]
      rw [← h1, h2, hE δ x hx, (hΦ x hx).fderiv]
    obtain ⟨k, hk⟩ := isOpen_U.exists_eq_add_of_fderiv_eq convex_U.isPreconnected hψd hdiff hψ'
    exact ⟨k, fun z hz => hk hz⟩
  choose k hk using hper
  refine ⟨fun δ => D.ρ δ (k δ), fun δ z hz => ?_⟩
  have h1 := hk δ z hz
  have h2 : Φ₀ (mob (δ : SL(2, ℤ)) z) = D.ρR δ (D.ρR δ⁻¹ (Φ₀ (mob (δ : SL(2, ℤ)) z))) := by
    have := congrArg (fun T : Wd d →L[ℂ] Wd d => T (Φ₀ (mob (δ : SL(2, ℤ)) z)))
      (D.ρ.map_mul δ δ⁻¹)
    simp only [mul_inv_cancel, map_one] at this
    exact this
  rw [h2, h1, map_add]
  rfl

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
