module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.StokesHA

@[expose] public section


/-!
# Composition of holomorphic-antiholomorphic families with Möbius maps

Translating a family `(u, w)` by `σ ∈ SL₂(ℤ)` and summing over a finite set of translates.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

section Comp

variable {ι : Type} [Fintype ι]

theorem toR_pos (g : SL(2, ℤ)) : 0 < (toR g).det.val := by rw [toR_det]; simp

theorem mob_mem_Uset (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : 0 < (mob (toR g) z).im :=
  mob_im_pos _ (toR_pos g) hz

theorem differentiableOn_mob (g : SL(2, ℤ)) : DifferentiableOn ℂ (mob (toR g)) Uset := fun _ hz =>
  (mob_hasDerivAt (toR g) (toR_det g) hz).differentiableAt.differentiableWithinAt

theorem differentiableOn_dnm_sq_inv (g : SL(2, ℤ)) : DifferentiableOn ℂ (fun z => ((dnm (toR g) z) ^ 2)⁻¹) Uset := by
  have h : Differentiable ℂ (fun z : ℂ => dnm (toR g) z) := by
    unfold dnm
    fun_prop
  exact ((h.pow 2).differentiableOn).inv (fun z hz => pow_ne_zero _ (dnm_ne_zero _ hz))

/-- Composition of a holomorphic family with a Möbius map. -/
def cU (g : SL(2, ℤ)) (u : ι → ℂ → ℂ) : ι → ℂ → ℂ := fun i z => u i (mob (toR g) z)

/-- Composition with a Möbius map, times `(cz+d)⁻²`. -/
def cW (g : SL(2, ℤ)) (w : ι → ℂ → ℂ) : ι → ℂ → ℂ := fun i z => w i (mob (toR g) z) * ((dnm (toR g) z) ^ 2)⁻¹

omit [Fintype ι] in
theorem cU_diff (g : SL(2, ℤ)) {u : ι → ℂ → ℂ} (hu : ∀ i, DifferentiableOn ℂ (u i) Uset) (i : ι) :
    DifferentiableOn ℂ (cU g u i) Uset :=
  (hu i).comp (differentiableOn_mob g) (fun _ hz => mob_mem_Uset g hz)

omit [Fintype ι] in
theorem cW_diff (g : SL(2, ℤ)) {w : ι → ℂ → ℂ} (hw : ∀ i, DifferentiableOn ℂ (w i) Uset) (i : ι) :
    DifferentiableOn ℂ (cW g w i) Uset :=
  ((hw i).comp (differentiableOn_mob g) (fun _ hz => mob_mem_Uset g hz)).mul (differentiableOn_dnm_sq_inv g)

theorem holAnti_cUW (g : SL(2, ℤ)) (u w : ι → ℂ → ℂ) (z : ℂ) :
    holAnti (cU g u) (cW g w) z = (conj ((dnm (toR g) z) ^ 2))⁻¹ * holAnti u w (mob (toR g) z) := by
  unfold holAnti cU cW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, map_inv₀]
  ring

omit [Fintype ι] in
theorem deriv_cU (g : SL(2, ℤ)) {u : ι → ℂ → ℂ} (hu : ∀ i, DifferentiableOn ℂ (u i) Uset) (i : ι) {z : ℂ}
    (hz : 0 < z.im) :
    deriv (cU g u i) z = deriv (u i) (mob (toR g) z) * ((dnm (toR g) z) ^ 2)⁻¹ := by
  have h1 := hasDerivAt_of_diffOn (hu i) (mob_mem_Uset g hz)
  have h2 := mob_hasDerivAt (toR g) (toR_det g) hz
  have := (h1.comp z h2).deriv
  unfold cU
  change deriv (u i ∘ mob (toR g)) z = _
  rw [this, one_div]

theorem holAntiD_cUW (g : SL(2, ℤ)) {u : ι → ℂ → ℂ} (w : ι → ℂ → ℂ) (hu : ∀ i, DifferentiableOn ℂ (u i) Uset)
    {z : ℂ} (hz : 0 < z.im) :
    holAntiD (cW g w) (fun i => deriv (cU g u i)) z =
      ((dnm (toR g) z) ^ 2)⁻¹ * (conj ((dnm (toR g) z) ^ 2))⁻¹ *
        holAntiD w (fun i => deriv (u i)) (mob (toR g) z) := by
  unfold holAntiD cW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show deriv (cU g u i) z * _ = _
  rw [deriv_cU g hu i hz, map_mul, map_inv₀]
  ring

end Comp

section Sum

variable {ι : Type} [Fintype ι] {Q : Type}

/-- The family over `Q × ι` of the `g_q`-translates. -/
def uQ (gq : Q → SL(2, ℤ)) (u : ι → ℂ → ℂ) : Q × ι → ℂ → ℂ := fun p => cU (gq p.1) u p.2

def wQ (gq : Q → SL(2, ℤ)) (w : ι → ℂ → ℂ) : Q × ι → ℂ → ℂ := fun p => cW (gq p.1) w p.2

theorem holAnti_Q [Fintype Q] (gq : Q → SL(2, ℤ)) (u w : ι → ℂ → ℂ) (z : ℂ) :
    holAnti (uQ gq u) (wQ gq w) z = ∑ q, (conj ((dnm (toR (gq q)) z) ^ 2))⁻¹ * holAnti u w (mob (toR (gq q)) z) := by
  unfold holAnti uQ wQ
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have := holAnti_cUW (gq q) u w z
  unfold holAnti cU cW at this
  exact this

theorem holAntiD_Q [Fintype Q] (gq : Q → SL(2, ℤ)) {u : ι → ℂ → ℂ} (w : ι → ℂ → ℂ) (hu : ∀ i, DifferentiableOn ℂ (u i) Uset)
    {z : ℂ} (hz : 0 < z.im) :
    holAntiD (wQ gq w) (fun p => deriv (uQ gq u p)) z =
      ∑ q, ((dnm (toR (gq q)) z) ^ 2)⁻¹ * (conj ((dnm (toR (gq q)) z) ^ 2))⁻¹ *
        holAntiD w (fun i => deriv (u i)) (mob (toR (gq q)) z) := by
  unfold holAntiD uQ wQ
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have := holAntiD_cUW (gq q) w hu hz
  unfold holAntiD cW at this
  exact this

omit [Fintype ι] in
theorem uQ_diff (gq : Q → SL(2, ℤ)) {u : ι → ℂ → ℂ} (hu : ∀ i, DifferentiableOn ℂ (u i) Uset) (p : Q × ι) :
    DifferentiableOn ℂ (uQ gq u p) Uset := cU_diff _ hu _

omit [Fintype ι] in
theorem wQ_diff (gq : Q → SL(2, ℤ)) {w : ι → ℂ → ℂ} (hw : ∀ i, DifferentiableOn ℂ (w i) Uset) (p : Q × ι) :
    DifferentiableOn ℂ (wQ gq w p) Uset := cW_diff _ hw _

end Sum

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
