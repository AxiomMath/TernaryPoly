module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.GreenAtil

@[expose] public section


/-!
# The Petersson density of the coset sum

`∂_z Ã = (2i)^{n+1} · pr`, where `pr ≥ |f|² y^{n+1}` is the sum over cosets of the Petersson densities of the translates.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane MeasureTheory Set intervalIntegral
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

theorem mob_im (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    (mob (toR g) z).im = z.im / Complex.normSq (dnm (toR g) z) := by
  have h := mob_eq_smul (toR g) (toR_pos g) ⟨z, hz⟩
  have h2 := UpperHalfPlane.im_smul_eq_div_normSq (toR g) (⟨z, hz⟩ : ℍ)
  have e : ((toR g).det.val) = 1 := by rw [toR_det]; rfl
  rw [e] at h2
  have h3 : (mob (toR g) z).im = ((toR g) • (⟨z, hz⟩ : ℍ)).im := by
    rw [show mob (toR g) z = _ from h]
    rfl
  rw [h3, h2]
  simp [UpperHalfPlane.denom, dnm]

/-- The real density: the sum over the cosets of the Petersson densities of the translates. -/
def pr (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (n : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  ∑ q : SL(2, ℤ) ⧸ Γ, (‖dnm (toR (gq Γ q)) z‖ ^ 4)⁻¹ *
    (‖f (mob (toR (gq Γ q)) z)‖ ^ 2 * (mob (toR (gq Γ q)) z).im ^ (n + 1))

theorem DAtil_eq (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (n : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    DAtil Γ n f z = (2 * Complex.I) ^ (n + 1) * ((pr Γ n f z : ℝ) : ℂ) := by
  unfold DAtil pr
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  set J := dnm (toR (gq Γ q)) z
  set ζ := mob (toR (gq Γ q)) z
  have h1 : ζ - conj ζ = 2 * Complex.I * (ζ.im : ℂ) := by
    rw [Complex.sub_conj]; push_cast; ring
  have h2 : f ζ * conj (f ζ) = ((‖f ζ‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have h3 : (J ^ 2)⁻¹ * (conj (J ^ 2))⁻¹ = (((‖J‖ : ℝ) : ℂ) ^ 4)⁻¹ := by
    rw [← mul_inv]
    congr 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow]; push_cast; ring
  rw [h1, h2, h3, mul_pow]
  ring


section Positivity

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {n : ℕ} {f : ℂ → ℂ}

theorem pr_nonneg {z : ℂ} (hz : 0 < z.im) : 0 ≤ pr Γ n f z := by
  unfold pr
  refine Finset.sum_nonneg (fun q _ => ?_)
  have := mob_mem_Uset (gq Γ q) hz
  positivity

theorem continuousOn_pr (hf : DifferentiableOn ℂ f Uset) : ContinuousOn (pr Γ n f) Uset := by
  unfold pr
  refine continuousOn_finsetSum _ (fun q _ => ?_)
  have hd : Continuous (fun z : ℂ => dnm (toR (gq Γ q)) z) := by unfold dnm; fun_prop
  have h1 : ContinuousOn (fun z : ℂ => (‖dnm (toR (gq Γ q)) z‖ ^ 4)⁻¹) Uset := by
    refine ContinuousOn.inv₀ ((hd.norm.pow 4).continuousOn) (fun z hz => ?_)
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (dnm_ne_zero _ hz))
  have hm : ContinuousOn (mob (toR (gq Γ q))) Uset := (differentiableOn_mob _).continuousOn
  have h2 : ContinuousOn (fun z : ℂ => f (mob (toR (gq Γ q)) z)) Uset :=
    hf.continuousOn.comp hm (fun z hz => mob_mem_Uset _ hz)
  have h3 : ContinuousOn (fun z : ℂ => (mob (toR (gq Γ q)) z).im) Uset :=
    Complex.continuous_im.comp_continuousOn hm
  exact h1.mul ((h2.norm.pow 2).mul (h3.pow _))

omit [Γ.FiniteIndex] in
theorem gq_one_mem : gq Γ (QuotientGroup.mk 1) ∈ Γ := by
  unfold gq
  have hy : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Γ)) : SL(2, ℤ) ⧸ Γ) =
      QuotientGroup.mk 1 := QuotientGroup.out_eq' _
  have := QuotientGroup.eq.mp hy
  simpa using this

theorem pr_ge {g : ℂ → ℂ} {Gf Gg : ℕ → ℂ → ℂ} {v : MvPolynomial (Fin 2) ℂ}
    (S : Setup Γ n f g Gf Gg v) {z : ℂ} (hz : 0 < z.im) :
    ‖f z‖ ^ 2 * z.im ^ (n + 1) ≤ pr Γ n f z := by
  have hnn : ∀ q ∈ (Finset.univ : Finset (SL(2, ℤ) ⧸ Γ)), 0 ≤ (‖dnm (toR (gq Γ q)) z‖ ^ 4)⁻¹ *
      (‖f (mob (toR (gq Γ q)) z)‖ ^ 2 * (mob (toR (gq Γ q)) z).im ^ (n + 1)) := by
    intro q _
    have := mob_mem_Uset (gq Γ q) hz
    positivity
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum hnn (Finset.mem_univ (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Γ)))
  set γ := gq Γ (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Γ) with hγ
  have hmem : γ ∈ Γ := gq_one_mem
  have hJ : dnm (toR γ) z ≠ 0 := dnm_ne_zero _ hz
  have hN : 0 < ‖dnm (toR γ) z‖ := norm_pos_iff.mpr hJ
  have hN' : ‖dnm (toR γ) z‖ ≠ 0 := hN.ne'
  rw [S.mf γ hmem z hz, mob_im γ hz, Complex.normSq_eq_norm_sq, norm_mul, norm_pow, div_pow, mul_pow,
    ← pow_mul, ← pow_mul]
  have e : ‖dnm (toR γ) z‖ ^ ((n + 3) * 2) = ‖dnm (toR γ) z‖ ^ 4 * ‖dnm (toR γ) z‖ ^ (2 * (n + 1)) := by
    rw [← pow_add]; congr 1; ring
  rw [e]
  field_simp

end Positivity

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
