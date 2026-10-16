module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.Slash
public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.Core

@[expose] public section


/-!
# Exponential decay of the slashes of a cusp form of `Γ(N)`

`decays_cuspForm`: `f ∣[k] σ` decays exponentially at `i∞` for every `σ ∈ SL₂(ℤ)` (Mathlib `exp_decay_atImInfty` for `CuspForm.translate`).

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup Filter Asymptotics
open scoped MatrixGroups Pointwise ConjAct
noncomputable section
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.EisensteinClass

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

omit [NeZero N] in
theorem fs_eq_cuspSlash (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    fs n (cuspH (leviGroup N) n f) σ z = cuspSlash N n σ f (ofComplex z) := by
  rw [← slashTwisted_cuspSlash N n σ f hz]
  have hdet : ((mapGL ℝ σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; simp
  unfold slashTwisted fs cuspH
  rw [hdet]
  simp only [Complex.ofReal_one, one_pow, one_mul, zpow_neg, zpow_natCast]
  rw [mul_comm]
  rfl

theorem decays_cuspForm : Decays n (cuspH (leviGroup N) n f) := by
  intro σ
  obtain ⟨c, hc, hO⟩ : ∃ c > 0, ⇑(cuspSlash N n σ f) =O[atImInfty] fun τ : ℍ => Real.exp (-c * τ.im) :=
    CuspFormClass.exp_decay_atImInfty' _
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).1 hC
  refine ⟨C, c, max A 1, hc, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz => ?_⟩
  have hz1 : 0 < z.im := lt_of_lt_of_le one_pos ((le_max_right A 1).trans hz)
  rw [fs_eq_cuspSlash N n f σ hz1, UpperHalfPlane.ofComplex_apply_of_im_pos hz1]
  have := hA ⟨z, hz1⟩ ((le_max_left A 1).trans hz)
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, Real.abs_exp] at this
  exact this

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
