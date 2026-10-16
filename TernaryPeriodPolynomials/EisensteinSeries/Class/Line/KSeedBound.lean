module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBruhat
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityAssembly
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.AntiHolomorphic

@[expose] public section


/-!
# Decay and holomorphy of the orbit seeds

Paper: Appendix C.5.

The bridge `Tinf_eq_lineSeed` needs, for the seed `h`, holomorphy on the upper half plane and the decay
`‖h z‖² Im(z)^{n+3} ≤ M`. For `h = hfun f` this is the cusp form bound (`hfun_bound`); for the orbit seeds
`h|A` (`r₀ > 0`) and `hStar (h|A⁺)` (`r₀ < 0`) it is preserved by `slashTwisted_decay` and the reflection
`z ↦ -conj z`, since the top blocks have positive determinant (`topBlock_det_pos`).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial ComplexConjugate
open scoped MatrixGroups Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.FormClassK
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
  (slashTwisted_decay slashTwisted_differentiableOn)

section Bounds

theorem topBlock_det_pos {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : P.det = 1) (h0 : P 2 0 = 0) (h1 : P 2 1 = 0)
    (hc : 0 < P 2 2) : 0 < (topBlock P).det := by
  have hd : P.det = (topBlock P).det * P 2 2 := by
    simp [topBlock, Matrix.det_fin_three, Matrix.det_fin_two, h0, h1]; ring
  rw [hP] at hd
  by_contra hneg
  push Not at hneg
  nlinarith

theorem hStar_decay (H : ℂ → ℂ) (M : ℝ) (k : ℕ) (hM : ∀ z : ℂ, 0 < z.im → ‖H z‖ ^ 2 * z.im ^ k ≤ M)
    (z : ℂ) (hz : 0 < z.im) : ‖hStar H z‖ ^ 2 * z.im ^ k ≤ M := by
  have := hM (-conj z) (by simpa using hz)
  simpa [hStar] using this

theorem hfun_decay {Λ : Subgroup (GL (Fin 2) ℝ)} [Λ.HasDetOne] [Λ.IsArithmetic] (n : ℕ)
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖hfun f z‖ ^ 2 * z.im ^ (n + 3) ≤ M := by
  obtain ⟨Ch, hCh⟩ := hfun_bound (Λ := Λ) n f
  refine ⟨Ch ^ 2, fun z hz => ?_⟩
  have h1 := hCh z hz
  have h2 : 0 ≤ ‖hfun f z‖ * z.im ^ (((n : ℝ) + 3) / 2) := by positivity
  have h3 : (‖hfun f z‖ * z.im ^ (((n : ℝ) + 3) / 2)) ^ 2 ≤ Ch ^ 2 := pow_le_pow_left₀ h2 h1 2
  have h4 : (z.im ^ (((n : ℝ) + 3) / 2)) ^ 2 = z.im ^ (n + 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    have : (((n : ℝ) + 3) / 2 * ((2 : ℕ) : ℝ)) = ((n + 3 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
  rw [mul_pow, h4] at h3
  exact h3

end Bounds


section Orbit

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- **Holomorphy and decay of the orbit seeds** (for orbits with `r₀ ≠ 0`): exactly the hypotheses of the
bridge `Tinf_eq_lineSeed`. -/
theorem orbitSeed_data (c : Ck N k) (h0 : orbitMat N k c 2 0 ≠ 0) :
    DifferentiableOn ℂ (orbitSeed N k n f c) {z : ℂ | 0 < z.im} ∧
    ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖orbitSeed N k n f c z‖ ^ 2 * z.im ^ (n + 3) ≤ M := by
  have hdet := orbitMat_det N k c
  obtain ⟨M0, hM0⟩ := hfun_decay n f
  have hh : DifferentiableOn ℂ (hfun f) {z : ℂ | 0 < z.im} := hfun_differentiableOn (leviGroup N) n f
  obtain ⟨r0, r1, r2⟩ := bruhatP_row (orbitMat N k c) h0
  have hPd : (bruhatP (orbitMat N k c)).det = 1 := by rw [det_bruhatP, hdet]
  unfold orbitSeed
  split_ifs with hpos
  · have hc : 0 < (topBlock (bruhatP (orbitMat N k c))).det := topBlock_det_pos hPd r0 r1 (by rw [r2]; exact hpos)
    exact ⟨slashTwisted_differentiableOn (n + 3) _ hc _ hh,
      _, slashTwisted_decay (n + 3) _ hc _ M0 hM0⟩
  · have hneg : orbitMat N k c 2 0 < 0 := lt_of_le_of_ne (not_lt.1 hpos) h0
    set R := realMat rPrime
    have hP'd : (bruhatP (orbitMat N k c) * R).det = 1 := by
      rw [Matrix.det_mul, hPd, det_realMat]; norm_num
    have h20 : (bruhatP (orbitMat N k c) * R) 2 0 = 0 := by
      simp [R, realMat_rPrime, Matrix.mul_apply, Fin.sum_univ_three, r0]
    have h21 : (bruhatP (orbitMat N k c) * R) 2 1 = 0 := by
      simp [R, realMat_rPrime, Matrix.mul_apply, Fin.sum_univ_three, r1]
    have h22 : 0 < (bruhatP (orbitMat N k c) * R) 2 2 := by
      have : (bruhatP (orbitMat N k c) * R) 2 2 = -(orbitMat N k c 2 0) := by
        simp [R, realMat_rPrime, Matrix.mul_apply, Fin.sum_univ_three, r0, r1, r2]
      rw [this]; linarith
    have hc := topBlock_det_pos hP'd h20 h21 h22
    exact ⟨TernaryPeriodPolynomials.Argument.FormSeedBridge.hStar_differentiableOn
        (slashTwisted_differentiableOn (n + 3) _ hc _ hh), _,
      hStar_decay _ _ _ (slashTwisted_decay (n + 3) _ hc _ M0 hM0)⟩

end Orbit

end TernaryPeriodPolynomials.Argument.EisensteinClass
