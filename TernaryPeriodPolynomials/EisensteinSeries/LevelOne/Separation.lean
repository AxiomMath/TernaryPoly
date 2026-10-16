module

public import TernaryPeriodPolynomials.EisensteinSeries.LevelOne.EisensteinScalar

@[expose] public section


/-!
# Separation of the cuspidal pair character from the Eisenstein eigenvalue

The Eisenstein eigenvalue of `T_p` on `H¹(GL₂(ℤ), Sym^d ⊗ det^σ) / periodImage` is
`q = p^(d+1-σ) + p^(-σ) > p^(d+1-σ)`. The local operator of the identity-plane cusp acts on the
edge by `1 + p^{-(n+2)} T_p` (`d = n + 1`, `σ = -1`) and that of the good-line cusp by
`1 + p^{-(n+1)} T_p` (`d = n + 1`, `σ = 0`). If the character value `c1 = c(T_2)` satisfies
`‖c1 - 1‖ ≤ 3/4` (the cuspidal pair character at `n ≥ 3`), the `H¹` eigenvalue
`e_2 = (c1 - 1) / (2^{-(n+2)})`, resp. `(c1 - 1) / (2^{-(n+1)})`, has norm below `2^{d+1-σ} < q`.
Hence the joint generalized eigenspace of `H¹` with eigenvalues `e` has dimension at most one
(`finrank_jointH1_identity_le_one`, `finrank_jointH1_goodLine_le_one`).

Original work by Claude Sonnet 5.5 and Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups
open GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.BoundaryFunctional
open TernaryPeriodPolynomials.Spectral.ParabolicES

namespace TernaryPeriodPolynomials.LevelOneEisenstein

/-- The prime `2`. -/
def two : Nat.Primes := ⟨2, Nat.prime_two⟩

theorem two_ne_three : two.val ≠ 3 := by decide

theorem q_eq_ofReal (d : ℕ) (σ : ℤ) (p : Nat.Primes) :
    q d σ p = (((p.val : ℝ) ^ ((d : ℤ) + 1 - σ) + (p.val : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  simp [q]

/-- The Eisenstein eigenvalue has norm at least `p^(d+1-σ)`. -/
theorem le_norm_q (d : ℕ) (σ : ℤ) (p : Nat.Primes) :
    (p.val : ℝ) ^ ((d : ℤ) + 1 - σ) ≤ ‖q d σ p‖ := by
  have h1 : 0 ≤ (p.val : ℝ) ^ ((d : ℤ) + 1 - σ) := zpow_nonneg (Nat.cast_nonneg _) _
  have h2 : 0 ≤ (p.val : ℝ) ^ (-σ) := zpow_nonneg (Nat.cast_nonneg _) _
  rw [q_eq_ofReal, Complex.norm_real, Real.norm_of_nonneg (add_nonneg h1 h2)]
  linarith

/-- **Multiplicity one in `H¹(GL₂(ℤ), Sym^d ⊗ det^σ)`, norm form**: if the `T_2` eigenvalue has norm
below `2^(d+1-σ)`, the joint generalized eigenspace has dimension at most one. -/
theorem finrank_jointH1_le_one_of_norm_lt {d : ℕ} (hd : Even d) (hpos : 0 < d) (σ : ℤ)
    (e : Nat.Primes → ℂ) (h : ‖e two‖ < (2 : ℝ) ^ ((d : ℤ) + 1 - σ)) :
    Module.finrank ℂ (jointH1 d σ e) ≤ 1 := by
  obtain ⟨r, rfl⟩ := hd.two_dvd
  refine finrank_jointH1_le_one_of_ne r (by omega) σ e two two_ne_three ?_
  intro heq
  have hq := le_norm_q (2 * r) σ two
  rw [← heq] at hq
  have h2 : ((two.val : ℕ) : ℝ) = 2 := by simp [two]
  rw [h2] at hq
  exact absurd h (not_lt.mpr hq)

/-- **Identity-plane cusp.** For `n` odd and the `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` eigenvalues `e`
with `e 2 = (c1 - 1) / (2^{n+2})⁻¹` and `‖c1 - 1‖ ≤ 3/4`, the joint generalized eigenspace of the
`T_p` (`p ≠ 3`) has dimension at most one. -/
theorem finrank_jointH1_identity_le_one {n : ℕ} (hodd : Odd n) (e : Nat.Primes → ℂ) (c1 : ℂ)
    (hc : ‖c1 - 1‖ ≤ 3 / 4) (he : e two = (c1 - 1) / (((two.val : ℕ) : ℂ) ^ (n + 2))⁻¹) :
    Module.finrank ℂ (jointH1 (n + 1) (-1) e) ≤ 1 := by
  refine finrank_jointH1_le_one_of_norm_lt hodd.add_one (Nat.succ_pos n) (-1) e ?_
  have hexp : (2 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1 - (-1)) = 2 ^ (n + 3) := by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 - (-1) = ((n + 3 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have h2 : ‖((two.val : ℕ) : ℂ)‖ = 2 := by simp [two]
  rw [hexp, he, norm_div, norm_inv, norm_pow, h2, div_inv_eq_mul]
  have hpos : (0 : ℝ) < 2 ^ (n + 2) := by positivity
  calc ‖c1 - 1‖ * 2 ^ (n + 2) ≤ 3 / 4 * 2 ^ (n + 2) := mul_le_mul_of_nonneg_right hc hpos.le
    _ < 2 ^ (n + 3) := by
      have hx : (2 : ℝ) ^ (n + 3) = 2 * 2 ^ (n + 2) := by ring
      rw [hx]
      linarith

/-- **Good-line cusp.** For `n` odd and the `H¹(GL₂(ℤ), Sym^{n+1})` eigenvalues `e` with
`e 2 = (c1 - 1) / (2^{n+1})⁻¹` and `‖c1 - 1‖ ≤ 3/4`, the joint generalized eigenspace of the `T_p`
(`p ≠ 3`) has dimension at most one. -/
theorem finrank_jointH1_goodLine_le_one {n : ℕ} (hodd : Odd n) (e : Nat.Primes → ℂ) (c1 : ℂ)
    (hc : ‖c1 - 1‖ ≤ 3 / 4) (he : e two = (c1 - 1) / (((two.val : ℕ) : ℂ) ^ (n + 1))⁻¹) :
    Module.finrank ℂ (jointH1 (n + 1) 0 e) ≤ 1 := by
  refine finrank_jointH1_le_one_of_norm_lt hodd.add_one (Nat.succ_pos n) 0 e ?_
  have hexp : (2 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1 - 0) = 2 ^ (n + 2) := by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 - 0 = ((n + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have h2 : ‖((two.val : ℕ) : ℂ)‖ = 2 := by simp [two]
  rw [hexp, he, norm_div, norm_inv, norm_pow, h2, div_inv_eq_mul]
  have hpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  calc ‖c1 - 1‖ * 2 ^ (n + 1) ≤ 3 / 4 * 2 ^ (n + 1) := mul_le_mul_of_nonneg_right hc hpos.le
    _ < 2 ^ (n + 2) := by
      have hx : (2 : ℝ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
      rw [hx]
      linarith

end TernaryPeriodPolynomials.LevelOneEisenstein
