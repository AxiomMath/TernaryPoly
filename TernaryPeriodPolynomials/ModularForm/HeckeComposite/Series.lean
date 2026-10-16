module

public import TernaryPeriodPolynomials.ModularForm.HeckeEuler.Operators
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.QExpansion

@[expose] public section


/-!
# q-series of the composite Hecke operator

For any function `f` on the upper half plane whose `q`-expansion with coefficients `c` converges
everywhere (`hq`), the composite operator `T_m f` has the `q`-expansion with coefficients
`compositeCoeff k m c N = ∑_{ad = m} [a ∣ N] a^{k-1} c(d·(N/a))`. No modularity is used.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open Function.Periodic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open scoped BigOperators

/-- The `q`-coefficients of `T_m f` for `f` with `q`-coefficients `c`. -/
def compositeCoeff (k : ℤ) (m : ℕ) (c : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ ad ∈ Nat.divisorsAntidiagonal m,
    if ad.1 ∣ N then (ad.1 : ℂ) ^ (k - 1) * c (ad.2 * (N / ad.1)) else 0

/-- The scalar identity of one `(a,d)` block: `m^{k/2-1} ∑_b m^{k/2} d^{-k} g_b = a^{k-1} d^{-1} ∑_b g_b`
when `m = a d`. -/
theorem pair_scalar (k : ℤ) {m a d : ℕ} (ha : 0 < a) (hd : 0 < d) (hm : (m : ℂ) = (a : ℂ) * (d : ℂ))
    (g : ℕ → ℂ) :
    (m : ℂ) ^ ((k : ℂ) / 2 - 1) * ∑ b ∈ Finset.range d, (m : ℂ) ^ ((k : ℂ) / 2) * (d : ℂ) ^ (-k) * g b =
      (a : ℂ) ^ (k - 1) * ((d : ℂ)⁻¹ * ∑ b ∈ Finset.range d, g b) := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hm0 : (m : ℂ) ≠ 0 := by rw [hm]; exact mul_ne_zero ha0 hd0
  have key : (m : ℂ) ^ (k - 1) = (a : ℂ) ^ (k - 1) * (d : ℂ) ^ (k - 1) := by
    rw [hm, mul_zpow]
  have dd : (d : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k) = (d : ℂ)⁻¹ := by
    rw [← zpow_add₀ hd0, show k - 1 + -k = -1 by ring, zpow_neg_one]
  rw [← Finset.mul_sum]
  calc (m : ℂ) ^ ((k : ℂ) / 2 - 1) * ((m : ℂ) ^ ((k : ℂ) / 2) * (d : ℂ) ^ (-k) * ∑ b ∈ Finset.range d, g b)
      = ((m : ℂ) ^ ((k : ℂ) / 2 - 1) * (m : ℂ) ^ ((k : ℂ) / 2)) * (d : ℂ) ^ (-k) *
          ∑ b ∈ Finset.range d, g b := by ring
    _ = (m : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k) * ∑ b ∈ Finset.range d, g b := by
          rw [half_weight_mul_pow hm0]
    _ = ((a : ℂ) ^ (k - 1) * (d : ℂ) ^ (k - 1)) * (d : ℂ) ^ (-k) * ∑ b ∈ Finset.range d, g b := by
          rw [key]
    _ = (a : ℂ) ^ (k - 1) * ((d : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k)) * ∑ b ∈ Finset.range d, g b := by
          ring
    _ = (a : ℂ) ^ (k - 1) * ((d : ℂ)⁻¹ * ∑ b ∈ Finset.range d, g b) := by
          rw [dd]; ring

/-- One `(a,d)` block of `T_m f` as a `q`-series. -/
theorem pair_hasSum {k : ℤ} {m a d : ℕ} (ha : 0 < a) (hd : 0 < d) (hm : (m : ℂ) = (a : ℂ) * (d : ℂ))
    (c : ℕ → ℂ) {f : UpperHalfPlane → ℂ}
    (hq : ∀ z : UpperHalfPlane, HasSum (fun n => c n * qParam 1 (z : ℂ) ^ n) (f z))
    (τ : UpperHalfPlane) :
    HasSum (fun N => (if a ∣ N then (a : ℂ) ^ (k - 1) * c (d * (N / a)) else 0) * qParam 1 (τ : ℂ) ^ N)
      ((m : ℂ) ^ ((k : ℂ) / 2 - 1) *
        ∑ b ∈ Finset.range d, (m : ℂ) ^ ((k : ℂ) / 2) * (d : ℂ) ^ (-k) * f (upperPoint a b d τ)) := by
  classical
  have scalarEq := pair_scalar k ha hd hm (fun b => f (upperPoint a b d τ))
  beta_reduce at scalarEq
  rw [scalarEq]
  have series : ∀ residue : Fin d,
      HasSum (fun index => c index * qParam 1 (((a : ℂ) * (τ : ℂ) + (residue.val : ℂ)) / (d : ℂ)) ^ index)
        (f (upperPoint a residue.val d τ)) := by
    intro residue
    have h := hq (upperPoint a residue.val d τ)
    rw [upperPoint_coe ha hd] at h
    exact h
  have sumEq : ∑ residue : Fin d, f (upperPoint a residue.val d τ) =
      ∑ b ∈ Finset.range d, f (upperPoint a b d τ) :=
    Fin.sum_univ_eq_sum_range (fun b => f (upperPoint a b d τ)) d
  have avg : HasSum (fun index => c (d * index) * qParam 1 ((a : ℂ) * (τ : ℂ)) ^ index)
      ((d : ℂ)⁻¹ * ∑ b ∈ Finset.range d, f (upperPoint a b d τ)) := by
    rw [← sumEq]
    exact qSeries_average_hasSum c ((a : ℂ) * (τ : ℂ)) d hd
      (fun residue => f (upperPoint a residue.val d τ)) series
  have scaled := avg.mul_left ((a : ℂ) ^ (k - 1))
  have injective : Function.Injective (fun j : ℕ => a * j) :=
    fun x y e => Nat.eq_of_mul_eq_mul_left ha e
  refine (injective.hasSum_iff ?_).mp ?_
  · intro N hN
    have not_divides : ¬ a ∣ N := by
      rintro ⟨j, hj⟩
      exact hN ⟨j, hj.symm⟩
    rw [ite_eq_right not_divides, zero_mul]
  · refine scaled.congr_fun (fun j => ?_)
    simp only [Function.comp_apply]
    rw [ite_eq_left (dvd_mul_right a j), Nat.mul_div_cancel_left j ha, qParam_one_nat_mul, pow_mul]
    ring

/-- The `q`-series of the composite Hecke operator `T_m f`, for any `f` with everywhere-convergent
`q`-expansion of coefficients `c`. -/
theorem compositeHecke_hasSum {k : ℤ} {m : ℕ} (hm : 0 < m) (c : ℕ → ℂ) {f : UpperHalfPlane → ℂ}
    (hq : ∀ z : UpperHalfPlane, HasSum (fun n => c n * qParam 1 (z : ℂ) ^ n) (f z))
    (τ : UpperHalfPlane) :
    HasSum (fun N => compositeCoeff k m c N * qParam 1 (τ : ℂ) ^ N) (compositeHecke k m f τ) := by
  have pairs : ∀ ad ∈ Nat.divisorsAntidiagonal m,
      HasSum (fun N => (if ad.1 ∣ N then (ad.1 : ℂ) ^ (k - 1) * c (ad.2 * (N / ad.1)) else 0) *
          qParam 1 (τ : ℂ) ^ N)
        ((m : ℂ) ^ ((k : ℂ) / 2 - 1) *
          ∑ b ∈ Finset.range ad.2, (m : ℂ) ^ ((k : ℂ) / 2) * (ad.2 : ℂ) ^ (-k) * f (upperPoint ad.1 b ad.2 τ)) := by
    intro ad had
    rw [Nat.mem_divisorsAntidiagonal] at had
    have ha : 0 < ad.1 := Nat.pos_of_ne_zero (fun h0 => hm.ne' (by rw [← had.1, h0, zero_mul]))
    have hd : 0 < ad.2 := Nat.pos_of_ne_zero (fun h0 => hm.ne' (by rw [← had.1, h0, mul_zero]))
    exact pair_hasSum ha hd (by rw [← had.1, Nat.cast_mul]) c hq τ
  have total := hasSum_sum (fun ad had => pairs ad had)
  have hval : compositeHecke k m f τ = ∑ ad ∈ Nat.divisorsAntidiagonal m,
      (m : ℂ) ^ ((k : ℂ) / 2 - 1) *
        ∑ b ∈ Finset.range ad.2, (m : ℂ) ^ ((k : ℂ) / 2) * (ad.2 : ℂ) ^ (-k) * f (upperPoint ad.1 b ad.2 τ) := by
    unfold compositeHecke
    rw [Finset.mul_sum]
  have fcongr : (fun N => compositeCoeff k m c N * qParam 1 (τ : ℂ) ^ N) =
      fun N => ∑ ad ∈ Nat.divisorsAntidiagonal m,
        (if ad.1 ∣ N then (ad.1 : ℂ) ^ (k - 1) * c (ad.2 * (N / ad.1)) else 0) * qParam 1 (τ : ℂ) ^ N := by
    funext N
    unfold compositeCoeff
    rw [Finset.sum_mul]
  rw [fcongr, hval]
  exact total

end TernaryPeriodPolynomials.Argument.Identities
