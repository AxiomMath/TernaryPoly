module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Multiplicativity

@[expose] public section


/-!
# Composite Hecke operators `T_m`

For a positive integer `m` the paper defines `H_m` as the set of `[[a,b],[0,d]]` with `a,d ∈ ℤ`,
`a,d > 0`, `ad = m`, `0 ≤ b < d`, and `T_m h = m^{k/2-1} ∑_{A ∈ H_m} h|_k A`.

Normalization used here: `(h|_k A)(τ) = det(A)^{k/2} (cτ+d)^{-k} h(Aτ)`. For upper triangular `A`
(`c = 0`, `det A = m`) this is `m^{k/2} d^{-k} h(Aτ)`, so the operator is written out on points as
`compositeHecke`. The pairs `(a,d)` with `ad = m` are `Nat.divisorsAntidiagonal m`.

Proved here:
* `compositeHecke_prime`: for a prime `p`, `T_p h(τ) = p^{k-1} h(pτ) + p⁻¹ ∑_{b<p} h((τ+b)/p)`, the prime
  formula displayed in the paper;
* `compositeHecke_prime_eigen`: if `h` satisfies the prime Hecke relations with eigenvalues `λ_p`
  (`HasPrimeHeckeRelations`), then `T_p h = λ_p h`.

The composite multiplicativity `T_m T_n = T_{mn}` for `gcd(m,n) = 1` and the statement `T_m h = a_h(m) h`
for all `m ≥ 1` and every normalized eigenform are proved in `MainBodyRows/HeckeCompositeFunction.lean`
(`compositeHecke_comp_coprime`, `compositeHecke_eigenform`). They avoid the coset decomposition: the
composite operator is converted to a q-series with coefficients `compositeCoeff`
(`MainBodyRows/HeckeCompositeSeries.lean`), whose arithmetic lives in `MainBodyRows/HeckeCompositeArith.lean`,
and the identities are read off by q-expansion uniqueness. The Euler product for normalized eigenforms is
proved separately in `MainBodyRows/HeckeEulerProduct.lean`, from the multiplicativity of the Fourier
coefficients (`cuspForm_hecke_multiplicative`).

Formalized by Claude Haiku 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The matrix `[[a,b],[0,d]]` in `GL₂(ℝ)` when its determinant is nonzero, and `1` otherwise. -/
def upperGL (a b d : ℕ) : GeneralLinearGroup (Fin 2) ℝ :=
  if hdet : (!![(a : ℝ), (b : ℝ); 0, (d : ℝ)]).det ≠ 0 then
    GeneralLinearGroup.mkOfDetNeZero _ hdet
  else 1

theorem upperGL_val {a b d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    (upperGL a b d).val = !![(a : ℝ), (b : ℝ); 0, (d : ℝ)] := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdet : (!![(a : ℝ), (b : ℝ); 0, (d : ℝ)]).det ≠ 0 := by
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero]
    exact mul_ne_zero ha' hd'
  unfold upperGL
  rw [dite_eq_left hdet]
  rfl

theorem upperGL_det_pos {a b d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    0 < (GeneralLinearGroup.det (upperGL a b d)).val := by
  change 0 < (upperGL a b d).val.det
  rw [upperGL_val ha hd, Matrix.det_fin_two_of, mul_zero, sub_zero]
  exact mul_pos (by exact_mod_cast ha) (by exact_mod_cast hd)

/-- The point `[[a,b],[0,d]] · τ` of the upper half plane. -/
def upperPoint (a b d : ℕ) (τ : UpperHalfPlane) : UpperHalfPlane :=
  upperGL a b d • τ

theorem upperPoint_coe {a b d : ℕ} (ha : 0 < a) (hd : 0 < d) (τ : UpperHalfPlane) :
    ((upperPoint a b d τ : UpperHalfPlane) : ℂ) = ((a : ℂ) * τ + b) / d := by
  unfold upperPoint
  rw [UpperHalfPlane.coe_smul_of_det_pos (upperGL_det_pos ha hd)]
  unfold UpperHalfPlane.num UpperHalfPlane.denom
  rw [upperGL_val ha hd]
  simp

/-- The composite Hecke operator `T_m` of the paper on functions on the upper half plane:
`T_m f(τ) = m^{k/2-1} ∑_{ad = m, a,d > 0} ∑_{0 ≤ b < d} m^{k/2} d^{-k} f([[a,b],[0,d]] τ)`. -/
def compositeHecke (k : ℤ) (m : ℕ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℂ :=
  (m : ℂ) ^ ((k : ℂ) / 2 - 1) *
    ∑ ad ∈ Nat.divisorsAntidiagonal m, ∑ b ∈ Finset.range ad.2,
      (m : ℂ) ^ ((k : ℂ) / 2) * (ad.2 : ℂ) ^ (-k) * f (upperPoint ad.1 b ad.2 τ)

theorem divisorsAntidiagonal_prime (p : ℕ) (hp : p.Prime) :
    Nat.divisorsAntidiagonal p = {(1, p), (p, 1)} := by
  ext ⟨a, d⟩
  simp only [Nat.mem_divisorsAntidiagonal, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hmul, -⟩
    have ha : a ∣ p := ⟨d, hmul.symm⟩
    rcases (Nat.dvd_prime hp).mp ha with h1 | h1
    · left
      refine ⟨h1, ?_⟩
      rw [h1] at hmul
      omega
    · right
      have hpd : p * d = p * 1 := by
        rw [mul_one]
        rw [h1] at hmul
        exact hmul
      exact ⟨h1, Nat.eq_of_mul_eq_mul_left hp.pos hpd⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [h1, h2]
      exact ⟨one_mul p, hp.ne_zero⟩
    · rw [h1, h2]
      exact ⟨mul_one p, hp.ne_zero⟩

theorem half_weight_mul_pow {k : ℤ} {p : ℕ} (hp : (p : ℂ) ≠ 0) :
    (p : ℂ) ^ ((k : ℂ) / 2 - 1) * (p : ℂ) ^ ((k : ℂ) / 2) = (p : ℂ) ^ (k - 1) := by
  rw [← Complex.cpow_add _ _ hp]
  rw [show (k : ℂ) / 2 - 1 + (k : ℂ) / 2 = ((k - 1 : ℤ) : ℂ) by push_cast; ring,
    Complex.cpow_intCast]

/-- The prime formula for `T_p`: `T_p f(τ) = p^{k-1} f(pτ) + p⁻¹ ∑_{b<p} f((τ+b)/p)`. -/
theorem compositeHecke_prime (k : ℤ) (p : ℕ) (hp : p.Prime) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    compositeHecke k p f τ =
      (p : ℂ) ^ (k - 1) * f (upperPoint p 0 1 τ) +
        (p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (upperPoint 1 b p τ) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hce := half_weight_mul_pow (k := k) hp0
  have hterm : ∀ b : ℕ, (p : ℂ) ^ ((k : ℂ) / 2 - 1) *
      ((p : ℂ) ^ ((k : ℂ) / 2) * (p : ℂ) ^ (-k) * f (upperPoint 1 b p τ)) =
        (p : ℂ)⁻¹ * f (upperPoint 1 b p τ) := by
    intro b
    rw [show (p : ℂ) ^ ((k : ℂ) / 2 - 1) *
        ((p : ℂ) ^ ((k : ℂ) / 2) * (p : ℂ) ^ (-k) * f (upperPoint 1 b p τ)) =
        ((p : ℂ) ^ ((k : ℂ) / 2 - 1) * (p : ℂ) ^ ((k : ℂ) / 2)) * (p : ℂ) ^ (-k) *
          f (upperPoint 1 b p τ) by ring, hce, ← zpow_add₀ hp0]
    rw [show k - 1 + -k = -1 by ring, _root_.zpow_neg_one]
  have hlast : (p : ℂ) ^ ((k : ℂ) / 2 - 1) *
      ((p : ℂ) ^ ((k : ℂ) / 2) * ((1 : ℕ) : ℂ) ^ (-k) * f (upperPoint p 0 1 τ)) =
        (p : ℂ) ^ (k - 1) * f (upperPoint p 0 1 τ) := by
    rw [Nat.cast_one, _root_.one_zpow, mul_one, ← hce]
    ring
  have hpair : (1, p) ≠ (p, 1) := fun h => hp.one_lt.ne (congrArg Prod.fst h)
  unfold compositeHecke
  rw [divisorsAntidiagonal_prime p hp, Finset.sum_pair hpair]
  dsimp only
  rw [Finset.sum_range_one, mul_add, Finset.mul_sum, Finset.sum_congr rfl (fun b _ => hterm b),
    ← Finset.mul_sum, hlast]
  ring

theorem upperPoint_dilate (p : ℕ) (hp : 0 < p) (τ : UpperHalfPlane) :
    upperPoint p 0 1 τ = GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate p hp) • τ := by
  apply UpperHalfPlane.ext
  rw [upperPoint_coe hp Nat.one_pos τ, binaryHeckeDilate_smul]
  simp

theorem upperPoint_translate (p : ℕ) (hp : 0 < p) (index : Fin p) (τ : UpperHalfPlane) :
    upperPoint 1 index p τ =
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate p hp index) • τ := by
  apply UpperHalfPlane.ext
  rw [upperPoint_coe Nat.one_pos hp τ, binaryHeckeTranslate_smul]
  simp

/-- For an eigenform of the prime Hecke relations, `T_p h = λ_p h`. -/
theorem compositeHecke_prime_eigen (k : ℤ) (p : Nat.Primes) (f : UpperHalfPlane → ℂ)
    (eigenvalues : Nat.Primes → ℂ) (relations : HasPrimeHeckeRelations k f eigenvalues)
    (τ : UpperHalfPlane) :
    compositeHecke k p f τ = eigenvalues p * f τ := by
  rw [compositeHecke_prime k p p.property f τ, relations p τ]
  congr 1
  · rw [upperPoint_dilate p p.property.pos τ]
  · congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun index _ => by rw [upperPoint_translate p p.property.pos index τ]

end TernaryPeriodPolynomials.Argument.Identities
