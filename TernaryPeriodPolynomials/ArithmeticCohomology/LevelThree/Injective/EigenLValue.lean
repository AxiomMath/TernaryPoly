module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Hecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Moment
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Multiplicativity
public import Mathlib.NumberTheory.ModularForms.LFunction

@[expose] public section


/-!
# Imaginary-axis moments of joint Hecke eigenforms on `Γ₁(3)`

Let `f ≠ 0` be a cusp form of weight `k > 0` on `Γ₁(3)` which is an eigenvector of every `T_p`
(`p ≠ 3`) and of `U_3`, with eigenvalue `λ_p`. Its `q`-expansion coefficients `a_n` satisfy, for
every prime `p`, `λ_p a_n = d_p a_{n/p} + a_{pn}` with `d_p = χ_k(p) p^{k-1}` for `p ≠ 3` and
`d_3 = 0`. By Sol's level-generic argument `a_1 ≠ 0`, the normalised coefficients are
multiplicative with Euler factors of degree two, hence `L(f, s) ≠ 0` for real `s > k/2 + 1`.
Through Mathlib's `CuspForm.hasSum_L` and `CuspForm.Λ_eq_mellin` this gives the nonvanishing of the
moments `∫_0^∞ t^p f(i t) dt` for `p + 1 > k/2 + 1` (`moment_ne_zero_of_jointEigen`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm
open UpperHalfPlane
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke

namespace TernaryPeriodPolynomials.LevelThreeInjective.EigenLValue

open TernaryPeriodPolynomials.LevelThreeInjective.Moment

/-- The `q`-expansion coefficients (period one) of a cusp form on `Γ₁(3)`. -/
abbrev coeffs {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) : ℕ → ℂ :=
  fun n => (qExpansion 1 (f : ℍ → ℂ)).coeff n

/-- The Hecke determinant: `χ_k(p) p^{k-1}` for `p ≠ 3` and `0` for the `U_3` operator. -/
def heckeDet (k : ℤ) (p : Nat.Primes) : ℂ :=
  if p.val = 3 then 0 else levelThreeChar k p.val * (p.val : ℂ) ^ (k - 1)

/-- The width of the cusp `∞` of `Γ₁(3)` is one. -/
theorem strictWidthInfty_eq_one : binaryRealGammaOneThree.strictWidthInfty = 1 :=
  Subgroup.strictWidthInfty_eq_one_of_T_mem (Γ := CongruenceSubgroup.Gamma1 3) gammaOneThree_T_mem

/-- The uniform coefficient relation of a joint eigenform, at every prime. -/
theorem coeff_relations {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (eigenvalues : Nat.Primes → ℂ)
    (hT : ∀ (p : Nat.Primes) (hp : p.val ≠ 3), levelThreeHecke k p hp f = eigenvalues p • f)
    (hU : levelThreeU3 k f = eigenvalues ⟨3, Nat.prime_three⟩ • f)
    (p : Nat.Primes) (n : ℕ) :
    eigenvalues p * coeffs f n =
      heckeDet k p * qSeriesDilateCoefficients (coeffs f) p.val n + coeffs f (p.val * n) := by
  by_cases h : p.val = 3
  · have hd : heckeDet k p = 0 := by
      unfold heckeDet
      exact ite_eq_left h
    rw [hd, zero_mul, zero_add]
    have hp : p = ⟨3, Nat.prime_three⟩ := Subtype.ext h
    subst hp
    have h1 := congrArg
      (fun g : CuspForm binaryRealGammaOneThree k => (qExpansion 1 (g : ℍ → ℂ)).coeff n) hU
    simp only [levelThreeU3_coeff, coeff_smul] at h1
    exact h1.symm
  · have h1 := congrArg (fun g : CuspForm binaryRealGammaOneThree k => (qExpansion 1 (g : ℍ → ℂ)).coeff n)
      (hT p h)
    simp only [levelThreeHecke_coeff, coeff_smul] at h1
    have hd : heckeDet k p = levelThreeChar k p.val * (p.val : ℂ) ^ (k - 1) := by
      unfold heckeDet
      exact ite_eq_right h
    rw [hd]
    exact h1.symm

/-- The first coefficient of a nonzero joint eigenform is nonzero. -/
theorem coeff_one_ne_zero {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (hf : f ≠ 0)
    (eigenvalues : Nat.Primes → ℂ)
    (hT : ∀ (p : Nat.Primes) (hp : p.val ≠ 3), levelThreeHecke k p hp f = eigenvalues p • f)
    (hU : levelThreeU3 k f = eigenvalues ⟨3, Nat.prime_three⟩ • f) :
    coeffs f 1 ≠ 0 := by
  intro h1
  have zero := coefficients_zero_of_prime_hecke_relations (coeffs f) eigenvalues (heckeDet k)
    (CuspFormClass.qExpansion_coeff_zero f (by norm_num : (0 : ℝ) < 1)
      LevelThreeHeckeSum.one_mem_strictPeriods) h1 (coeff_relations f eigenvalues hT hU)
  have expansion_zero : qExpansion 1 (f : ℍ → ℂ) = 0 := by
    ext n
    simpa only [map_zero] using zero n
  have modular_zero : CuspForm.toModularFormₗ f = 0 :=
    (ModularForm.qExpansion_eq_zero_iff (by norm_num : (0 : ℝ) < 1)
      LevelThreeHeckeSum.one_mem_strictPeriods (CuspForm.toModularFormₗ f)).mp expansion_zero
  apply hf
  apply DFunLike.ext
  intro point
  exact congrArg (fun modular : ModularForm binaryRealGammaOneThree k => modular point) modular_zero

/-- A joint eigenform may be normalised to have first coefficient one. -/
theorem exists_normalized {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (hf : f ≠ 0)
    (eigenvalues : Nat.Primes → ℂ)
    (hT : ∀ (p : Nat.Primes) (hp : p.val ≠ 3), levelThreeHecke k p hp f = eigenvalues p • f)
    (hU : levelThreeU3 k f = eigenvalues ⟨3, Nat.prime_three⟩ • f) :
    ∃ g : CuspForm binaryRealGammaOneThree k,
      (∀ (p : Nat.Primes) (hp : p.val ≠ 3), levelThreeHecke k p hp g = eigenvalues p • g) ∧
      levelThreeU3 k g = eigenvalues ⟨3, Nat.prime_three⟩ • g ∧ coeffs g 1 = 1 ∧
      coeffs g = (coeffs f 1)⁻¹ • coeffs f := by
  have first_ne := coeff_one_ne_zero f hf eigenvalues hT hU
  refine ⟨(coeffs f 1)⁻¹ • f, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [map_smul, hT p hp]
    exact smul_comm _ _ _
  · rw [map_smul, hU]
    exact smul_comm _ _ _
  · change (qExpansion 1 (((coeffs f 1)⁻¹ • f : CuspForm binaryRealGammaOneThree k) : ℍ → ℂ)).coeff 1 = 1
    rw [coeff_smul]
    exact inv_mul_cancel₀ first_ne
  · funext n
    change (qExpansion 1 (((coeffs f 1)⁻¹ • f : CuspForm binaryRealGammaOneThree k) : ℍ → ℂ)).coeff n = _
    rw [coeff_smul]
    rfl

/-- The coefficient of a normalised eigenform at a prime is its eigenvalue. -/
theorem first_of_relations (a : ℕ → ℂ) (trace determinant : Nat.Primes → ℂ) (initial : a 1 = 1)
    (relations : ∀ (prime : Nat.Primes) (index : ℕ),
      trace prime * a index =
        determinant prime * qSeriesDilateCoefficients a prime.val index + a (prime.val * index))
    (prime : Nat.Primes) : a prime.val = trace prime := by
  have relation := relations prime 1
  have not_divides : ¬prime.val ∣ 1 := fun divides => prime.property.ne_one (Nat.dvd_one.mp divides)
  simpa only [qSeriesDilateCoefficients, ite_eq_right not_divides, initial, mul_one, mul_zero,
    zero_add] using relation.symm

/-- The prime-power recurrence of a normalised eigenform. -/
theorem recurrence_of_relations (a : ℕ → ℂ) (trace determinant : Nat.Primes → ℂ)
    (relations : ∀ (prime : Nat.Primes) (index : ℕ),
      trace prime * a index =
        determinant prime * qSeriesDilateCoefficients a prime.val index + a (prime.val * index))
    (prime : Nat.Primes) (exponent : ℕ) :
    a (prime.val ^ (exponent + 2)) =
      trace prime * a (prime.val ^ (exponent + 1)) - determinant prime * a (prime.val ^ exponent) := by
  have relation := relations prime (prime.val ^ (exponent + 1))
  have divides : prime.val ∣ prime.val ^ (exponent + 1) := dvd_pow_self _ (by omega)
  have quotient : prime.val ^ (exponent + 1) / prime.val = prime.val ^ exponent := by
    rw [pow_succ, Nat.mul_div_cancel _ prime.property.pos]
  have product : prime.val * prime.val ^ (exponent + 1) = prime.val ^ (exponent + 2) :=
    (pow_succ' prime.val (exponent + 1)).symm
  rw [qSeriesDilateCoefficients, ite_eq_left divides, quotient, product] at relation
  linear_combination -relation

/-- For a normalised joint eigenform the `L`-series is nonzero for real `s > k/2 + 1`. -/
theorem LSeries_ne_zero_of_normalized {k : ℤ} (hk : 0 < k) (g : CuspForm binaryRealGammaOneThree k)
    (eigenvalues : Nat.Primes → ℂ)
    (hT : ∀ (p : Nat.Primes) (hp : p.val ≠ 3), levelThreeHecke k p hp g = eigenvalues p • g)
    (hU : levelThreeU3 k g = eigenvalues ⟨3, Nat.prime_three⟩ • g) (initial : coeffs g 1 = 1)
    (argument : ℝ) (bound : (k : ℝ) / 2 + 1 < argument) :
    LSeries (coeffs g) (argument : ℂ) ≠ 0 := by
  have relations := coeff_relations g eigenvalues hT hU
  have nonvanishing := cuspForm_removedLSeries_ne_zero_of_recurrence hk g 1 argument bound
    eigenvalues (heckeDet k)
    (by simpa only [strictWidthInfty_eq_one] using initial)
    (by simpa only [strictWidthInfty_eq_one] using
      multiplicative_of_prime_hecke_relations (coeffs g) eigenvalues (heckeDet k) initial relations)
    (fun prime => by
      simpa only [strictWidthInfty_eq_one] using
        first_of_relations (coeffs g) eigenvalues (heckeDet k) initial relations prime)
    (fun prime exponent => by
      simpa only [strictWidthInfty_eq_one] using
        recurrence_of_relations (coeffs g) eigenvalues (heckeDet k) relations prime exponent)
  have removed (coefficients : ℕ → ℂ) : removeEulerCoefficients coefficients 1 = coefficients := by
    funext index
    simp [removeEulerCoefficients]
  simp only [strictWidthInfty_eq_one] at nonvanishing
  rw [removed] at nonvanishing
  exact nonvanishing

/-- The `L`-series of a cusp form on `Γ₁(3)` is Mathlib's `L`-function in the half-plane of
absolute convergence. -/
theorem LSeries_eq_L {k : ℤ} (hk : 0 < k) (f : CuspForm binaryRealGammaOneThree k) (s : ℂ)
    (convergent : (k : ℝ) / 2 + 1 < s.re) : LSeries (coeffs f) s = ModularForm.L hk f s := by
  have zero := CuspFormClass.qExpansion_coeff_zero f (by norm_num : (0 : ℝ) < 1)
    LevelThreeHeckeSum.one_mem_strictPeriods
  have summed := CuspForm.hasSum_L hk f convergent
  simp only [strictWidthInfty_eq_one, Complex.ofReal_one, Complex.one_cpow, one_mul] at summed
  have terms : LSeries.term (coeffs f) s =
      fun index => (qExpansion 1 (f : ℍ → ℂ)).coeff index / (index : ℂ) ^ s := by
    funext index
    rw [LSeries.term_def]
    split_ifs with is_zero
    · subst index
      simp only [zero, zero_div]
    · rfl
  change (∑' index, LSeries.term (coeffs f) s index) = _
  rw [terms]
  exact summed.tsum_eq

/-- Nonvanishing of the `L`-series at `p + 1` gives a nonvanishing moment. -/
theorem moment_ne_zero_of_LSeries {k : ℤ} (hk : 0 < k) (f : CuspForm binaryRealGammaOneThree k)
    (p : ℕ) (convergent : (k : ℝ) / 2 + 1 < (p : ℝ) + 1)
    (nonzero : LSeries (coeffs f) ((p : ℂ) + 1) ≠ 0) : Moment.moment (⇑f) p ≠ 0 := by
  have bound : (k : ℝ) / 2 + 1 < ((p : ℂ) + 1).re := by simpa using convergent
  rw [LSeries_eq_L hk f _ bound] at nonzero
  rw [moment_eq_mellin]
  intro zero
  apply nonzero
  rw [ModularForm.L, CuspForm.Λ_eq_mellin, zero]
  simp

/-- **Moments of a joint Hecke eigenform.** A nonzero joint eigenform of all `T_p` (`p ≠ 3`) and
`U_3` of positive weight `k` on `Γ₁(3)` has nonzero moment `∫_0^∞ t^p f(i t) dt` whenever
`p + 1 > k/2 + 1`. -/
theorem moment_ne_zero_of_jointEigen {k : ℤ} (hk : 0 < k)
    (f : CuspForm binaryRealGammaOneThree k) (hf : f ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (hT : ∀ (p : Nat.Primes) (hp : p.val ≠ 3), levelThreeHecke k p hp f = eigenvalues p • f)
    (hU : levelThreeU3 k f = eigenvalues ⟨3, Nat.prime_three⟩ • f)
    (p : ℕ) (hp : (k : ℝ) / 2 + 1 < (p : ℝ) + 1) :
    Moment.moment (⇑f) p ≠ 0 := by
  obtain ⟨g, gT, gU, g1, gc⟩ := exists_normalized f hf eigenvalues hT hU
  have nonzero := LSeries_ne_zero_of_normalized hk g eigenvalues gT gU g1 ((p : ℝ) + 1) hp
  have cast : (((p : ℝ) + 1 : ℝ) : ℂ) = (p : ℂ) + 1 := by
    simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  rw [cast, gc, LSeries_smul] at nonzero
  exact moment_ne_zero_of_LSeries hk f p hp (fun h => nonzero (by rw [h, mul_zero]))

end TernaryPeriodPolynomials.LevelThreeInjective.EigenLValue
