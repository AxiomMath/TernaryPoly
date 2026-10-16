module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.PrimeLatticeMeasure
public import Mathlib.Data.Nat.Factorization.Induction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem adeleNorm_mul_image (idele : Adelesˣ) (domain : Set Adeles) :
    (adeleNorm idele : ENNReal) * adeleMeasure domain =
      adeleMeasure ((fun value => idele.val * value) '' domain) := by
  have scaling := adeleNorm_mul_preimage idele ((fun value => idele.val * value) '' domain)
  have injective : Function.Injective (fun value : Adeles => idele.val * value) :=
    (ContinuousAddEquiv.mulLeft idele).injective
  rw [Set.preimage_image_eq domain injective] at scaling
  exact scaling

theorem primeLattice_eq_image (prime : Nat.Primes) :
    primeLattice prime = (fun value : FiniteAdeles => (prime.val : FiniteAdeles) * value) ''
      Set.range integralEmbedding := by
  ext value
  constructor
  · rintro ⟨integralValue, rfl⟩
    refine ⟨integralEmbedding integralValue, ⟨integralValue, rfl⟩, ?_⟩
    change (prime.val : FiniteAdeles) * integralEmbedding integralValue =
      integralEmbedding ((prime.val : IntegralAdeles) * integralValue)
    rw [map_mul, map_natCast]
  · rintro ⟨_, ⟨integralValue, rfl⟩, rfl⟩
    refine ⟨integralValue, ?_⟩
    change integralEmbedding ((prime.val : IntegralAdeles) * integralValue) =
      (prime.val : FiniteAdeles) * integralEmbedding integralValue
    rw [map_mul, map_natCast]

noncomputable def primeRationalUnit (prime : Nat.Primes) : ℚˣ :=
  Units.mk0 (prime.val : ℚ) (Nat.cast_ne_zero.mpr prime.property.ne_zero)

theorem adeleNorm_rational_prime (prime : Nat.Primes) :
    adeleNorm (Units.map rationalAdele (primeRationalUnit prime)) = 1 := by
  let idele : Adelesˣ := Units.map rationalAdele (primeRationalUnit prime)
  have real_positive : 0 < (prime.val : ℝ) := by exact_mod_cast prime.property.pos
  have multiplier_eq : idele.val = ((prime.val : ℝ), (prime.val : FiniteAdeles)) := by
    simp [idele, primeRationalUnit, rationalAdele]
    rfl
  have function_eq :
      (fun value : Adeles => idele.val * value) =
        Prod.map (fun value : ℝ => (prime.val : ℝ) * value)
          (fun value : FiniteAdeles => (prime.val : FiniteAdeles) * value) := by
    funext value
    rw [multiplier_eq]
    rfl
  have domain_image : (fun value : Adeles => idele.val * value) '' additiveDomain =
      Set.Ico 0 (prime.val : ℝ) ×ˢ primeLattice prime := by
    rw [function_eq, additiveDomain, Set.prodMap_image_prod,
      Set.image_mul_left_Ico real_positive, ← primeLattice_eq_image, mul_zero, mul_one]
  have scaling := adeleNorm_mul_image idele additiveDomain
  rw [adeleMeasure_additiveDomain, mul_one, domain_image, adeleMeasure,
    Measure.prod_prod, Real.volume_Ico, sub_zero, ENNReal.ofReal_natCast,
    prime_mul_primeLattice_measure] at scaling
  exact ENNReal.coe_injective scaling

theorem adeleNorm_rational_nat (value : ℕ) (nonzero : value ≠ 0) :
    adeleNorm (Units.map rationalAdele
      (Units.mk0 (value : ℚ) (Nat.cast_ne_zero.mpr nonzero))) = 1 := by
  revert nonzero
  refine Nat.recOnPrimePow ?_ ?_ ?_ value
  · intro nonzero
    exact (nonzero rfl).elim
  · intro nonzero
    simp
  · intro remaining prime power prime_spec _ _ induction_hypothesis nonzero
    have remaining_nonzero : remaining ≠ 0 := by
      intro remaining_zero
      simp only [remaining_zero, mul_zero, ne_eq, not_true_eq_false] at nonzero
    have units_equal :
        Units.mk0 ((prime ^ power * remaining : ℕ) : ℚ) (Nat.cast_ne_zero.mpr nonzero) =
          primeRationalUnit ⟨prime, prime_spec⟩ ^ power *
            Units.mk0 (remaining : ℚ) (Nat.cast_ne_zero.mpr remaining_nonzero) := by
      apply Units.ext
      simp [primeRationalUnit]
    rw [units_equal]
    simp only [map_mul, map_pow, induction_hypothesis remaining_nonzero]
    rw [adeleNorm_rational_prime ⟨prime, prime_spec⟩, one_pow, one_mul]

theorem adeleNorm_rational_neg_one :
    adeleNorm (Units.map rationalAdele (-1 : ℚˣ)) = 1 := by
  have split : Units.map rationalAdele (-1 : ℚˣ) =
      realAdeleUnit (-1 : ℝˣ) * integralAdeleUnit (-1 : IntegralAdelesˣ) := by
    apply Units.ext
    simp [rationalAdele, realAdeleUnit, integralAdeleUnit]
    rfl
  rw [split, map_mul, adeleNorm_integralAdeleUnit, mul_one]
  apply NNReal.coe_injective
  rw [adeleNorm_realAdeleUnit]
  norm_num

theorem adeleNorm_rational_int (value : ℤ) (nonzero : value ≠ 0) :
    adeleNorm (Units.map rationalAdele
      (Units.mk0 (value : ℚ) (Int.cast_ne_zero.mpr nonzero))) = 1 := by
  obtain ⟨naturalValue, positive | negative⟩ := Int.eq_nat_or_neg value
  · subst value
    exact adeleNorm_rational_nat naturalValue (by exact_mod_cast nonzero)
  · subst value
    have natural_nonzero : naturalValue ≠ 0 := by
      intro natural_zero
      simp only [natural_zero, Nat.cast_zero, neg_zero, ne_eq, not_true_eq_false] at nonzero
    have units_equal :
        Units.mk0 ((-(naturalValue : ℤ) : ℤ) : ℚ) (Int.cast_ne_zero.mpr nonzero) =
          (-1 : ℚˣ) * Units.mk0 (naturalValue : ℚ) (Nat.cast_ne_zero.mpr natural_nonzero) := by
      apply Units.ext
      simp
    rw [units_equal]
    simp only [map_mul, adeleNorm_rational_neg_one,
      adeleNorm_rational_nat naturalValue natural_nonzero, one_mul]

theorem adeleNorm_rational (unit : ℚˣ) : adeleNorm (Units.map rationalAdele unit) = 1 := by
  have numerator_nonzero : unit.val.num ≠ 0 := by
    exact Rat.num_ne_zero.mpr (Units.ne_zero unit)
  have denominator_nonzero : unit.val.den ≠ 0 := unit.val.den_nz
  let numerator : ℚˣ := Units.mk0 (unit.val.num : ℚ) (Int.cast_ne_zero.mpr numerator_nonzero)
  let denominator : ℚˣ := Units.mk0 (unit.val.den : ℚ) (Nat.cast_ne_zero.mpr denominator_nonzero)
  have units_equal : numerator = unit * denominator := by
    apply Units.ext
    change (unit.val.num : ℚ) = unit.val * (unit.val.den : ℚ)
    exact (div_eq_iff (Nat.cast_ne_zero.mpr denominator_nonzero)).mp (Rat.num_div_den unit.val)
  have norm_equal := congrArg (fun rationalUnit : ℚˣ =>
    adeleNorm (Units.map rationalAdele rationalUnit)) units_equal
  change adeleNorm (Units.map rationalAdele numerator) = _ at norm_equal
  rw [adeleNorm_rational_int unit.val.num numerator_nonzero] at norm_equal
  have denominator_norm : adeleNorm (Units.map rationalAdele denominator) = 1 :=
    adeleNorm_rational_nat unit.val.den denominator_nonzero
  rw [map_mul, map_mul, denominator_norm, mul_one] at norm_equal
  exact norm_equal.symm

theorem normPower_rational (unit : ℚˣ) (exponent : ℂ) :
    normPower (Units.map rationalAdele unit) exponent = 1 := by
  simp [normPower, adeleNorm_rational]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
