module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarHecke
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.TaylorSeries

@[expose] public section


open scoped BigOperators
open Function.Periodic
open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem primitiveRoot_power_sum {modulus : ℕ} {root : ℂ}
    (primitive : IsPrimitiveRoot root modulus) (exponent : ℕ) :
    (∑ index : Fin modulus, (root ^ exponent) ^ index.val) =
      if modulus ∣ exponent then (modulus : ℂ) else 0 := by
  classical
  by_cases divides : modulus ∣ exponent
  · rw [ite_eq_left divides, (primitive.pow_eq_one_iff_dvd exponent).mpr divides]
    simp
  · rw [ite_eq_right divides, Fin.sum_univ_eq_sum_range,
      geom_sum_eq (fun equal => divides ((primitive.pow_eq_one_iff_dvd exponent).mp equal))]
    have power : (root ^ exponent) ^ modulus = 1 := by
      rw [← pow_mul, Nat.mul_comm exponent modulus, pow_mul, primitive.pow_eq_one, one_pow]
    rw [power, sub_self, zero_div]

theorem qParam_one_nat_mul (point : ℂ) (multiple : ℕ) :
    qParam 1 (multiple * point) = qParam 1 point ^ multiple := by
  simp only [qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem qParam_one_translate_div (point : ℂ) (modulus index : ℕ) :
    qParam 1 ((point + index) / modulus) =
      qParam 1 (point / modulus) *
        Complex.exp (2 * Real.pi * Complex.I / modulus) ^ index := by
  simp only [qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

theorem qParam_one_div_pow (point : ℂ) (modulus : ℕ) (positive : 0 < modulus) :
    qParam 1 (point / modulus) ^ modulus = qParam 1 point := by
  rw [← qParam_one_nat_mul]
  congr 1
  have nonzero : (modulus : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt positive)
  field_simp [nonzero]

theorem qParam_one_average (point : ℂ) (modulus : ℕ) (positive : 0 < modulus) (exponent : ℕ) :
    (∑ index : Fin modulus, qParam 1 ((point + index.val) / modulus) ^ exponent) =
      if modulus ∣ exponent then (modulus : ℂ) * qParam 1 point ^ (exponent / modulus) else 0 := by
  classical
  let root := Complex.exp (2 * Real.pi * Complex.I / modulus)
  have term (index : Fin modulus) : qParam 1 ((point + index.val) / modulus) ^ exponent =
      qParam 1 (point / modulus) ^ exponent * (root ^ exponent) ^ index.val := by
    rw [qParam_one_translate_div, mul_pow]
    change _ * (root ^ index.val) ^ exponent = _
    rw [← pow_mul, Nat.mul_comm index.val exponent, pow_mul]
  simp only [term, ← Finset.mul_sum]
  rw [primitiveRoot_power_sum (Complex.isPrimitiveRoot_exp modulus (ne_of_gt positive))]
  by_cases divides : modulus ∣ exponent
  · rw [ite_eq_left divides, ite_eq_left divides]
    have power : qParam 1 (point / modulus) ^ exponent = qParam 1 point ^ (exponent / modulus) := by
      conv_lhs => rw [← Nat.mul_div_cancel' divides]
      rw [pow_mul, qParam_one_div_pow point modulus positive]
    rw [power, mul_comm]
  · rw [ite_eq_right divides, ite_eq_right divides, mul_zero]

def qSeriesDilateCoefficients (coefficients : ℕ → ℂ) (modulus index : ℕ) : ℂ :=
  if modulus ∣ index then coefficients (index / modulus) else 0

theorem qSeries_dilate_hasSum (coefficients : ℕ → ℂ) (point : ℂ)
    (modulus : ℕ) (positive : 0 < modulus) (value : ℂ)
    (series : HasSum (fun index => coefficients index * qParam 1 (modulus * point) ^ index) value) :
    HasSum (fun index => qSeriesDilateCoefficients coefficients modulus index * qParam 1 point ^ index) value := by
  have injective : Function.Injective (fun index : ℕ => modulus * index) :=
    fun _ _ equality => Nat.eq_of_mul_eq_mul_left positive equality
  apply (injective.hasSum_iff (fun index outside => ?_)).mp
  · simpa only [Function.comp_def, qSeriesDilateCoefficients, dvd_mul_right, ite_true,
      Nat.mul_div_cancel_left _ positive, qParam_one_nat_mul, pow_mul] using series
  · have not_divides : ¬modulus ∣ index := by
      rintro ⟨factor, rfl⟩
      exact outside ⟨factor, rfl⟩
    simp only [qSeriesDilateCoefficients, ite_eq_right not_divides, zero_mul]

theorem qSeries_average_hasSum (coefficients : ℕ → ℂ) (point : ℂ)
    (modulus : ℕ) (positive : 0 < modulus) (values : Fin modulus → ℂ)
    (series : ∀ residue : Fin modulus,
      HasSum (fun index => coefficients index * qParam 1 ((point + residue.val) / modulus) ^ index) (values residue)) :
    HasSum (fun index => coefficients (modulus * index) * qParam 1 point ^ index)
      ((modulus : ℂ)⁻¹ * ∑ residue : Fin modulus, values residue) := by
  classical
  have combined := hasSum_sum (s := Finset.univ) (fun residue _ => series residue)
  have terms (index : ℕ) :
      (modulus : ℂ)⁻¹ *
        (∑ residue : Fin modulus, coefficients index * qParam 1 ((point + residue.val) / modulus) ^ index) =
      if modulus ∣ index then coefficients index * qParam 1 point ^ (index / modulus) else 0 := by
    rw [← Finset.mul_sum, qParam_one_average point modulus positive]
    split_ifs with divides
    · have nonzero : (modulus : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt positive)
      field_simp
    · ring
  have sparse := (combined.mul_left (modulus : ℂ)⁻¹).congr_fun (fun index => (terms index).symm)
  have injective : Function.Injective (fun index : ℕ => modulus * index) :=
    fun _ _ equality => Nat.eq_of_mul_eq_mul_left positive equality
  have reindexed := (injective.hasSum_iff (f := fun index =>
    if modulus ∣ index then coefficients index * qParam 1 point ^ (index / modulus) else 0)
    (fun index outside => by
      have not_divides : ¬modulus ∣ index := by
        rintro ⟨factor, rfl⟩
        exact outside ⟨factor, rfl⟩
      exact ite_eq_right not_divides)).mpr sparse
  simpa only [Function.comp_def, dvd_mul_right, ite_true, Nat.mul_div_cancel_left _ positive] using reindexed

theorem qSeries_hecke_hasSum (coefficients : ℕ → ℂ) (point : ℂ)
    (modulus : ℕ) (positive : 0 < modulus) (dilatedValue : ℂ) (translatedValues : Fin modulus → ℂ)
    (dilatedSeries : HasSum (fun index => coefficients index * qParam 1 (modulus * point) ^ index) dilatedValue)
    (translatedSeries : ∀ residue : Fin modulus,
      HasSum (fun index => coefficients index * qParam 1 ((point + residue.val) / modulus) ^ index)
        (translatedValues residue)) (factor : ℂ) :
    HasSum (fun index =>
      (factor * qSeriesDilateCoefficients coefficients modulus index + coefficients (modulus * index)) *
        qParam 1 point ^ index)
      (factor * dilatedValue + (modulus : ℂ)⁻¹ * ∑ residue : Fin modulus, translatedValues residue) := by
  have dilation := (qSeries_dilate_hasSum coefficients point modulus positive dilatedValue dilatedSeries).mul_left factor
  have average := qSeries_average_hasSum coefficients point modulus positive translatedValues translatedSeries
  apply (dilation.add average).congr_fun
  intro index
  ring

theorem cuspForm_hecke_coefficient {level : Subgroup (GeneralLinearGroup (Fin 2) ℝ)} {weight : ℤ}
    [level.HasDetOne] [Fact (IsCusp OnePoint.infty level)] (form : CuspForm level weight)
    (period : (1 : ℝ) ∈ level.strictPeriods) (prime : Nat.Primes) (eigenvalue : ℂ)
    (eigenrelation : ∀ point : UpperHalfPlane,
      eigenvalue * form point =
        (prime.val : ℂ) ^ (weight - 1) *
            form (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate prime.val prime.property.pos) • point) +
          (prime.val : ℂ)⁻¹ * ∑ index : Fin prime.val,
            form (GeneralLinearGroup.map (algebraMap ℚ ℝ)
              (binaryHeckeTranslate prime.val prime.property.pos index) • point)) (index : ℕ) :
    eigenvalue * (UpperHalfPlane.qExpansion 1 form).coeff index =
      (prime.val : ℂ) ^ (weight - 1) * qSeriesDilateCoefficients
          (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) prime.val index +
        (UpperHalfPlane.qExpansion 1 form).coeff (prime.val * index) := by
  let coefficients := fun index => (UpperHalfPlane.qExpansion 1 form).coeff index
  have series (point : UpperHalfPlane) :
      HasSum (fun index =>
        ((prime.val : ℂ) ^ (weight - 1) * qSeriesDilateCoefficients coefficients prime.val index +
          coefficients (prime.val * index)) * qParam 1 point ^ index) (eigenvalue * form point) := by
    rw [eigenrelation]
    apply qSeries_hecke_hasSum coefficients point prime.val prime.property.pos
    · simpa only [binaryHeckeDilate_smul] using
        ModularForm.hasSum_qExpansion form (by norm_num : (0 : ℝ) < 1) period
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate prime.val prime.property.pos) • point)
    · intro residue
      simpa only [binaryHeckeTranslate_smul] using
        ModularForm.hasSum_qExpansion form (by norm_num : (0 : ℝ) < 1) period
          (GeneralLinearGroup.map (algebraMap ℚ ℝ)
            (binaryHeckeTranslate prime.val prime.property.pos residue) • point)
  have coefficient := ModularFormClass.qExpansion_coeff_unique
    (f := eigenvalue • form) (by norm_num : (0 : ℝ) < 1) period
    (fun point => by simpa only [_root_.smul_apply, smul_eq_mul] using series point) index
  change _ = (UpperHalfPlane.qExpansion 1 (eigenvalue • (form : UpperHalfPlane → ℂ))).coeff index at coefficient
  rw [ModularForm.qExpansion_smul (by norm_num : (0 : ℝ) < 1) period,
    PowerSeries.coeff_smul, smul_eq_mul] at coefficient
  exact coefficient.symm

theorem cuspForm_hecke_prime_coefficient {level : Subgroup (GeneralLinearGroup (Fin 2) ℝ)} {weight : ℤ}
    [level.HasDetOne] [Fact (IsCusp OnePoint.infty level)] (form : CuspForm level weight)
    (period : (1 : ℝ) ∈ level.strictPeriods) (prime : Nat.Primes) (eigenvalue : ℂ)
    (eigenrelation : ∀ point : UpperHalfPlane,
      eigenvalue * form point =
        (prime.val : ℂ) ^ (weight - 1) *
            form (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate prime.val prime.property.pos) • point) +
          (prime.val : ℂ)⁻¹ * ∑ index : Fin prime.val,
            form (GeneralLinearGroup.map (algebraMap ℚ ℝ)
              (binaryHeckeTranslate prime.val prime.property.pos index) • point))
    (normalized : (UpperHalfPlane.qExpansion 1 form).coeff 1 = 1) :
    (UpperHalfPlane.qExpansion 1 form).coeff prime.val = eigenvalue := by
  have coefficient := cuspForm_hecke_coefficient form period prime eigenvalue eigenrelation 1
  have not_divides : ¬prime.val ∣ 1 := by
    intro divides
    exact prime.property.ne_one (Nat.dvd_one.mp divides)
  simpa only [qSeriesDilateCoefficients, ite_eq_right not_divides, normalized, mul_one,
    mul_zero, zero_add] using coefficient.symm

theorem cuspForm_hecke_prime_power_recurrence {level : Subgroup (GeneralLinearGroup (Fin 2) ℝ)} {weight : ℤ}
    [level.HasDetOne] [Fact (IsCusp OnePoint.infty level)] (form : CuspForm level weight)
    (period : (1 : ℝ) ∈ level.strictPeriods) (prime : Nat.Primes) (eigenvalue : ℂ)
    (eigenrelation : ∀ point : UpperHalfPlane,
      eigenvalue * form point =
        (prime.val : ℂ) ^ (weight - 1) *
            form (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate prime.val prime.property.pos) • point) +
          (prime.val : ℂ)⁻¹ * ∑ index : Fin prime.val,
            form (GeneralLinearGroup.map (algebraMap ℚ ℝ)
              (binaryHeckeTranslate prime.val prime.property.pos index) • point)) (exponent : ℕ) :
    (UpperHalfPlane.qExpansion 1 form).coeff (prime.val ^ (exponent + 2)) =
      eigenvalue * (UpperHalfPlane.qExpansion 1 form).coeff (prime.val ^ (exponent + 1)) -
        (prime.val : ℂ) ^ (weight - 1) * (UpperHalfPlane.qExpansion 1 form).coeff (prime.val ^ exponent) := by
  have coefficient := cuspForm_hecke_coefficient form period prime eigenvalue eigenrelation
    (prime.val ^ (exponent + 1))
  have divides : prime.val ∣ prime.val ^ (exponent + 1) := dvd_pow_self _ (by omega)
  have quotient : prime.val ^ (exponent + 1) / prime.val = prime.val ^ exponent := by
    rw [pow_succ, Nat.mul_div_cancel _ prime.property.pos]
  have product : prime.val * prime.val ^ (exponent + 1) = prime.val ^ (exponent + 2) := by
    exact (pow_succ' prime.val (exponent + 1)).symm
  rw [qSeriesDilateCoefficients, ite_eq_left divides, quotient, product] at coefficient
  linear_combination -coefficient

end TernaryPeriodPolynomials.SphericalDetection.Helpers
