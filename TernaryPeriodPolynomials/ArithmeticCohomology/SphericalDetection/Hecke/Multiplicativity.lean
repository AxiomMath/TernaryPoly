module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.QExpansion
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.OuterValues
public import Mathlib.NumberTheory.LSeries.Linearity

@[expose] public section


open Matrix
open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def HasPrimeHeckeRelations (weight : ℤ) (function : UpperHalfPlane → ℂ)
    (eigenvalues : Nat.Primes → ℂ) : Prop :=
  ∀ (prime : Nat.Primes) (point : UpperHalfPlane),
    eigenvalues prime * function point =
      (prime.val : ℂ) ^ (weight - 1) *
          function (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate prime.val prime.property.pos) • point) +
        (prime.val : ℂ)⁻¹ * ∑ index : Fin prime.val,
          function (GeneralLinearGroup.map (algebraMap ℚ ℝ)
            (binaryHeckeTranslate prime.val prime.property.pos index) • point)

theorem HasPrimeHeckeRelations.smul {weight : ℤ} {function : UpperHalfPlane → ℂ}
    {eigenvalues : Nat.Primes → ℂ} (relations : HasPrimeHeckeRelations weight function eigenvalues)
    (scalar : ℂ) : HasPrimeHeckeRelations weight (scalar • function) eigenvalues := by
  intro prime point
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  linear_combination scalar * relations prime point

theorem coefficients_zero_of_prime_hecke_relations (coefficients : ℕ → ℂ)
    (trace determinant : Nat.Primes → ℂ) (constant_zero : coefficients 0 = 0)
    (first_zero : coefficients 1 = 0)
    (relations : ∀ (prime : Nat.Primes) (index : ℕ),
      trace prime * coefficients index =
        determinant prime * qSeriesDilateCoefficients coefficients prime.val index +
          coefficients (prime.val * index)) : ∀ index, coefficients index = 0 := by
  intro index
  induction index using Nat.strong_induction_on with
  | h index induction =>
    by_cases zero : index = 0
    · simpa only [zero] using constant_zero
    by_cases one : index = 1
    · simpa only [one] using first_zero
    obtain ⟨prime, prime_property, factor, factorization⟩ := Nat.exists_prime_and_dvd one
    subst index
    have factor_positive : 0 < factor := by
      by_contra not_positive
      have factor_zero : factor = 0 := by omega
      exact zero (by simp [factor_zero])
    have factor_small : factor < prime * factor := by
      have prime_large := prime_property.two_le
      nlinarith
    have correction_zero : qSeriesDilateCoefficients coefficients prime factor = 0 := by
      unfold qSeriesDilateCoefficients
      split_ifs
      · exact induction (factor / prime) ((Nat.div_le_self factor prime).trans_lt factor_small)
      · rfl
    have relation := relations ⟨prime, prime_property⟩ factor
    change trace ⟨prime, prime_property⟩ * coefficients factor =
      determinant ⟨prime, prime_property⟩ * qSeriesDilateCoefficients coefficients prime factor +
        coefficients (prime * factor) at relation
    simpa only [induction factor factor_small, correction_zero, mul_zero, zero_add] using relation.symm

theorem multiplicative_of_prime_hecke_relations (coefficients : ℕ → ℂ)
    (trace determinant : Nat.Primes → ℂ) (initial : coefficients 1 = 1)
    (relations : ∀ (prime : Nat.Primes) (index : ℕ),
      trace prime * coefficients index =
        determinant prime * qSeriesDilateCoefficients coefficients prime.val index +
          coefficients (prime.val * index)) :
    ∀ first second : ℕ, first.Coprime second →
      coefficients (first * second) = coefficients first * coefficients second := by
  intro first
  induction first using Nat.strong_induction_on with
  | h first induction =>
    intro second coprime
    by_cases zero : first = 0
    · subst first
      have second_one : second = 1 := by simpa using coprime
      simp [second_one, initial]
    by_cases one : first = 1
    · simp [one, initial]
    obtain ⟨prime, prime_property, factor, factorization⟩ := Nat.exists_prime_and_dvd one
    subst first
    have factor_positive : 0 < factor := by
      by_contra not_positive
      have factor_zero : factor = 0 := by omega
      exact zero (by simp [factor_zero])
    have factor_small : factor < prime * factor := by
      have prime_large := prime_property.two_le
      nlinarith
    have factor_coprime : factor.Coprime second := coprime.coprime_mul_left
    have prime_coprime : prime.Coprime second := coprime.coprime_mul_right
    have smaller := induction factor factor_small second factor_coprime
    have correction : qSeriesDilateCoefficients coefficients prime (factor * second) =
        qSeriesDilateCoefficients coefficients prime factor * coefficients second := by
      by_cases divides : prime ∣ factor
      · rw [qSeriesDilateCoefficients, ite_eq_left (dvd_mul_of_dvd_left divides second),
          qSeriesDilateCoefficients, ite_eq_left divides]
        have quotient : factor * second / prime = (factor / prime) * second := by
          rw [Nat.mul_comm factor second, Nat.mul_div_assoc second divides, Nat.mul_comm]
        rw [quotient]
        exact induction (factor / prime) ((Nat.div_le_self factor prime).trans_lt factor_small) second
          (factor_coprime.of_dvd_left (Nat.div_dvd_of_dvd divides))
      · have not_divides : ¬prime ∣ factor * second :=
          fun divides_product => divides (prime_coprime.dvd_mul_right.mp divides_product)
        simp only [qSeriesDilateCoefficients, ite_eq_right not_divides, ite_eq_right divides, zero_mul]
    have larger_relation := relations ⟨prime, prime_property⟩ (factor * second)
    have smaller_relation := relations ⟨prime, prime_property⟩ factor
    change trace ⟨prime, prime_property⟩ * coefficients (factor * second) =
      determinant ⟨prime, prime_property⟩ * qSeriesDilateCoefficients coefficients prime (factor * second) +
        coefficients (prime * (factor * second)) at larger_relation
    rw [smaller, correction, ← Nat.mul_assoc] at larger_relation
    linear_combination -larger_relation + coefficients second * smaller_relation

theorem cuspForm_hecke_multiplicative {level : Subgroup (GeneralLinearGroup (Fin 2) ℝ)} {weight : ℤ}
    [level.HasDetOne] [Fact (IsCusp OnePoint.infty level)] (form : CuspForm level weight)
    (period : (1 : ℝ) ∈ level.strictPeriods) (eigenvalues : Nat.Primes → ℂ)
    (eigenrelations : ∀ (prime : Nat.Primes) (point : UpperHalfPlane),
      eigenvalues prime * form point =
        (prime.val : ℂ) ^ (weight - 1) *
            form (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate prime.val prime.property.pos) • point) +
          (prime.val : ℂ)⁻¹ * ∑ index : Fin prime.val,
            form (GeneralLinearGroup.map (algebraMap ℚ ℝ)
              (binaryHeckeTranslate prime.val prime.property.pos index) • point))
    (initial : (UpperHalfPlane.qExpansion 1 form).coeff 1 = 1) :
    ∀ first second : ℕ, first.Coprime second →
      (UpperHalfPlane.qExpansion 1 form).coeff (first * second) =
        (UpperHalfPlane.qExpansion 1 form).coeff first * (UpperHalfPlane.qExpansion 1 form).coeff second :=
  multiplicative_of_prime_hecke_relations _ eigenvalues (fun prime => (prime.val : ℂ) ^ (weight - 1)) initial
    (fun prime index => cuspForm_hecke_coefficient form period prime (eigenvalues prime) (eigenrelations prime) index)

theorem levelOneCuspForm_hecke_outerLValues_ne_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (modulus : ℕ) (eigenvalues : Nat.Primes → ℂ)
    (eigenrelations : ∀ (prime : Nat.Primes) (point : UpperHalfPlane),
      eigenvalues prime * form point =
        (prime.val : ℂ) ^ (weight - 1) *
            form (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate prime.val prime.property.pos) • point) +
          (prime.val : ℂ)⁻¹ * ∑ index : Fin prime.val,
            form (GeneralLinearGroup.map (algebraMap ℚ ℝ)
              (binaryHeckeTranslate prime.val prime.property.pos index) • point))
    (initial : (UpperHalfPlane.qExpansion 1 form).coeff 1 = 1) :
    LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index)
      modulus) (((weight : ℝ) - 2 : ℝ) : ℂ) ≠ 0 ∧
    LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index)
      modulus) (((weight : ℝ) - 1 : ℝ) : ℂ) ≠ 0 := by
  have period : (1 : ℝ) ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty_mem_strictPeriods
  have nonvanishing := levelOneCuspForm_removedOuterLValues_ne_zero form modulus eigenvalues
    (fun prime => (prime.val : ℂ) ^ (weight - 1))
    (by simpa only [Subgroup.strictWidthInfty_SL2Z] using initial)
    (by simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_multiplicative form period eigenvalues eigenrelations initial)
    (fun prime => by simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_prime_coefficient form period prime (eigenvalues prime) (eigenrelations prime) initial)
    (fun prime exponent => by simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_prime_power_recurrence form period prime (eigenvalues prime) (eigenrelations prime) exponent)
  simpa only [Subgroup.strictWidthInfty_SL2Z] using nonvanishing

theorem cuspForm_hecke_first_coefficient_ne_zero {level : Subgroup (GeneralLinearGroup (Fin 2) ℝ)} {weight : ℤ}
    [level.HasDetOne] [Fact (IsCusp OnePoint.infty level)] (form : CuspForm level weight)
    (period : (1 : ℝ) ∈ level.strictPeriods) (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues) :
    (UpperHalfPlane.qExpansion 1 form).coeff 1 ≠ 0 := by
  intro first_zero
  have coefficients_zero := coefficients_zero_of_prime_hecke_relations
    (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) eigenvalues
    (fun prime => (prime.val : ℂ) ^ (weight - 1))
    (CuspFormClass.qExpansion_coeff_zero form (by norm_num : (0 : ℝ) < 1) period) first_zero
    (fun prime index => cuspForm_hecke_coefficient form period prime (eigenvalues prime) (relations prime) index)
  have expansion_zero : UpperHalfPlane.qExpansion 1 form = 0 := by
    ext index
    simpa only [map_zero] using coefficients_zero index
  have modular_zero : CuspForm.toModularFormₗ form = 0 :=
    (ModularForm.qExpansion_eq_zero_iff (by norm_num : (0 : ℝ) < 1) period
      (CuspForm.toModularFormₗ form)).mp expansion_zero
  apply nonzero
  apply DFunLike.ext
  intro point
  exact congrArg (fun modular : ModularForm level weight => modular point) modular_zero

theorem levelOneCuspForm_hecke_normalize {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues) :
    ∃ normalized : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight,
      (UpperHalfPlane.qExpansion 1 normalized).coeff 1 = 1 ∧
      HasPrimeHeckeRelations weight normalized eigenvalues ∧
      normalized = ((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ • form := by
  have period : (1 : ℝ) ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty_mem_strictPeriods
  have first_nonzero := cuspForm_hecke_first_coefficient_ne_zero form period nonzero eigenvalues relations
  refine ⟨((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ • form, ?_, relations.smul _, rfl⟩
  change (UpperHalfPlane.qExpansion 1
    (((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ • (form : UpperHalfPlane → ℂ))).coeff 1 = 1
  rw [ModularForm.qExpansion_smul (by norm_num : (0 : ℝ) < 1) period, PowerSeries.coeff_smul, smul_eq_mul,
    inv_mul_cancel₀ first_nonzero]

theorem levelOneCuspForm_hecke_outerLValues_ne_zero_of_nonzero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (modulus : ℕ) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues) :
    LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index)
      modulus) (((weight : ℝ) - 2 : ℝ) : ℂ) ≠ 0 ∧
    LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index)
      modulus) (((weight : ℝ) - 1 : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨normalized, initial, normalized_relations, normalized_eq⟩ :=
    levelOneCuspForm_hecke_normalize form nonzero eigenvalues relations
  have nonvanishing := levelOneCuspForm_hecke_outerLValues_ne_zero normalized modulus eigenvalues
    normalized_relations initial
  have period : (1 : ℝ) ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty_mem_strictPeriods
  have expansion : UpperHalfPlane.qExpansion 1 normalized =
      ((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ • UpperHalfPlane.qExpansion 1 form := by
    rw [normalized_eq]
    change UpperHalfPlane.qExpansion 1
      (((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ • (form : UpperHalfPlane → ℂ)) = _
    exact ModularForm.qExpansion_smul (by norm_num : (0 : ℝ) < 1) period _ form
  have coefficients : removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 normalized).coeff index)
      modulus = ((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ •
        removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) modulus := by
    funext index
    rw [expansion]
    simp only [removeEulerCoefficients, PowerSeries.coeff_smul, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [coefficients, LSeries_smul, LSeries_smul] at nonvanishing
  exact ⟨fun zero => nonvanishing.1 (by rw [zero, mul_zero]),
    fun zero => nonvanishing.2 (by rw [zero, mul_zero])⟩

theorem cuspLevelOneCuspForm_hecke_relations (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspScalarWeightedRealization cusp halfWeight vector 1)
      UpperHalfPlane.upperHalfPlaneSet)
    (eigenvalues : Nat.Primes → ℂ)
    (eigenvectors : ∀ prime, cuspPrimeHeckeSum cusp prime vector = eigenvalues prime • vector) :
    HasPrimeHeckeRelations (-2 * halfWeight)
      (cuspLevelOneCuspForm_of_holomorphic cusp halfWeight negative vector spherical rotation holomorphic)
      (fun prime => (prime.val : ℂ) ^ (-halfWeight - 1) * eigenvalues prime) := by
  intro prime point
  change ((prime.val : ℂ) ^ (-halfWeight - 1) * eigenvalues prime) *
      cuspScalarWeightedRealization cusp halfWeight vector 1 point =
    (prime.val : ℂ) ^ (-2 * halfWeight - 1) *
        cuspScalarWeightedRealization cusp halfWeight vector 1
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate prime.val prime.property.pos) • point : UpperHalfPlane) : ℂ) +
      (prime.val : ℂ)⁻¹ * ∑ index : Fin prime.val,
        cuspScalarWeightedRealization cusp halfWeight vector 1
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ)
            (binaryHeckeTranslate prime.val prime.property.pos index) • point : UpperHalfPlane) : ℂ)
  simp only [binaryHeckeDilate_smul, binaryHeckeTranslate_smul]
  exact cuspPrimeHeckeSum_eigen_relation cusp central_positive halfWeight vector rotation prime
    (eigenvalues prime) (eigenvectors prime) point

theorem cuspScalarHecke_outerLValues_ne_zero (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspScalarWeightedRealization cusp halfWeight vector 1)
      UpperHalfPlane.upperHalfPlaneSet)
    (nonzero : ∃ point : UpperHalfPlane, cuspScalarWeightedRealization cusp halfWeight vector 1 point ≠ 0)
    (eigenvalues : Nat.Primes → ℂ)
    (eigenvectors : ∀ prime, cuspPrimeHeckeSum cusp prime vector = eigenvalues prime • vector)
    (modulus : ℕ) :
    LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1
      (cuspScalarWeightedLinear cusp halfWeight 1 vector)).coeff index) modulus)
      (((-2 * halfWeight : ℤ) : ℂ) - 2) ≠ 0 ∧
    LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1
      (cuspScalarWeightedLinear cusp halfWeight 1 vector)).coeff index) modulus)
      (((-2 * halfWeight : ℤ) : ℂ) - 1) ≠ 0 := by
  let form := cuspLevelOneCuspForm_of_holomorphic cusp halfWeight negative vector spherical rotation holomorphic
  have form_nonzero : form ≠ 0 := by
    obtain ⟨point, nonzero_value⟩ := nonzero
    intro zero
    apply nonzero_value
    exact congrArg (fun other : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
      (-2 * halfWeight) => other point) zero
  have outer := levelOneCuspForm_hecke_outerLValues_ne_zero_of_nonzero form form_nonzero modulus
    (fun prime => (prime.val : ℂ) ^ (-halfWeight - 1) * eigenvalues prime)
    (cuspLevelOneCuspForm_hecke_relations cusp central_positive halfWeight negative vector spherical rotation
      holomorphic eigenvalues eigenvectors)
  have form_coe : (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear cusp halfWeight 1 vector := by
    funext point
    rfl
  rw [form_coe] at outer
  simpa only [Complex.ofReal_sub, Complex.ofReal_intCast, Complex.ofReal_ofNat, Complex.ofReal_one] using outer

end TernaryPeriodPolynomials.SphericalDetection.Helpers
