module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Euler.Series
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem complex_quadratic_roots (trace determinant : ℂ) :
    ∃ first second : ℂ, first + second = trace ∧ first * second = determinant := by
  obtain ⟨radical, square⟩ := IsAlgClosed.exists_pow_nat_eq
    (trace ^ 2 - 4 * determinant) (by decide : 0 < 2)
  refine ⟨(trace + radical) / 2, (trace - radical) / 2, ?_, ?_⟩
  · ring
  · linear_combination -(1 / 4 : ℂ) * square

theorem cuspForm_LSeries_eq {weight : ℤ}
    {level : Subgroup (GeneralLinearGroup (Fin 2) ℝ)} [level.IsArithmetic]
    (weight_positive : 0 < weight) (form : CuspForm level weight)
    (argument : ℂ) (argument_bound : (weight : ℝ) / 2 + 1 < argument.re) :
    LSeries (fun index =>
      (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff index) argument =
        (level.strictWidthInfty : ℂ) ^ (-argument) *
          ModularForm.L weight_positive form argument := by
  have zero_coefficient :
      (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero form level.strictWidthInfty_pos
      level.strictWidthInfty_mem_strictPeriods
  have term_eq (index : ℕ) :
      LSeries.term (fun index =>
        (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff index)
        argument index =
      (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff index /
        (index : ℂ) ^ argument := by
    by_cases zero_index : index = 0
    · simp [zero_index, zero_coefficient]
    · rw [LSeries.term_def, ite_eq_right zero_index]
  have series := (CuspForm.hasSum_L weight_positive form argument_bound).congr_fun term_eq
  exact series.tsum_eq

theorem cuspForm_LSeries_norm_summable {weight : ℤ}
    {level : Subgroup (GeneralLinearGroup (Fin 2) ℝ)} [level.IsArithmetic]
    (weight_positive : 0 < weight) (form : CuspForm level weight)
    (argument : ℂ) (argument_bound : (weight : ℝ) / 2 + 1 < argument.re) :
    Summable (fun index => ‖LSeries.term (fun index =>
      (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff index)
      argument index‖) := by
  have zero_coefficient :
      (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero form level.strictWidthInfty_pos
      level.strictWidthInfty_mem_strictPeriods
  apply summable_norm_iff.mpr
  apply (CuspForm.hasSum_L weight_positive form argument_bound).summable.congr
  intro index
  by_cases zero_index : index = 0
  · simp [zero_index, zero_coefficient]
  · rw [LSeries.term_def, ite_eq_right zero_index]

theorem cuspForm_eulerRoots {weight : ℤ}
    {level : Subgroup (GeneralLinearGroup (Fin 2) ℝ)} [level.IsArithmetic]
    (form : CuspForm level weight) (trace determinant : Nat.Primes → ℂ)
    (initial : (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff 1 = 1)
    (first : ∀ place : Nat.Primes,
      (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff place.val = trace place)
    (recurrence : ∀ (place : Nat.Primes) (exponent : ℕ),
      (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
          (place.val ^ (exponent + 2)) =
        trace place * (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
          (place.val ^ (exponent + 1)) -
        determinant place * (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
          (place.val ^ exponent)) :
    ∃ first_root second_root : Nat.Primes → ℂ,
      (∀ place, first_root place + second_root place = trace place) ∧
      (∀ place, first_root place * second_root place = determinant place) ∧
      (∀ place, ‖first_root place‖ ≤ (place.val : ℝ) ^ ((weight : ℝ) / 2)) ∧
      (∀ place, ‖second_root place‖ ≤ (place.val : ℝ) ^ ((weight : ℝ) / 2)) := by
  classical
  choose first_root second_root root_sum root_product using
    fun place => complex_quadratic_roots (trace place) (determinant place)
  obtain ⟨constant, _, coefficient_bound⟩ := cuspForm_primePowerCoefficient_bound form
  have root_bound (root : Nat.Primes → ℂ)
      (equation : ∀ place, root place ^ 2 - trace place * root place + determinant place = 0)
      (place : Nat.Primes) : ‖root place‖ ≤ (place.val : ℝ) ^ ((weight : ℝ) / 2) :=
    primePowerRecurrence_root_norm_le
      (fun exponent => (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
        (place.val ^ exponent)) (trace place) (determinant place) (root place)
      place (weight : ℝ) constant (by simpa using initial) (by simpa using first place)
      (recurrence place) (equation place) (coefficient_bound place)
  refine ⟨first_root, second_root, root_sum, root_product, root_bound first_root ?_,
    root_bound second_root ?_⟩
  · intro place
    rw [← root_sum place, ← root_product place]
    ring
  · intro place
    rw [← root_sum place, ← root_product place]
    ring

theorem cuspForm_LSeries_ne_zero_of_recurrence {weight : ℤ}
    {level : Subgroup (GeneralLinearGroup (Fin 2) ℝ)} [level.IsArithmetic]
    (weight_positive : 0 < weight) (form : CuspForm level weight)
    (argument : ℝ) (argument_bound : (weight : ℝ) / 2 + 1 < argument)
    (trace determinant : Nat.Primes → ℂ)
    (initial : (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff 1 = 1)
    (multiplicative : ∀ first_index second_index : ℕ,
      first_index.Coprime second_index →
        (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
            (first_index * second_index) =
          (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff first_index *
            (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff second_index)
    (first : ∀ place : Nat.Primes,
      (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff place.val = trace place)
    (recurrence : ∀ (place : Nat.Primes) (exponent : ℕ),
      (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
          (place.val ^ (exponent + 2)) =
        trace place * (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
          (place.val ^ (exponent + 1)) -
        determinant place * (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
          (place.val ^ exponent)) :
    LSeries (fun index =>
      (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff index)
      (argument : ℂ) ≠ 0 := by
  classical
  obtain ⟨first_root, second_root, root_sum, root_product, first_bound, second_bound⟩ :=
    cuspForm_eulerRoots form trace determinant initial first recurrence
  have product_nonzero := outerEulerProduct_ne_zero first_root second_root
    (weight : ℝ) argument first_bound second_bound argument_bound
  have product_eq := quadraticEulerSeries_eq_product
    (fun index => (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff index)
    (argument : ℂ) trace determinant first_root second_root initial multiplicative first
    recurrence root_sum root_product
    (cuspForm_LSeries_norm_summable weight_positive form argument (by simpa using argument_bound))
  have scaled_eq (root : Nat.Primes → ℂ) (place : Nat.Primes) :
      scaledEulerRoot root argument place = root place * (place.val : ℂ) ^ (-(argument : ℂ)) := by
    unfold scaledEulerRoot
    rw [← Complex.ofReal_neg]
    have real_power := Complex.ofReal_cpow
      (x := (place.val : ℝ)) (by exact_mod_cast place.property.pos.le) (-argument)
    exact congrArg (fun value : ℂ => root place * value)
      (by simpa only [Complex.ofReal_natCast] using real_power)
  simp_rw [scaled_eq] at product_nonzero
  rw [product_eq]
  exact product_nonzero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
