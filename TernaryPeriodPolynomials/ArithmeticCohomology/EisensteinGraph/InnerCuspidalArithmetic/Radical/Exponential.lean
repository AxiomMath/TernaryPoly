module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Radical.Invariants
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Nilpotent.Exp

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem radicalShearFamily_derivative (index : Fin 2) (polynomial : Poly) :
    Polynomial.derivative (radicalShearFamily index polynomial) =
      radicalShearFamily index (-X index.succ * pderiv 0 polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [radicalShearFamily]
  | add first second firstIdentity secondIdentity =>
    rw [map_add, Polynomial.derivative_add, firstIdentity, secondIdentity,
      map_add, mul_add, map_add]
  | mul_X polynomial coordinate identity =>
    rw [map_mul, Polynomial.derivative_mul, identity]
    by_cases zero : coordinate = 0
    · subst coordinate
      simp [radicalShearFamily, pderiv_X]
      ring
    · simp [radicalShearFamily, zero, pderiv_X_of_ne zero]
      ring

theorem radicalShearFamily_coefficient_recurrence (index : Fin 2) (polynomial : Poly)
    (order : ℕ) :
    (radicalShearFamily index polynomial).coeff (order + 1) =
      ((order + 1 : ℕ) : ℂ)⁻¹ •
        (radicalShearFamily index (-X index.succ * pderiv 0 polynomial)).coeff order := by
  have identity := congrArg (fun family : Polynomial Poly => family.coeff order)
    (radicalShearFamily_derivative index polynomial)
  rw [Polynomial.coeff_derivative] at identity
  have nonzero : ((order + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero order
  have scalarIdentity : (radicalShearFamily index polynomial).coeff (order + 1) *
      C ((order + 1 : ℕ) : ℂ) =
        (radicalShearFamily index (-X index.succ * pderiv 0 polynomial)).coeff order := by
    simpa using identity
  rw [← scalarIdentity, Algebra.smul_def, MvPolynomial.algebraMap_eq,
    ← mul_assoc, mul_comm (C (((order + 1 : ℕ) : ℂ)⁻¹)), mul_assoc,
    ← map_mul, inv_mul_cancel₀ nonzero, map_one, mul_one]

theorem pderiv_iterate_zero_of_coeff (polynomial : Poly) (order : ℕ)
    (vanishing : ∀ exponent : Fin 3 →₀ ℕ, order ≤ exponent 0 → polynomial.coeff exponent = 0) :
    (fun value : Poly => pderiv 0 value)^[order] polynomial = 0 := by
  induction order generalizing polynomial with
  | zero =>
    apply MvPolynomial.ext
    intro exponent
    exact vanishing exponent (Nat.zero_le _)
  | succ order induction =>
    rw [Function.iterate_succ_apply]
    apply induction
    intro exponent large
    rw [coeff_pderiv, vanishing]
    · simp
    · simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      omega

theorem homogeneous_pderiv_iterate_zero (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    (fun value : Poly => pderiv 0 value)^[degree + 1] polynomial.val = 0 := by
  apply pderiv_iterate_zero_of_coeff
  intro exponent large
  apply MvPolynomial.IsHomogeneous.coeff_eq_zero polynomial.property
  have degreeIdentity := Finsupp.degree_eq_sum exponent
  simp only [Fin.sum_univ_three] at degreeIdentity
  omega

theorem pderiv_mul_binary_X (index : Fin 2) (polynomial : Poly) :
    pderiv 0 (X index.succ * polynomial) = X index.succ * pderiv 0 polynomial := by
  simp [pderiv_X_of_ne (Fin.succ_ne_zero index)]

theorem radicalInfinitesimal_pow (degree : ℕ) (positive : 0 < degree) (index : Fin 2)
    (order : ℕ) (polynomial : HomogeneousPoly degree) :
    ((radicalInfinitesimal degree positive index ^ order) polynomial).val =
      X index.succ ^ order * (fun value : Poly => pderiv 0 value)^[order] polynomial.val := by
  induction order with
  | zero => simp
  | succ order induction =>
    rw [pow_succ', Module.End.mul_apply]
    change X index.succ * pderiv 0
      ((radicalInfinitesimal degree positive index ^ order) polynomial).val = _
    rw [induction, pderiv_mul, pderiv_pow, pderiv_X_of_ne (Fin.succ_ne_zero index)]
    simp only [mul_zero, zero_mul, zero_add]
    rw [Function.iterate_succ_apply', pow_succ]
    ring

theorem radicalInfinitesimal_nilpotent (degree : ℕ) (positive : 0 < degree) (index : Fin 2) :
    IsNilpotent (radicalInfinitesimal degree positive index) := by
  refine ⟨degree + 1, ?_⟩
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  rw [radicalInfinitesimal_pow, homogeneous_pderiv_iterate_zero, mul_zero]
  rfl

theorem radicalInfinitesimal_pow_zero (degree : ℕ) (positive : 0 < degree) (index : Fin 2) :
    radicalInfinitesimal degree positive index ^ (degree + 1) = 0 := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  rw [radicalInfinitesimal_pow, homogeneous_pderiv_iterate_zero, mul_zero]
  rfl

theorem radicalShearFamily_homogeneous_coefficient (degree : ℕ) (positive : 0 < degree)
    (index : Fin 2) (order : ℕ) (polynomial : HomogeneousPoly degree) :
    (radicalShearFamily index polynomial.val).coeff order =
      ((order.factorial : ℕ) : ℂ)⁻¹ •
        (((-(radicalInfinitesimal degree positive index)) ^ order) polynomial).val := by
  induction order generalizing polynomial with
  | zero => simp [radicalShearFamily_coeff_zero]
  | succ order induction =>
    rw [radicalShearFamily_coefficient_recurrence]
    have negativeValue : ((-(radicalInfinitesimal degree positive index)) polynomial).val =
        -X index.succ * pderiv 0 polynomial.val := by
      rw [LinearMap.neg_apply]
      change -(X index.succ * pderiv 0 polynomial.val) = _
      exact (neg_mul (X index.succ : Poly) (pderiv 0 polynomial.val)).symm
    rw [← negativeValue]
    rw [induction ((-(radicalInfinitesimal degree positive index)) polynomial), smul_smul]
    have composition :
        ((-(radicalInfinitesimal degree positive index)) ^ order)
            ((-(radicalInfinitesimal degree positive index)) polynomial) =
          (((-(radicalInfinitesimal degree positive index)) ^ (order + 1)) polynomial) := by
      rw [pow_succ, Module.End.mul_apply]
    rw [composition]
    rw [Nat.factorial_succ, Nat.cast_mul, _root_.mul_inv_rev]
    congr 1
    ring

theorem radicalShearFamily_natDegree (degree : ℕ) (positive : 0 < degree)
    (index : Fin 2) (polynomial : HomogeneousPoly degree) :
    (radicalShearFamily index polynomial.val).natDegree ≤ degree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro order large
  rw [radicalShearFamily_homogeneous_coefficient degree positive index order polynomial]
  have power : (-(radicalInfinitesimal degree positive index)) ^ (degree + 1) = 0 := by
    have identity := _root_.neg_pow (radicalInfinitesimal degree positive index) (degree + 1)
    simpa only [radicalInfinitesimal_pow_zero, mul_zero] using identity
  have higher : (-(radicalInfinitesimal degree positive index)) ^ order = 0 :=
    pow_eq_zero_of_le (by omega) power
  rw [higher]
  simp

theorem radicalShearFamily_eval_one_exponential (degree : ℕ) (positive : 0 < degree)
    (index : Fin 2) (polynomial : HomogeneousPoly degree) :
    Polynomial.eval 1 (radicalShearFamily index polynomial.val) =
      (IsNilpotent.exp (-(radicalInfinitesimal degree positive index)) polynomial).val := by
  have power : (-(radicalInfinitesimal degree positive index)) ^ (degree + 1) = 0 := by
    have identity := _root_.neg_pow (radicalInfinitesimal degree positive index) (degree + 1)
    simpa only [radicalInfinitesimal_pow_zero, mul_zero] using identity
  rw [Polynomial.as_sum_range_C_mul_X_pow'
    (radicalShearFamily index polynomial.val)
    (Nat.lt_succ_of_le (radicalShearFamily_natDegree degree positive index polynomial)),
    Polynomial.eval_finsetSum, IsNilpotent.exp_eq_sum power, LinearMap.sum_apply]
  change (∑ order ∈ Finset.range (degree + 1),
      Polynomial.eval 1 (Polynomial.C ((radicalShearFamily index polynomial.val).coeff order) *
        Polynomial.X ^ order)) = _
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, one_pow, mul_one]
  have sumCoefficients : (∑ order ∈ Finset.range (degree + 1),
      ((order.factorial : ℕ) : ℂ)⁻¹ •
        (((-(radicalInfinitesimal degree positive index)) ^ order) polynomial).val) =
      (∑ order ∈ Finset.range (degree + 1),
        (order.factorial : ℚ)⁻¹ •
          ((-(radicalInfinitesimal degree positive index)) ^ order) polynomial).val := by
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    apply Finset.sum_congr rfl
    intro order _
    rw [← Rat.cast_smul_eq_qsmul ℂ]
    simp
  simp only [radicalShearFamily_homogeneous_coefficient degree positive index,
    LinearMap.smul_apply]
  exact sumCoefficients

theorem radicalShear_action_exponential (degree : ℕ) (positive : 0 < degree)
    (index : Fin 2) (polynomial : HomogeneousPoly degree) :
    bind₁ (fun coordinate : Fin 3 =>
      if coordinate = 0 then X 0 - X index.succ else X coordinate) polynomial.val =
      (IsNilpotent.exp (-(radicalInfinitesimal degree positive index)) polynomial).val := by
  have evaluation := radicalShearFamily_eval index 1 polynomial.val
  simp only [map_one, one_mul] at evaluation
  rw [← evaluation]
  exact radicalShearFamily_eval_one_exponential degree positive index polynomial

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
