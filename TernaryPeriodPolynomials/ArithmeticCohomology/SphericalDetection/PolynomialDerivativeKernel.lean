module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PolynomialAntiderivative
public import Mathlib.Algebra.MvPolynomial.Supported

@[expose] public section


open GeneralEisenstein MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem pderiv_zero_notMem_vars {σ : Type*} (coordinate : σ) (polynomial : MvPolynomial σ ℂ)
    (derivative_zero : pderiv coordinate polynomial = 0) : coordinate ∉ polynomial.vars := by
  classical
  intro member
  obtain ⟨exponent, support, positive⟩ := (mem_vars_iff_mem_support coordinate).mp member
  have exponent_positive : 1 ≤ exponent coordinate :=
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp positive)
  have single_le : Finsupp.single coordinate 1 ≤ exponent := Finsupp.single_le_iff.mpr exponent_positive
  have coefficient_zero := congrArg (·.coeff (exponent - Finsupp.single coordinate 1)) derivative_zero
  rw [coeff_pderiv, tsub_add_cancel_of_le single_le, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at coefficient_zero
  have multiplier_nonzero : (((exponent - Finsupp.single coordinate 1 : σ →₀ ℕ) coordinate : ℕ) : ℂ) + 1 ≠ 0 := by
    have numeric : (exponent - Finsupp.single coordinate 1 : σ →₀ ℕ) coordinate + 1 ≠ 0 := Nat.succ_ne_zero _
    exact_mod_cast numeric
  exact (mem_support_iff.mp support) ((mul_eq_zero.mp coefficient_zero).resolve_right multiplier_nonzero)

theorem pderiv_zero_iff_notMem_vars {σ : Type*} (coordinate : σ) (polynomial : MvPolynomial σ ℂ) :
    pderiv coordinate polynomial = 0 ↔ coordinate ∉ polynomial.vars :=
  ⟨pderiv_zero_notMem_vars coordinate polynomial, pderiv_eq_zero_of_notMem_vars⟩

def binaryPolynomialLift : Binary.Poly →ₐ[ℂ] Poly := rename Fin.castSucc

theorem binaryPolynomialLift_injective : Function.Injective binaryPolynomialLift :=
  rename_injective Fin.castSucc (Fin.castSucc_injective 2)

theorem binaryPolynomialLift_pderiv_third (polynomial : Binary.Poly) :
    pderiv (2 : Fin 3) (binaryPolynomialLift polynomial) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro member
  obtain ⟨index, _, equality⟩ := mem_vars_rename Fin.castSucc polynomial member
  exact Fin.castSucc_ne_last index equality

theorem pderiv_third_zero_exists_binary (polynomial : Poly)
    (derivative_zero : pderiv (2 : Fin 3) polynomial = 0) :
    ∃ binary : Binary.Poly, binaryPolynomialLift binary = polynomial := by
  apply exists_rename_eq_of_vars_subset_range polynomial Fin.castSucc (Fin.castSucc_injective 2)
  intro index member
  fin_cases index
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact (pderiv_zero_notMem_vars 2 polynomial derivative_zero member).elim

def binaryHomogeneousLift (degree : ℕ) : Binary.HomogeneousPoly degree →ₗ[ℂ] HomogeneousPoly degree where
  toFun polynomial := ⟨binaryPolynomialLift polynomial.val,
    polynomial.property.rename_isHomogeneous⟩
  map_add' _ _ := Subtype.ext (map_add binaryPolynomialLift _ _)
  map_smul' _ _ := Subtype.ext (map_smul binaryPolynomialLift _ _)

theorem binaryHomogeneousLift_injective (degree : ℕ) : Function.Injective (binaryHomogeneousLift degree) := by
  intro first second equal
  apply Subtype.ext
  exact binaryPolynomialLift_injective (congrArg Subtype.val equal)

theorem homogeneous_pderiv_third_zero_exists_binary {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (derivative_zero : pderiv (2 : Fin 3) polynomial.val = 0) :
    ∃ binary : Binary.HomogeneousPoly degree, binaryHomogeneousLift degree binary = polynomial := by
  obtain ⟨binary, equality⟩ := pderiv_third_zero_exists_binary polynomial.val derivative_zero
  have homogeneous : binary.IsHomogeneous degree := by
    apply (IsHomogeneous.rename_isHomogeneous_iff (Fin.castSucc_injective 2)).mp
    change (binaryPolynomialLift binary).IsHomogeneous degree
    rw [equality]
    exact polynomial.property
  exact ⟨⟨binary, homogeneous⟩, Subtype.ext equality⟩

theorem homogeneous_of_X_mul {σ : Type*} (coordinate : σ) (polynomial : MvPolynomial σ ℂ)
    {degree : ℕ} (homogeneous : (X coordinate * polynomial).IsHomogeneous degree) :
    polynomial.IsHomogeneous (degree - 1) := by
  classical
  intro exponent nonzero
  have product_nonzero : (X coordinate * polynomial).coeff (Finsupp.single coordinate 1 + exponent) ≠ 0 := by
    rw [coeff_X_mul]
    exact nonzero
  have degree_eq := homogeneous product_nonzero
  have degree_eq' : 1 + exponent.degree = degree := by
    have result : (Finsupp.single coordinate 1 + exponent).degree = degree := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using degree_eq
    simpa only [map_add, Finsupp.degree_single] using result
  have result : exponent.degree = degree - 1 := by omega
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using result

end TernaryPeriodPolynomials.SphericalDetection.Helpers
