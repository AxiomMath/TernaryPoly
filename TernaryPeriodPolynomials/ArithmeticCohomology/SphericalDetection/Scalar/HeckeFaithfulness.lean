module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.ImageEigenform
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.Holomorphic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspClassicalScalarMap_injective (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) :
    Function.Injective ((cuspScalarWeightedLinear cusp halfWeight 1).comp
      (cuspClassicalVectors cusp halfWeight).subtype) := by
  intro first second equality
  apply Subtype.ext
  apply sub_eq_zero.mp
  by_contra nonzero
  let difference : cuspClassicalVectors cusp halfWeight := first - second
  have vector_nonzero : difference.val ≠ 0 := nonzero
  obtain ⟨point, scalar_nonzero⟩ := cuspScalarWeightedRealization_identity_nonzero cusp central_positive
    halfWeight difference.val difference.property.1 difference.property.2.1 vector_nonzero
  have function_zero : cuspScalarWeightedLinear cusp halfWeight 1 difference.val = 0 := by
    change cuspScalarWeightedLinear cusp halfWeight 1 (first.val - second.val) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr equality
  exact scalar_nonzero (congrFun function_zero point)

theorem scalarPrimeHecke_of_relations (halfWeight : ℤ) (function : UpperHalfPlane → ℂ)
    (eigenvalues : Nat.Primes → ℂ) (relations : HasPrimeHeckeRelations (-2 * halfWeight) function eigenvalues)
    (prime : Nat.Primes) :
    scalarPrimeHecke halfWeight prime function =
      ((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • function := by
  funext point
  have scaled := congrArg (fun value : ℂ => (prime.val : ℂ) ^ (halfWeight + 1) * value)
    (relations prime point)
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    ← zpow_add₀ (Nat.cast_ne_zero.mpr prime.property.ne_zero), ← _root_.zpow_neg_one,
    ← zpow_add₀ (Nat.cast_ne_zero.mpr prime.property.ne_zero)] at scaled
  have first_exponent : halfWeight + 1 + (-2 * halfWeight - 1) = -halfWeight := by ring
  have second_exponent : halfWeight + 1 + (-1 : ℤ) = halfWeight := by ring
  rw [first_exponent, second_exponent] at scaled
  exact scaled.symm

theorem cuspClassicalVector_hecke_eigen (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.smooth) (classical_vector : vector ∈ cuspClassicalVectors cusp halfWeight)
    (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations (-2 * halfWeight)
      (cuspScalarWeightedLinear cusp halfWeight 1 vector) eigenvalues) (prime : Nat.Primes) :
    cuspPrimeHeckeSum cusp prime vector = ((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • vector := by
  let first : cuspClassicalVectors cusp halfWeight :=
    ⟨cuspPrimeHeckeSum cusp prime vector, cuspPrimeHeckeSum_classical cusp central_positive halfWeight prime vector classical_vector⟩
  let second : cuspClassicalVectors cusp halfWeight :=
    ((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • ⟨vector, classical_vector⟩
  have equality : first = second := by
    apply cuspClassicalScalarMap_injective cusp central_positive halfWeight
    change cuspScalarWeightedLinear cusp halfWeight 1 (cuspPrimeHeckeSum cusp prime vector) =
      cuspScalarWeightedLinear cusp halfWeight 1 (((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • vector)
    rw [map_smul, cuspPrimeHeckeSum_scalar_intertwines cusp central_positive halfWeight prime vector classical_vector.2.1]
    exact scalarPrimeHecke_of_relations halfWeight _ eigenvalues relations prime
  exact congrArg Subtype.val equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
