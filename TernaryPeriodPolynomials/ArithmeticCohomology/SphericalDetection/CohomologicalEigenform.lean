module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.HeckeFaithfulness

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The supplied spherical cohomological constituent contains an actual level-one Hecke eigenform
and a simultaneous Hecke eigenvector realizing it, with both outer incomplete L-values nonzero. -/
theorem cohomological_exists_spherical_eigenform (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (odd : Odd degree)
    (cohomological : Cohomological cusp degree) (modulus : ℕ) :
    ∃ (halfWeight : ℤ)
      (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
      (eigenvector : cusp.smooth) (eigenvalues : Nat.Primes → ℂ),
      2 * halfWeight = -((degree : ℤ) + 3) ∧ 9 ≤ degree ∧
      form ≠ 0 ∧ eigenvector ≠ 0 ∧ eigenvector ∈ cuspClassicalVectors cusp halfWeight ∧
      (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear cusp halfWeight 1 eigenvector ∧
      HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues ∧
      (∀ prime : Nat.Primes, cuspPrimeHeckeSum cusp prime eigenvector =
        ((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • eigenvector) ∧
      LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index)
        modulus) (((-2 * halfWeight : ℤ) : ℂ) - 2) ≠ 0 ∧
      LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index)
        modulus) (((-2 * halfWeight : ℤ) : ℂ) - 1) ≠ 0 := by
  obtain ⟨halfWeight, vector, weight, nonzero, fixed, rotation, _, holomorphic⟩ :=
    cohomological_exists_spherical_holomorphic cusp spherical odd cohomological
  have central_positive := cohomological_centralCharacter_positive cusp cohomological
  have scalar_holomorphic := cuspScalarWeightedRealization_holomorphic cusp halfWeight vector
    fixed rotation holomorphic 1
  obtain ⟨form, eigenvector, eigenvalues, form_nonzero, classical_vector, realization, relations, lower, upper⟩ :=
    cuspScalar_exists_eigenform_outerLValues cusp central_positive halfWeight (by omega) vector
      fixed rotation scalar_holomorphic nonzero modulus
  have weight_large := levelOneCuspForm_weight_ge_twelve form form_nonzero
  have eigenvector_nonzero : eigenvector ≠ 0 := by
    intro zero
    have function_zero : (form : UpperHalfPlane → ℂ) = 0 := by rw [realization, zero, map_zero]
    exact form_nonzero (DFunLike.coe_injective function_zero)
  refine ⟨halfWeight, form, eigenvector, eigenvalues, weight, by omega, form_nonzero,
    eigenvector_nonzero, classical_vector, realization, relations, ?_, lower, upper⟩
  intro prime
  apply cuspClassicalVector_hecke_eigen cusp central_positive halfWeight eigenvector classical_vector eigenvalues
  rw [← realization]
  exact relations

end TernaryPeriodPolynomials.SphericalDetection.Helpers
