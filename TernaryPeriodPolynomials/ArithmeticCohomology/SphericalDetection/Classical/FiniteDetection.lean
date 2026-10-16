module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.SubmoduleEigenvector

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspClassicalFiniteAverageOperator_endpoint_injective (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (spherical_cusp : SphericalCusp cusp) {degree : ℕ} (large : 3 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ) (negative : halfWeight < 0)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (convergent : 3 < ((degree : ℂ) / 2 + 3 + cohomologicalPoint).re) :
    Function.Injective (cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative
      ((degree : ℂ) / 2 + 3 + cohomologicalPoint) convergent) := by
  apply LinearMap.ker_eq_bot.mp
  by_contra nonzero
  obtain ⟨vector, form, eigenvalues, member, vector_nonzero, form_nonzero, _form_eq, relations, eigen⟩ :=
    cuspClassicalSubmodule_exists_eigenform cusp central_positive halfWeight negative _ nonzero
      (cuspClassicalFiniteAverageOperator_ker_hecke cusp central_positive halfWeight negative _ convergent)
  apply vector_nonzero
  apply goodLineFiniteVectorIntegral_eigen_detects cusp spherical_cusp large cohomological halfWeight weight
    form form_nonzero eigenvalues relations vector.val vector.property.1 eigen
  intro real
  rw [← cuspClassicalFiniteAverage_endpoint degree cusp halfWeight convergent vector real,
    ← cuspClassicalFiniteAverageOperator_realization cusp central_positive halfWeight negative _ convergent vector,
    LinearMap.mem_ker.mp member, map_zero]
  rfl

theorem goodLineFiniteVectorIntegral_classical_detects (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (spherical_cusp : SphericalCusp cusp) {degree : ℕ} (large : 3 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (vector : cusp.smooth) (classical_vector : vector ∈ cuspClassicalVectors cusp halfWeight)
    (vanishes : ∀ real : BinaryRealGL,
      goodLineFiniteVectorIntegral degree cusp cohomologicalPoint (cuspSmoothAction cusp (atInfinity real) vector) = 0) :
    vector = 0 := by
  have negative : halfWeight < 0 := by omega
  have convergent : 3 < ((degree : ℂ) / 2 + 3 + cohomologicalPoint).re := by
    have degree_large : (3 : ℝ) < degree := by exact_mod_cast large
    norm_num [cohomologicalPoint, Complex.add_re, Complex.div_re]
    linarith
  let classicalVector : cuspClassicalVectors cusp halfWeight := ⟨vector, classical_vector⟩
  have zero : cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative
      ((degree : ℂ) / 2 + 3 + cohomologicalPoint) convergent classicalVector = 0 := by
    apply cuspClassicalRealization_injective cusp halfWeight
    rw [map_zero, cuspClassicalFiniteAverageOperator_realization]
    funext real
    exact (cuspClassicalFiniteAverage_endpoint degree cusp halfWeight convergent classicalVector real).trans (vanishes real)
  have equal : classicalVector = 0 :=
    cuspClassicalFiniteAverageOperator_endpoint_injective cusp central_positive spherical_cusp large
      cohomological halfWeight negative weight convergent (zero.trans (map_zero _).symm)
  exact congrArg Subtype.val equal

end TernaryPeriodPolynomials.SphericalDetection.Helpers
