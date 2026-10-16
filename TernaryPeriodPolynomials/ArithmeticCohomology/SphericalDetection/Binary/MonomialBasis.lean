module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SmoothCoordinates
public import Mathlib.Algebra.MvPolynomial.Supported

@[expose] public section


open GeneralEisenstein MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

abbrev BinaryHomogeneousExponent (degree : ℕ) :=
  {exponent : Fin 2 →₀ ℕ // exponent.degree = degree}

theorem binary_homogeneous_restrictSupport (degree : ℕ) :
    restrictSupport ℂ {exponent : Fin 2 →₀ ℕ | exponent.degree = degree} =
      homogeneousSubmodule (Fin 2) ℂ degree := by
  ext polynomial
  rw [mem_restrictSupport_iff]
  change (↑polynomial.support ⊆ {exponent : Fin 2 →₀ ℕ | exponent.degree = degree}) ↔
    polynomial.IsHomogeneous degree
  simp only [Set.subset_def, Finset.mem_coe, mem_support_iff, Set.mem_ofPred_eq,
    IsHomogeneous, IsWeightedHomogeneous, Finsupp.degree_eq_weight_one]
  exact ⟨fun homogeneous _ nonzero => homogeneous _ nonzero,
    fun homogeneous _ nonzero => homogeneous nonzero⟩

def binaryMonomialBasis (degree : ℕ) :
    Module.Basis (BinaryHomogeneousExponent degree) ℂ (Binary.HomogeneousPoly degree) :=
  (basisRestrictSupport ℂ {exponent : Fin 2 →₀ ℕ | exponent.degree = degree}).map
    (LinearEquiv.ofEq _ _ (binary_homogeneous_restrictSupport degree))

instance binaryHomogeneousExponent_fintype (degree : ℕ) : Fintype (BinaryHomogeneousExponent degree) := by
  let : FiniteDimensional ℂ (Binary.HomogeneousPoly degree) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 2) ℂ degree)
  exact FiniteDimensional.fintypeBasisIndex (binaryMonomialBasis degree)

theorem binaryHomogeneousExponent_sum {degree : ℕ} (exponent : BinaryHomogeneousExponent degree) :
    exponent.val 0 + exponent.val 1 = degree := by
  simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using exponent.property

theorem binaryMonomialBasis_coe (degree : ℕ) (exponent : BinaryHomogeneousExponent degree) :
    (binaryMonomialBasis degree exponent).val = monomial exponent.val (1 : ℂ) := by
  have equal : binaryMonomialBasis degree exponent =
      ⟨monomial exponent.val (1 : ℂ), isHomogeneous_monomial 1 exponent.property⟩ := by
    apply Module.Basis.apply_eq_iff.mpr
    ext other
    change (monomial exponent.val (1 : ℂ)).coeff other.val = (Finsupp.single exponent (1 : ℂ)) other
    simp [coeff_monomial, Finsupp.single_apply, Subtype.ext_iff]
  exact congrArg Subtype.val equal

end TernaryPeriodPolynomials.SphericalDetection.Helpers
