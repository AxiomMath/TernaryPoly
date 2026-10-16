module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.HomogeneousLastDivision
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.RadicalProjectedValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realUpperBinaryValue (degree : ℕ) (element : RealPlaneRadical) :
    Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] HomogeneousPoly degree :=
  (homogeneousLastDivide degree).comp
    ((LinearMap.id - (realUpperRadicalRep (degree + 1)).ρ element).comp (binaryHomogeneousLift (degree + 1)))

theorem realUpperBinaryValue_multiply (degree : ℕ) (element : RealPlaneRadical)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    homogeneousLastMultiply degree (realUpperBinaryValue degree element polynomial) =
      binaryHomogeneousLift (degree + 1) polynomial -
        (realUpperRadicalRep (degree + 1)).ρ element (binaryHomogeneousLift (degree + 1) polynomial) := by
  apply homogeneousLastMultiply_divide
  change binaryHomogeneousRestrict (degree + 1)
    (binaryHomogeneousLift (degree + 1) polynomial -
      (realUpperRadicalRep (degree + 1)).ρ element (binaryHomogeneousLift (degree + 1) polynomial)) = 0
  rw [map_sub, binaryHomogeneousRestrict_realUpper, sub_self]

theorem realUpperBinaryValue_mul (degree : ℕ) (first second : RealPlaneRadical)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    realUpperBinaryValue degree (first * second) polynomial =
      (realUpperRadicalRep degree).ρ first (realUpperBinaryValue degree second polynomial) +
        realUpperBinaryValue degree first polynomial := by
  apply homogeneousLastMultiply_injective degree
  rw [map_add, homogeneousLastMultiply_realUpper, realUpperBinaryValue_multiply,
    realUpperBinaryValue_multiply, realUpperBinaryValue_multiply, map_sub, map_mul, Module.End.mul_apply]
  abel

def realUpperBinarySection (degree : ℕ) :
    Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] groupCohomology.cocycles₁ (realUpperRadicalRep degree) where
  toFun polynomial := ⟨fun element => realUpperBinaryValue degree element polynomial,
    (groupCohomology.mem_cocycles₁_iff _).mpr (fun first second => realUpperBinaryValue_mul degree first second polynomial)⟩
  map_add' first second := by
    apply groupCohomology.cocycles₁_ext
    intro element
    exact map_add (realUpperBinaryValue degree element) first second
  map_smul' scalar polynomial := by
    apply groupCohomology.cocycles₁_ext
    intro element
    exact map_smul (realUpperBinaryValue degree element) scalar polynomial

theorem realUpperBinarySection_apply (degree : ℕ) (polynomial : Binary.HomogeneousPoly (degree + 1))
    (element : RealPlaneRadical) :
    (realUpperBinarySection degree polynomial element).val =
      (binaryPolynomialLift polynomial.val -
        action (-1) (planeUnipotent (element.toAdd 0 : ℂ) (element.toAdd 1 : ℂ))
          (binaryPolynomialLift polynomial.val)).divMonomial (Finsupp.single 2 1) := by
  change (binaryPolynomialLift polynomial.val -
      (realCoefficientComponent (degree + 1) trivialCharacter
        (planeUnipotent (element.toAdd 0) (element.toAdd 1)) (binaryHomogeneousLift (degree + 1) polynomial)).val).divMonomial
          (Finsupp.single 2 1) = _
  rw [realCoefficientComponent_trivial, map_planeUnipotent]
  rfl

theorem binaryRestrict_lastDivide (degree : ℕ) (polynomial : HomogeneousPoly (degree + 1))
    (zero : binaryHomogeneousRestrict (degree + 1) polynomial = 0) :
    binaryPolynomialRestrict (homogeneousLastDivide degree polynomial).val =
      binaryPolynomialRestrict (pderiv 2 polynomial.val) := by
  have equality := congrArg Subtype.val (homogeneousLastMultiply_divide degree polynomial zero)
  change X 2 * (homogeneousLastDivide degree polynomial).val = polynomial.val at equality
  rw [← equality, pderiv_mul, pderiv_X_self, one_mul, map_add, map_mul, binaryPolynomialRestrict_X]
  simp

end TernaryPeriodPolynomials.SphericalDetection.Helpers
