module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Transfer

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence SingularLocalHomology
open SymmetricSpaceBoundaryFull SymmetricSpaceBoundaryDuality SymmetricSpaceBoundaryManifold
open SymmetricSpaceBoundaryOrientation OrdinaryTopBoundaryComparison

/-- The genuine arithmetic H3 image of the entire full-level boundary, using the actual restriction and cap maps. -/
def actualFullBoundaryImage (n : ℕ) (e : ℤ) :
    Submodule ℚ (groupHomology (restrictedCoefficients n e) 3) :=
  LinearMap.range (fullBoundaryClassToGroup n e).hom

/-- Actual full-level entire-boundary arithmetic classes have pairwise distinguished apartment coefficients. -/
theorem actualFullBoundaryImage_pairwise (n : ℕ) (e : ℤ)
    (x : groupHomology (restrictedCoefficients n e) 3) (hx : x ∈ actualFullBoundaryImage n e) :
    coefficientPairwise n (groupApartmentEvaluation (restrictedCoefficients n e) x) := by
  obtain ⟨y, rfl⟩ := hx
  exact fullBoundaryClassToGroup_pairwise n e y

/-- An actual boundary H3 class in the precise full-level component has pairwise ordinary image. -/
theorem boundary_image_fullLevel_pairwise (n : ℕ) (e : ℤ)
    (b : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3)
    (hb : (boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).inv b ∈ fullLevelComponent n e 1) :
    coefficientPairwise n (groupApartmentEvaluation (restrictedCoefficients n e)
      (boundaryToGroup (restrictedCoefficients n e) 3 b)) := by
  have h := fullLevelBoundary_pairwise n e
    ⟨(boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).inv b, hb⟩
  have hi := congrArg (fun f => f b)
    (boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).inv_hom_id
  change (boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).hom
    ((boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).inv b) = b at hi
  rw [hi] at h
  exact h

end TernaryPoly.OrdinaryBoundaryActualEvaluation
