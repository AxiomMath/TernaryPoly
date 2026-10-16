module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.Main

@[expose] public section


/-!
# The positive geometric orientation of `ℝ⁵` and the staircase product cell

Formalized by Claude Sonnet 5.5.

Paper: "we orient the flat and the averaged standard top-cell generator so that their local intersection
number is `+1`".

The library reads local homology of `ℝⁿ` in a rational generator fixed through a choice (`zeroReducedHomologyIso`).  A GEOMETRIC
orientation is instead fixed by a positive reference cell: `posOrientation5` is the Euclidean orientation rescaled by `d₅`, the
degree of the positive staircase product cell `stair` (tetrahedron times triangle) against the library's generator, so that
by definition the cell has degree `1` (`stair_generator_at`: the class of `stair` restricted to ANY point of its support
`Nset` is the geometric generator at that point; compare `Orient.Calibration.posOrientation` in dimension three, B2).
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.RationalManifoldCompact TernaryPoly.EuclideanCompactClasses
  TernaryPoly.RationalLocalOrientation TernaryPoly.EuclideanOrientationScalar
open TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Geometric

/-- **The positive geometric orientation of `ℝ⁵`**: the library's Euclidean orientation rescaled by `d₅`, the degree of the
positive staircase product cell (tetrahedron × triangle). -/
def posOrientation5 : Orientation (3 + 2) (EuclideanSpace ℝ (Fin (3 + 2))) where
  generator x := d5 • localGenerator 3 x
  nonzero x := smul_ne_zero Normalized.d5_ne_zero' (localGenerator_ne_zero 3 x)
  locallyRepresented x := by
    obtain ⟨U, K, hx, hUK, c, hc⟩ := localGenerator_locallyRepresented 3 x
    refine ⟨U, K, hx, hUK, d5 • c, fun y hy hK => ?_⟩
    rw [map_smul, hc y hy hK]

/-- **The positive staircase product cell represents the positive geometric generator at every point of `Nset`.** -/
theorem stair_generator_at (y : EuclideanSpace ℝ (Fin 5)) (hy : y ∈ (Nset : Set (EuclideanSpace ℝ (Fin (3 + 2))))) :
    homologyMap (supportPointMap (Nset : Set (EuclideanSpace ℝ (Fin (3 + 2)))) y hy) (3 + 2)
        (relCls stair (relCls_mem_of_sup stair_boundary_mem)) = posOrientation5.generator y := by
  rw [relCls_stair_eq, map_smul]
  change d5 • homologyMap (supportPointMap (Nset : Set (EuclideanSpace ℝ (Fin (3 + 2)))) y hy) (3 + 2)
    (compactGenerator 3 Nset isCompact_Nset) = d5 • localGenerator 3 y
  exact congrArg (d5 • ·) (compactGenerator_at_point 3 Nset isCompact_Nset y hy)

end TernaryPeriodPolynomials.Argument.Lemma33.Geometric
