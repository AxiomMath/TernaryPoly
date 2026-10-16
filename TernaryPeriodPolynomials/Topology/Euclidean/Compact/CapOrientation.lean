module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapConvex
public import TernaryPeriodPolynomials.Topology.Euclidean.Local.OrientationSection
public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactClasses

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanCompactCap
open CategoryTheory HomologicalComplex
open EuclideanLocalHomology EuclideanCompactClasses

/-- The actual manifold compact fundamental class for the fixed Euclidean orientation
is exactly the fixed Euclidean compact generator, by all-point detection. -/
theorem euclidean_compactFundamentalClass (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin (n+2)))) (hK : IsCompact K) :
    RationalManifoldCompact.compactFundamentalClass n (Homeomorph.refl _)
      (euclideanOrientation n) K hK = compactGenerator n K hK := by
  apply compactGenerator_unique n K hK
  intro x hx
  exact RationalManifoldCompact.compactFundamentalClass_at_point n (Homeomorph.refl _)
    (euclideanOrientation n) K hK x hx

end TernaryPoly.EuclideanCompactCap
