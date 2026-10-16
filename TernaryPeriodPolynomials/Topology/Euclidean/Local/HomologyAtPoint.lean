module

public import TernaryPeriodPolynomials.Topology.Euclidean.Local.Homology
public import TernaryPeriodPolynomials.Topology.Rational.Relative.Naturality

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanLocalHomology
open CategoryTheory Limits HomologicalComplex RationalRelativeSingular RationalSphere

/-- Actual Euclidean local chains at an arbitrary specified point. -/
abbrev localChainsAt (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :=
  relativeChains ({x}ᶜ : Set (EuclideanSpace ℝ (Fin d)))

/-- Translation to the origin identifies the literal local chain complexes. -/
def translateLocalIso (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    localChainsAt d x ≅ localChains d :=
  relativeHomeomorphIso (Homeomorph.subRight x) {x}ᶜ {0}ᶜ (by
    intro y
    simp [Homeomorph.subRight_apply, sub_eq_zero])

/-- Actual local homology at any Euclidean point identifies with the origin calculation. -/
def translateLocalHomologyIso (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    (localChainsAt d x).homology k ≅ (localChains d).homology k :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).mapIso (translateLocalIso d x)

/-- Every point of Euclidean (n+2)-space has the genuine one-dimensional local top homology. -/
def localTopAtIso (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+2))) :
    (localChainsAt (n+2) x).homology (n+2) ≅ ModuleCat.of ℚ ℚ :=
  translateLocalHomologyIso (n+2) x (n+2) ≪≫ localTopIso n

/-- All the other actual local homology groups vanish at every point. -/
theorem localAt_isZero_of_ne (n k : ℕ) (x : EuclideanSpace ℝ (Fin (n+2))) (hk : k ≠ n+2) :
    IsZero ((localChainsAt (n+2) x).homology k) :=
  (local_isZero_of_ne n k hk).of_iso (translateLocalHomologyIso (n+2) x k)

end TernaryPoly.EuclideanLocalHomology
