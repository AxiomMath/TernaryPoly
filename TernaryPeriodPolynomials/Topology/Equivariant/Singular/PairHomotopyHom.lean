module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallCochains
public import Mathlib.Algebra.Homology.Homotopy

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantSingularPairHomotopy
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall

variable {G : Type} [Group G] {C D : ChainComplex (Rep.{0} ℚ G) ℕ}

/-- The actual contravariant Hom-cochain functor carries every equivariant chain homotopy to
a genuine cochain homotopy, with arbitrary rational coefficient representation. -/
def homPullbackHomotopy {f g : C ⟶ D} (H : Homotopy f g) (V : Rep.{0} ℚ G) :
    Homotopy (homPullback f V) (homPullback g V) :=
  (((linearYoneda ℚ (Rep ℚ G)).obj V).rightOp.mapHomotopy H).unop

/-- Each induced Hom-cochain homotopy component is literal precomposition by the reversed-degree
component of the original equivariant chain homotopy. -/
theorem homPullbackHomotopy_component {f g : C ⟶ D} (H : Homotopy f g) (V : Rep.{0} ℚ G)
    (p q : ℕ) (c : D.X p ⟶ V) :
    (homPullbackHomotopy H V).hom p q c = H.hom q p ≫ c := rfl

/-- Homotopic actual equivariant chain maps induce equal maps on actual Hom cohomology. -/
theorem homPullback_cohomology_eq {f g : C ⟶ D} (H : Homotopy f g) (V : Rep.{0} ℚ G) (n : ℕ) :
    homologyMap (homPullback f V) n = homologyMap (homPullback g V) n :=
  (homPullbackHomotopy H V).homologyMap_eq n

/-- The actual Hom-cochain pullback of the zero chain map is the zero cochain map. -/
theorem homPullback_zero (V : Rep.{0} ℚ G) : homPullback (0 : C ⟶ D) V = 0 := by
  ext n c
  change (0 : C.X n ⟶ D.X n) ≫ c = 0
  exact zero_comp

/-- An actual equivariant chain nullhomotopy gives an actual Hom-cochain nullhomotopy. -/
def homPullbackNullhomotopy {f : C ⟶ D} (H : Homotopy f 0) (V : Rep.{0} ℚ G) :
    Homotopy (homPullback f V) 0 :=
  (homPullbackHomotopy H V).trans (Homotopy.ofEq (homPullback_zero V))

/-- An actual equivariant chain nullhomotopy kills every induced Hom-cohomology map. -/
theorem homPullback_cohomology_zero {f : C ⟶ D} (H : Homotopy f 0) (V : Rep.{0} ℚ G) (n : ℕ) :
    homologyMap (homPullback f V) n = 0 := by
  rw [(homPullbackNullhomotopy H V).homologyMap_eq,homologyMap_zero]

end TernaryPoly.EquivariantSingularPairHomotopy
