module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.Singular

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSingular
open CategoryTheory Limits HomologicalComplex AlgebraicTopology ContractibleSingularHomology
open RationalSingularAugmentation
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The genuine singular chain isomorphism of a homeomorphism. -/
def chainHomeomorphIso (e : X ≃ₜ Y) : chains X ≅ chains Y :=
  ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of.{0} ℚ ℚ)).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e)

/-- The actual restricted map of a pair. -/
def subspaceMap (f : C(X,Y)) (S : Set X) (T : Set Y) (h : Set.MapsTo f S T) : C(S,T) :=
  ⟨fun x => ⟨f x,h x.property⟩, f.continuous.comp continuous_subtype_val |>.subtype_mk _⟩

/-- Literal pair maps commute with subspace inclusion at chain level. -/
theorem inclusion_naturality (f : C(X,Y)) (S : Set X) (T : Set Y) (h : Set.MapsTo f S T) :
    inclusion S ≫ chainMap f = chainMap (subspaceMap f S T h) ≫ inclusion T := by
  change chainMap _ ≫ chainMap _ = chainMap _ ≫ chainMap _
  rw [← chainMap_comp, ← chainMap_comp]
  rfl

/-- The actual relative map of a continuous map of pairs. -/
def relativeMap (f : C(X,Y)) (S : Set X) (T : Set Y) (h : Set.MapsTo f S T) :
    relativeChains S ⟶ relativeChains T :=
  cokernel.map (inclusion S) (inclusion T) (chainMap (subspaceMap f S T h))
    (chainMap f) (inclusion_naturality f S T h)

/-- A homeomorphism of pairs induces the genuine relative chain isomorphism. -/
def relativeHomeomorphIso (e : X ≃ₜ Y) (S : Set X) (T : Set Y)
    (h : ∀ x, x ∈ S ↔ e x ∈ T) : relativeChains S ≅ relativeChains T :=
  cokernel.mapIso (inclusion S) (inclusion T)
    (chainHomeomorphIso (e.subtype h)) (chainHomeomorphIso e) (by
      change inclusion S ≫ chainMap e.toHomotopyEquiv.toFun =
        chainMap (e.subtype h).toHomotopyEquiv.toFun ≫ inclusion T
      exact inclusion_naturality e.toHomotopyEquiv.toFun S T (fun x hx => (h x).mp hx))

/-- The induced homeomorphism on actual relative homology. -/
def relativeHomeomorphHomologyIso (e : X ≃ₜ Y) (S : Set X) (T : Set Y)
    (h : ∀ x, x ∈ S ↔ e x ∈ T) (k : ℕ) :
    (relativeChains S).homology k ≅ (relativeChains T).homology k :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).mapIso
    (relativeHomeomorphIso e S T h)

end TernaryPoly.RationalRelativeSingular
