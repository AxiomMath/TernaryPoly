module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallSubspace
public import TernaryPeriodPolynomials.Topology.Rational.Relative.Homotopy

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantSingularPairHomotopy
open CategoryTheory Limits HomologicalComplex
open EquivariantSingularResolution EquivariantSingularSmall SingularCoverNaturality

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (S : Set E) [Fact (InvariantSet G E S)]

/-- The literal singular chain map of the inclusion of an invariant subspace. -/
def inclusion : equivariantChains G (TopCat.of S) ⟶ equivariantChains G E :=
  chainMap (SphereOddDegree.sInclusion S) (fun _ _ => rfl)

/-- The actual equivariant relative singular complex, as the literal inclusion cokernel. -/
abbrev relativeChains := cokernel (inclusion G E S)

variable {G E} {E' : TopCat.{0}} [MulAction G E'] [ContinuousConstSMul G E']
  (T : Set E') [Fact (InvariantSet G E' T)] (F : E ⟶ E')
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (hST : Set.MapsTo F S T)

/-- The actual continuous map on invariant subspaces, with no choice of replacement map. -/
def pairSubspaceMap : TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom (RationalRelativeSingular.subspaceMap F.hom S T hST)

omit [ContinuousConstSMul G E] [ContinuousConstSMul G E'] in
include hF in
/-- Equivariance restricts to the canonical invariant-subspace actions. -/
theorem pairSubspaceMap_equivariant (g : G) (x : S) :
    pairSubspaceMap S T F hST (g • x) = g • pairSubspaceMap S T F hST x := by
  apply Subtype.ext
  exact hF g x.val

/-- Literal equivariant pair maps commute with the actual subspace inclusions. -/
theorem inclusion_naturality :
    inclusion G E S ≫ chainMap F hF =
      chainMap (pairSubspaceMap S T F hST) (pairSubspaceMap_equivariant S T F hF hST) ≫ inclusion G E' T := by
  ext n c
  exact congrArg (fun m => (m.f n).hom c)
    (RationalRelativeSingular.inclusion_naturality F.hom S T hST)

/-- The literal equivariant singular map on the actual relative chain cokernels. -/
def relativeMap : relativeChains G E S ⟶ relativeChains G E' T :=
  cokernel.map (inclusion G E S) (inclusion G E' T)
    (chainMap (pairSubspaceMap S T F hST) (pairSubspaceMap_equivariant S T F hF hST))
    (chainMap F hF) (inclusion_naturality S T F hF hST)

/-- Relative chain maps retain the actual ambient singular map after quotient projection. -/
theorem relativeMap_projection :
    cokernel.π (inclusion G E S) ≫ relativeMap S T F hF hST =
      chainMap F hF ≫ cokernel.π (inclusion G E' T) := by
  simp only [relativeMap,cokernel.map,cokernel.π_desc]

end TernaryPoly.EquivariantSingularPairHomotopy
