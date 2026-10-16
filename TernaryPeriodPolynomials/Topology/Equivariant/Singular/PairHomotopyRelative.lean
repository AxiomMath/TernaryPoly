module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.PairHomotopySubspace
public import TernaryPeriodPolynomials.GroupCohomology.Relative.ChainHomotopyMap

@[expose] public section

noncomputable section
namespace TernaryPoly.EquivariantSingularPairHomotopy
open CategoryTheory Limits HomologicalComplex
open EquivariantSingularResolution EquivariantSingularSmall SingularCoverNaturality
open CoveringBoundaryDeformation.Chains

variable {G : Type} [Group G] {E E' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G E'] [ContinuousConstSMul G E']
  (S : Set E) (T : Set E') [Fact (InvariantSet G E S)] [Fact (InvariantSet G E' T)]
  {F₀ F₁ : E ⟶ E'}
  (hF₀ : ∀ (g : G) (x : E), F₀ (g • x) = g • F₀ x)
  (hF₁ : ∀ (g : G) (x : E), F₁ (g • x) = g • F₁ x)
  (h₀ : Set.MapsTo F₀ S T) (h₁ : Set.MapsTo F₁ S T)
  (H : TopCat.Homotopy F₀ F₁)
  (hH : ∀ (g : G) t x, H (t,g • x) = g • H (t,x))
  (hST : ∀ t x, x ∈ S → H (t,x) ∈ T)

/-- A genuine equivariant homotopy of pairs induces an actual homotopy of the literal
relative equivariant singular chain maps, without a contractibility assumption. -/
def relativePairHomotopy :
    Homotopy (relativeMap S T F₀ hF₀ h₀) (relativeMap S T F₁ hF₁ h₁) :=
  RelativeChainHomotopy.mapHomotopyOfCompatible (inclusion G E S) (inclusion G E' T)
    (chainHomotopy H hH hF₀ hF₁) (subspaceChainHomotopy S T hF₀ hF₁ h₀ h₁ H hH hST)
    (inclusion_naturality S T F₀ hF₀ h₀) (inclusion_naturality S T F₁ hF₁ h₁)
    (subspace_chainHomotopy_natural S T hF₀ hF₁ h₀ h₁ H hH hST)

/-- Every relative homotopy component is exactly the actual ambient equivariant prism component
followed by the quotient projection, factored through the actual source quotient. -/
theorem relativePairHomotopy_component (p q : ℕ) :
    (cokernel.π (inclusion G E S)).f p ≫
        (relativePairHomotopy S T hF₀ hF₁ h₀ h₁ H hH hST).hom p q =
      (chainHomotopy H hH hF₀ hF₁).hom p q ≫ (cokernel.π (inclusion G E' T)).f q :=
  RelativeChainHomotopy.projection_degreeDesc _ _ _ _

include H hH hST in
/-- Genuinely equivariantly homotopic pair maps have equal actual relative homology maps. -/
theorem relativeHomologyMap_eq (n : ℕ) :
    homologyMap (relativeMap S T F₀ hF₀ h₀) n = homologyMap (relativeMap S T F₁ hF₁ h₁) n :=
  (relativePairHomotopy S T hF₀ hF₁ h₀ h₁ H hH hST).homologyMap_eq n

end TernaryPoly.EquivariantSingularPairHomotopy
