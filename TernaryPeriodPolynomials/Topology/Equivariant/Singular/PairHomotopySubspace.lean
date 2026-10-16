module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.PairHomotopyMaps
public import TernaryPeriodPolynomials.Topology.Covering.BoundaryDeformationChains
public import TernaryPeriodPolynomials.Topology.Singular.ChainHomotopyNaturalitySubspace

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

/-- The literal topological homotopy restricted to the actual invariant subspaces. -/
def subspaceTopHomotopy : TopCat.Homotopy (pairSubspaceMap S T F₀ h₀) (pairSubspaceMap S T F₁ h₁) :=
  RationalRelativeSingular.subspaceHomotopy S T h₀ h₁ H hST

omit [ContinuousConstSMul G E] [ContinuousConstSMul G E'] in
include hH in
/-- Genuine equivariance is preserved by the literal restriction of the homotopy. -/
theorem subspaceTopHomotopy_equivariant (g : G) (t) (x : S) :
    subspaceTopHomotopy S T h₀ h₁ H hST (t,g • x) = g • subspaceTopHomotopy S T h₀ h₁ H hST (t,x) := by
  apply Subtype.ext
  exact hH g t x.val

/-- The actual equivariant singular chain homotopy of the actual restricted topological homotopy. -/
def subspaceChainHomotopy :
    Homotopy (chainMap (pairSubspaceMap S T F₀ h₀) (pairSubspaceMap_equivariant S T F₀ hF₀ h₀))
      (chainMap (pairSubspaceMap S T F₁ h₁) (pairSubspaceMap_equivariant S T F₁ hF₁ h₁)) :=
  chainHomotopy (subspaceTopHomotopy S T h₀ h₁ H hST)
    (subspaceTopHomotopy_equivariant S T h₀ h₁ H hH hST)
    (pairSubspaceMap_equivariant S T F₀ hF₀ h₀) (pairSubspaceMap_equivariant S T F₁ hF₁ h₁)

/-- Each actual equivariant prism component commutes with the literal invariant-subspace inclusions. -/
theorem subspace_chainHomotopy_natural (p q : ℕ) :
    (inclusion G E S).f p ≫ (chainHomotopy H hH hF₀ hF₁).hom p q =
      (subspaceChainHomotopy S T hF₀ hF₁ h₀ h₁ H hH hST).hom p q ≫ (inclusion G E' T).f q := by
  ext c
  exact congrArg (fun m => m.hom c)
    (SingularChainHomotopyNaturality.subspace_singularChainHomotopy_natural S T h₀ h₁ H hST p q)

end TernaryPoly.EquivariantSingularPairHomotopy
