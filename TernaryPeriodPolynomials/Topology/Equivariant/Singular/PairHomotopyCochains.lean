module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.PairHomotopyNull
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.PairHomotopyHom

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantSingularPairHomotopy
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (S : Set E) [Fact (InvariantSet G E S)]

/-- The actual equivariant Hom cochains of the literal relative singular chain quotient. -/
abbrev relativeHomCochains (V : Rep.{0} ℚ G) := homCochains (relativeChains G E S) V

variable {G E} {E' : TopCat.{0}} [MulAction G E'] [ContinuousConstSMul G E']
  (T : Set E') [Fact (InvariantSet G E' T)]

/-- The actual contravariant relative Hom-cochain map of a genuine equivariant map of pairs. -/
def relativeHomPullback (F : E ⟶ E') (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
    (hST : Set.MapsTo F S T) (V : Rep.{0} ℚ G) :
    relativeHomCochains G E' T V ⟶ relativeHomCochains G E S V :=
  homPullback (relativeMap S T F hF hST) V

/-- Relative Hom pullback is literal precomposition with the actual relative chain map. -/
theorem relativeHomPullback_apply (F : E ⟶ E')
    (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
    (hST : Set.MapsTo F S T) (V : Rep.{0} ℚ G) (n : ℕ) (c : (relativeChains G E' T).X n ⟶ V) :
    (relativeHomPullback S T F hF hST V).f n c = (relativeMap S T F hF hST).f n ≫ c := rfl

variable {F₀ F₁ : E ⟶ E'}
  (hF₀ : ∀ (g : G) (x : E), F₀ (g • x) = g • F₀ x)
  (hF₁ : ∀ (g : G) (x : E), F₁ (g • x) = g • F₁ x)
  (h₀ : Set.MapsTo F₀ S T) (h₁ : Set.MapsTo F₁ S T)
  (H : TopCat.Homotopy F₀ F₁) (hH : ∀ (g : G) t x, H (t,g • x) = g • H (t,x))
  (hST : ∀ t x, x ∈ S → H (t,x) ∈ T) (V : Rep.{0} ℚ G)

/-- Every genuine equivariant pair homotopy induces an actual relative Hom-cochain homotopy,
with arbitrary rational coefficient representation. -/
def relativeHomCochainHomotopy :
    Homotopy (relativeHomPullback S T F₀ hF₀ h₀ V) (relativeHomPullback S T F₁ hF₁ h₁ V) :=
  homPullbackHomotopy (relativePairHomotopy S T hF₀ hF₁ h₀ h₁ H hH hST) V

/-- The genuine relative Hom-cochain homotopy components are actual precomposition by the
relative equivariant singular prism components, with reversed degrees. -/
theorem relativeHomCochainHomotopy_component (p q : ℕ) (c : (relativeChains G E' T).X p ⟶ V) :
    (relativeHomCochainHomotopy S T hF₀ hF₁ h₀ h₁ H hH hST V).hom p q c =
      (relativePairHomotopy S T hF₀ hF₁ h₀ h₁ H hH hST).hom q p ≫ c := rfl

include H hH hST in
/-- Actual relative Hom-cohomology maps are invariant under genuine equivariant pair homotopies
in every degree, without finite-dimensionality or contractibility hypotheses. -/
theorem relativeHomCohomologyMap_eq (n : ℕ) :
    homologyMap (relativeHomPullback S T F₀ hF₀ h₀ V) n =
      homologyMap (relativeHomPullback S T F₁ hF₁ h₁ V) n :=
  (relativeHomCochainHomotopy S T hF₀ hF₁ h₀ h₁ H hH hST V).homologyMap_eq n

/-- A genuine equivariant pair collapse gives an actual relative Hom-cochain nullhomotopy. -/
def relativeHomCochainNullhomotopy (hT : ∀ x, F₁ x ∈ T) :
    Homotopy (relativeHomPullback S T F₀ hF₀ h₀ V) 0 :=
  homPullbackNullhomotopy (relativePairNullhomotopy S T hF₀ hF₁ h₀ h₁ H hH hST hT) V

include H hH hST h₁ hF₁ in
/-- A genuine equivariant pair collapse kills all induced actual relative Hom-cohomology maps. -/
theorem relativeHomCohomologyMap_zero (hT : ∀ x, F₁ x ∈ T) (n : ℕ) :
    homologyMap (relativeHomPullback S T F₀ hF₀ h₀ V) n = 0 := by
  rw [(relativeHomCochainNullhomotopy S T hF₀ hF₁ h₀ h₁ H hH hST V hT).homologyMap_eq,homologyMap_zero]

end TernaryPoly.EquivariantSingularPairHomotopy
