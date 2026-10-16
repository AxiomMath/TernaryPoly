module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.PairHomotopyRelative

@[expose] public section

noncomputable section
namespace TernaryPoly.EquivariantSingularPairHomotopy
open CategoryTheory Limits HomologicalComplex AlgebraicTopology
open EquivariantSingularResolution EquivariantSingularSmall SingularCoverNaturality

variable {G : Type} [Group G] {E E' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G E'] [ContinuousConstSMul G E']
  (S : Set E) (T : Set E') [Fact (InvariantSet G E S)] [Fact (InvariantSet G E' T)]

/-- A genuinely equivariant continuous map landing wholly in the target invariant subspace
induces the zero map of the literal relative chain cokernels. -/
theorem relativeMap_eq_zero_of_range (F : E ⟶ E')
    (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
    (hST : Set.MapsTo F S T) (hT : ∀ x, F x ∈ T) : relativeMap S T F hF hST = 0 := by
  let K : E ⟶ TopCat.of T := TopCat.ofHom ⟨fun x => ⟨F x,hT x⟩,F.hom.continuous.subtype_mk _⟩
  have hK (g : G) (x : E) : K (g • x) = g • K x := Subtype.ext (hF g x)
  have hFactor : chainMap F hF = chainMap K hK ≫ inclusion G E' T := by
    ext n c
    have he : K ≫ SphereOddDegree.sInclusion T = F := rfl
    have ht := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map_comp
      K (SphereOddDegree.sInclusion T)
    rw [he] at ht
    exact congrArg (fun m => (m.f n).hom c) ht
  apply (cancel_epi (cokernel.π (inclusion G E S))).mp
  rw [relativeMap_projection,comp_zero,hFactor,Category.assoc,cokernel.condition,comp_zero]

/-- An actual equivariant pair homotopy ending inside the target subspace gives a genuine
relative chain nullhomotopy, in all degrees. -/
def relativePairNullhomotopy {F₀ F₁ : E ⟶ E'}
    (hF₀ : ∀ (g : G) (x : E), F₀ (g • x) = g • F₀ x)
    (hF₁ : ∀ (g : G) (x : E), F₁ (g • x) = g • F₁ x)
    (h₀ : Set.MapsTo F₀ S T) (h₁ : Set.MapsTo F₁ S T)
    (H : TopCat.Homotopy F₀ F₁) (hH : ∀ (g : G) t x, H (t,g • x) = g • H (t,x))
    (hST : ∀ t x, x ∈ S → H (t,x) ∈ T) (hT : ∀ x, F₁ x ∈ T) :
    Homotopy (relativeMap S T F₀ hF₀ h₀) 0 :=
  (relativePairHomotopy S T hF₀ hF₁ h₀ h₁ H hH hST).trans
    (Homotopy.ofEq (relativeMap_eq_zero_of_range S T F₁ hF₁ h₁ hT))

/-- The induced actual equivariant relative homology map of such a pair collapse vanishes. -/
theorem relativeHomologyMap_zero {F₀ F₁ : E ⟶ E'}
    (hF₀ : ∀ (g : G) (x : E), F₀ (g • x) = g • F₀ x)
    (hF₁ : ∀ (g : G) (x : E), F₁ (g • x) = g • F₁ x)
    (h₀ : Set.MapsTo F₀ S T) (h₁ : Set.MapsTo F₁ S T)
    (H : TopCat.Homotopy F₀ F₁) (hH : ∀ (g : G) t x, H (t,g • x) = g • H (t,x))
    (hST : ∀ t x, x ∈ S → H (t,x) ∈ T) (hT : ∀ x, F₁ x ∈ T) (n : ℕ) :
    homologyMap (relativeMap S T F₀ hF₀ h₀) n = 0 := by
  rw [(relativePairNullhomotopy S T hF₀ hF₁ h₀ h₁ H hH hST hT).homologyMap_eq,homologyMap_zero]

end TernaryPoly.EquivariantSingularPairHomotopy
