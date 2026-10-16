module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Naturality
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Degrees
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.RelativeAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCap
open CategoryTheory Limits AlgebraicTopology
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SingularCoverNaturality
open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  [IsCancelSMul G E] [IsCancelSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p' = p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G)

/-- The actual scalar chain map of the underlying map of base spaces. -/
abbrev scalarSpaceMap : scalarChains B ⟶ scalarChains B' :=
  ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map f

/-- The actual relative scalar chain complex. -/
abbrev relativeScalarChains := cokernel (scalarSpaceMap f)

/-- The actual relative local chain complex. -/
abbrev relativeLocalChains := cokernel (localSpaceMap F hF V p p' hp hp')

/-- The actual relative local cochain complex is the kernel of geometric restriction. -/
abbrev relativeLocalCochains := kernel (localPullback p p' F f hsquare hp hp' hF V)

include hsquare in
/-- Cap with a subspace chain vanishes after actual local relative projection. -/
theorem cap_subspace_relative_zero (a b : ℕ) (φ : VertexCochain p' hp' V a)
    (c : singularChainGroup ℚ B (a+b)) :
    (cokernel.π (localSpaceMap F hF V p p' hp hp')).f b
      (cap p' hp' V a b φ ((scalarSpaceMap f).f (a+b) c)) = 0 := by
  have hn := cap_natural p p' F f hsquare hp hp' hF V a b φ c
  change _ = cap p' hp' V a b φ ((scalarSpaceMap f).f (a+b) c) at hn
  rw [← hn]
  exact congrArg (fun g => g (cap p hp V a b (vertexPullback p p' F f hsquare hp hp' hF V a φ) c))
    (HomologicalComplex.congr_hom (cokernel.condition (localSpaceMap F hF V p p' hp hp')) b)

/-- The genuine relative cap: an absolute local cochain and relative scalar chain give a relative local chain. -/
def relativeCap (a b : ℕ) : VertexCochain p' hp' V a →ₗ[ℚ]
    (relativeScalarChains f).X (a+b) →ₗ[ℚ] (relativeLocalChains p p' F hp hp' hF V).X b :=
  RelativeAlgebra.descendBilinear (scalarSpaceMap f) (a+b)
    (ModuleCat.of ℚ (VertexCochain p' hp' V a)) _
    ((capLinear p' hp' V a b).compr₂ ((cokernel.π (localSpaceMap F hF V p p' hp hp')).f b).hom)
    (cap_subspace_relative_zero p p' F f hsquare hp hp' hF V a b)

/-- The genuine relative cap has the prescribed actual front-face/back-face formula on representatives. -/
theorem relativeCap_projection (a b : ℕ) (φ : VertexCochain p' hp' V a)
    (c : singularChainGroup ℚ B' (a+b)) :
    relativeCap p p' F f hsquare hp hp' hF V a b φ ((cokernel.π (scalarSpaceMap f)).f (a+b) c) =
      (cokernel.π (localSpaceMap F hF V p p' hp hp')).f b (cap p' hp' V a b φ c) :=
  RelativeAlgebra.descend_projection (scalarSpaceMap f) (a+b) _ _
    (cap_subspace_relative_zero p p' F f hsquare hp hp' hF V a b φ) c

omit [IsCancelSMul G E] [IsCancelSMul G E'] in
/-- An actual relative cochain restricts to zero on the subspace. -/
theorem relativeCochain_restrict_zero (a : ℕ)
    (φ : (relativeLocalCochains p p' F f hsquare hp hp' hF V).X a) :
    vertexPullback p p' F f hsquare hp hp' hF V a
      ((kernel.ι (localPullback p p' F f hsquare hp hp' hF V)).f a φ) = 0 :=
  congrArg (fun g => g φ)
    (HomologicalComplex.congr_hom (kernel.condition (localPullback p p' F f hsquare hp hp' hF V)) a)

/-- Capping a genuine relative cochain with any subspace chain is identically zero. -/
theorem relativeCochain_cap_subspace_zero (a b : ℕ)
    (φ : (relativeLocalCochains p p' F f hsquare hp hp' hF V).X a)
    (c : singularChainGroup ℚ B (a+b)) :
    cap p' hp' V a b ((kernel.ι (localPullback p p' F f hsquare hp hp' hF V)).f a φ)
      ((scalarSpaceMap f).f (a+b) c) = 0 := by
  have hn := cap_natural p p' F f hsquare hp hp' hF V a b
    ((kernel.ι (localPullback p p' F f hsquare hp hp' hF V)).f a φ) c
  change _ = cap p' hp' V a b _ ((scalarSpaceMap f).f (a+b) c) at hn
  rw [← hn, relativeCochain_restrict_zero]
  change (localSpaceMap F hF V p p' hp hp').f b (capLinear p hp V a b 0 c) = 0
  rw [map_zero]
  exact map_zero _

/-- The genuine second relative cap: relative cochains and relative scalar chains give absolute local chains. -/
def relativeCochainCap (a b : ℕ) :
    (relativeLocalCochains p p' F f hsquare hp hp' hF V).X a →ₗ[ℚ]
      (relativeScalarChains f).X (a+b) →ₗ[ℚ] VertexChain p' hp' V b :=
  RelativeAlgebra.descendBilinear (scalarSpaceMap f) (a+b) _ (ModuleCat.of ℚ (VertexChain p' hp' V b))
    ((capLinear p' hp' V a b).comp ((kernel.ι (localPullback p p' F f hsquare hp hp' hF V)).f a).hom)
    (relativeCochain_cap_subspace_zero p p' F f hsquare hp hp' hF V a b)

/-- The second relative cap also has its literal geometric formula on every representative. -/
theorem relativeCochainCap_projection (a b : ℕ)
    (φ : (relativeLocalCochains p p' F f hsquare hp hp' hF V).X a)
    (c : singularChainGroup ℚ B' (a+b)) :
    relativeCochainCap p p' F f hsquare hp hp' hF V a b φ ((cokernel.π (scalarSpaceMap f)).f (a+b) c) =
      cap p' hp' V a b ((kernel.ι (localPullback p p' F f hsquare hp hp' hF V)).f a φ) c :=
  RelativeAlgebra.descend_projection (scalarSpaceMap f) (a+b) _ _
    (relativeCochain_cap_subspace_zero p p' F f hsquare hp hp' hF V a b φ) c

end TernaryPoly.SingularLocalCap
