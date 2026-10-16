module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Signs
public import TernaryPeriodPolynomials.Topology.SingularHomology.BarycentricSubdivisionOperator

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCap
open CategoryTheory Limits
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open scoped Classical Simplicial

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep.{0} ℚ G)

/-- The coefficient of the cap simplex: front-face evaluation, followed by actual
transport from its vertex zero through the original first vertex to the cut vertex. -/
def capCoefficient (a b : ℕ) (σ : SingularSimplex B (a+b)) :
    VertexCochain p hp V a →ₗ[ℚ]
      FiberCoefficient p hp V (atVertex (backSimplex B a b σ)) :=
  (coefficientTransportLinear p hp (simplexPullPath (backMap a b) σ).symm).comp
    ((coefficientTransportLinear p hp (simplexPullPath (frontMap a b) σ)).comp
      (LinearMap.proj (frontSimplex B a b σ)))

/-- The actual cap of a cochain with a simplex is the dependent singleton on its back face. -/
def capSimplex (a b : ℕ) (σ : SingularSimplex B (a+b)) :
    VertexCochain p hp V a →ₗ[ℚ] VertexChain p hp V b :=
  (DFinsupp.lsingle (backSimplex B a b σ)).comp (capCoefficient p hp V a b σ)

/-- The defining front-evaluation/back-output formula, with explicit transport paths. -/
theorem capSimplex_apply (a b : ℕ) (σ : SingularSimplex B (a+b))
    (φ : VertexCochain p hp V a) :
    capSimplex p hp V a b σ φ =
      DFinsupp.single (backSimplex B a b σ)
        (coefficientTransportLinear p hp (simplexPullPath (backMap a b) σ).symm
          (coefficientTransportLinear p hp (simplexPullPath (frontMap a b) σ)
            (φ (frontSimplex B a b σ)))) := rfl

/-- Extending the actual simplex cap linearly to the existing scalar singular chain module. -/
def cap (a b : ℕ) (φ : VertexCochain p hp V a) :
    singularChainGroup ℚ B (a+b) →ₗ[ℚ] VertexChain p hp V b :=
  (Sigma.desc fun σ : SingularSimplex B (a+b) =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ (capSimplex p hp V a b σ φ))).hom

/-- Scalar singular simplex generators have the literal geometric cap value. -/
theorem cap_generator (a b : ℕ) (φ : VertexCochain p hp V a)
    (σ : SingularSimplex B (a+b)) :
    cap p hp V a b φ (chainGenerator ℚ B (a+b) σ) = capSimplex p hp V a b σ φ := by
  have h := congrArg (fun f : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ (VertexChain p hp V b) =>
    f.hom (1 : ℚ)) (Sigma.ι_comp_desc (fun σ : SingularSimplex B (a+b) =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ (capSimplex p hp V a b σ φ))) σ)
  exact h.trans (one_smul ℚ _)

/-- Equality of linear maps out of actual scalar singular chains is detected on simplices. -/
theorem scalarChain_ext {X : TopCat.{0}} {n : ℕ} {W : Type} [AddCommGroup W] [Module ℚ W]
    {f g : singularChainGroup ℚ X n →ₗ[ℚ] W}
    (h : ∀ σ, f (chainGenerator ℚ X n σ) = g (chainGenerator ℚ X n σ)) : f = g := by
  have he : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply Sigma.hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    exact h σ
  exact congrArg ModuleCat.Hom.hom he

/-- Cap is linear in its local cochain as well as its scalar chain. -/
def capLinear (a b : ℕ) : VertexCochain p hp V a →ₗ[ℚ]
    (singularChainGroup ℚ B (a+b) →ₗ[ℚ] VertexChain p hp V b) where
  toFun := cap p hp V a b
  map_add' φ ψ := by
    apply scalarChain_ext
    intro σ
    simp only [LinearMap.add_apply, cap_generator, map_add]
  map_smul' r φ := by
    apply scalarChain_ext
    intro σ
    simp only [LinearMap.smul_apply, cap_generator, map_smul, RingHom.id_apply]

/-- Each simplex contributes only its actual back face to the finite support. -/
theorem capSimplex_support (a b : ℕ) (σ : SingularSimplex B (a+b))
    (φ : VertexCochain p hp V a) :
    (capSimplex p hp V a b σ φ).support ⊆ {backSimplex B a b σ} :=
  DFinsupp.support_single_subset

/-- On a finite scalar singular chain, cap is the finite sum of its transported back faces. -/
theorem cap_finset_sum {I : Type} (a b : ℕ) (φ : VertexCochain p hp V a)
    (s : Finset I) (σ : I → SingularSimplex B (a+b)) (r : I → ℚ) :
    cap p hp V a b φ (∑ i ∈ s, r i • chainGenerator ℚ B (a+b) (σ i)) =
      ∑ i ∈ s, r i • capSimplex p hp V a b (σ i) φ := by
  simp only [map_sum, map_smul, cap_generator]

variable [ContinuousConstSMul G E] [IsCancelSMul G E]

/-- At every actual simplex lift, cap is the tensor class of the back lifted face with
coefficient equal to evaluation of the cochain on the front lifted face. -/
theorem capSimplex_lift (a b : ℕ) (φ : VertexCochain p hp V a)
    {σ : SingularSimplex B (a+b)} (τ : Lifts p σ) :
    (degreeEquiv p hp V b).symm (capSimplex p hp V a b σ φ) =
      generator G E V b (backSimplex E a b τ.val)
        (vertexToFunction p hp φ (frontSimplex E a b τ.val)) := by
  rcases τ with ⟨τ,hτ⟩
  cases hτ
  erw [capSimplex_apply, degreeEquiv_symm_single_lift p hp V b
    (pullLift p (backMap a b) ⟨τ,rfl⟩), backwardTransport_lift]
  apply congrArg (generator G E V b (backSimplex E a b τ))
  exact (coefficient_simplexTransport p hp (frontMap a b) τ
    (φ (frontSimplex B a b (projection p (a+b) τ)))).trans
      (vertexToFunction_lift p hp φ
        (⟨pullSimplex (frontMap a b) τ, projection_pullSimplex p (frontMap a b) τ⟩ :
          Lifts p (frontSimplex B a b (projection p (a+b) τ)))).symm

end TernaryPoly.SingularLocalCap
