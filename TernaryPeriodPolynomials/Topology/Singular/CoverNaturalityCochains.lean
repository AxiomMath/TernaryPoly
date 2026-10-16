module

public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityChains
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityTransport

@[expose] public section


noncomputable section
open CategoryTheory HomologicalComplex
open scoped Simplicial
namespace TernaryPoly.SingularCoverNaturality
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient
open EquivariantSingularResolution EquivariantSingularCohomology

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p'=p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x)=g • F x)

include hsquare in
/-- Postcomposition of actual singular simplices preserves the commuting square. -/
theorem projection_square (n : ℕ) (τ : SingularSimplex E n) :
    projection p' n (projection F n τ)=projection f n (projection p n τ) := by
  apply (TopCat.toSSetObjEquiv B' (.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro z
  exact congrArg (fun m : E ⟶ B' => m (TopCat.toSSetObjEquiv E (.op ⦋n⦌) τ z)) hsquare

/-- A commuting square maps each literal lift to a literal lift of the image simplex. -/
def liftMap {n : ℕ} {σ : SingularSimplex B n} (τ : Lifts p σ) :
    Lifts p' (projection f n σ) :=
  ⟨projection F n τ.val,(projection_square p p' F f hsquare n τ.val).trans
    (congrArg (projection f n) τ.property)⟩

omit [ContinuousConstSMul G E] [ContinuousConstSMul G E'] in
/-- The actual lift map agrees at the vertex with the actual fiber map. -/
theorem liftMap_vertex {n : ℕ} {σ : SingularSimplex B n} (τ : Lifts p σ) :
    liftVertexEquiv p' hp' (projection f n σ) (liftMap p p' F f hsquare τ)=
      fiberMap p p' F f hsquare (liftVertexEquiv p hp σ τ) := rfl

/-- Geometric cochain pullback uses the actual image simplex and actual map on its vertex fiber. -/
def vertexPullback (V : Rep ℚ G) (n : ℕ) :
    VertexCochain p' hp' V n →ₗ[ℚ] VertexCochain p hp V n where
  toFun c σ := coefficientPullback p p' F f hsquare hp hp' hF V (atVertex σ)
    (c (projection f n σ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of actual Hom pullback is postcomposition of its singular generator. -/
theorem cochainPullback_evaluate (V : Rep ℚ G) (n : ℕ) (c : chainRep G E' n ⟶ V)
    (τ : SingularSimplex E n) :
    cochainFunctionEquiv G E V n ((cochainPullback F hF V).f n c) τ=
      cochainFunctionEquiv G E' V n c (projection F n τ) := by
  exact congrArg (fun m => c.hom (m.hom 1)) (generator_map F n τ)

/-- The actual vertex-fiber comparison commutes with literal space pullback. -/
theorem homVertexEquiv_pullback (V : Rep ℚ G) (n : ℕ) (c : chainRep G E' n ⟶ V) :
    homVertexEquiv p hp V n ((cochainPullback F hF V).f n c)=
      vertexPullback p p' F f hsquare hp hp' hF V n (homVertexEquiv p' hp' V n c) := by
  funext σ
  apply Subtype.ext
  funext e
  obtain ⟨τ,rfl⟩ := (liftVertexEquiv p hp σ).surjective e
  change (homVertexEquiv p hp V n ((cochainPullback F hF V).f n c) σ).val
      (liftVertexEquiv p hp σ τ)=
    (homVertexEquiv p' hp' V n c (projection f n σ)).val
      (fiberMap p p' F f hsquare (liftVertexEquiv p hp σ τ))
  exact (homVertexEquiv_lift p hp V n ((cochainPullback F hF V).f n c) τ).trans
    ((cochainPullback_evaluate F hF V n c τ.val).trans
      (homVertexEquiv_lift p' hp' V n c (liftMap p p' F f hsquare τ)).symm)

/-- Pullback preserves the literal alternating transported-face differential. -/
theorem differential_pullback (V : Rep ℚ G) (n : ℕ) (c : VertexCochain p' hp' V n) :
    vertexPullback p p' F f hsquare hp hp' hF V (n+1) (differential p' hp' V n c)=
      differential p hp V n (vertexPullback p p' F f hsquare hp hp' hF V n c) := by
  obtain ⟨c,rfl⟩ := (homVertexEquiv p' hp' V n).surjective c
  exact (congrArg (vertexPullback p p' F f hsquare hp hp' hF V (n+1))
    (homVertexEquiv_d p' hp' V n c)).trans
    ((homVertexEquiv_pullback p p' F f hsquare hp hp' hF V (n+1)
      ((cochains G E' V).d n (n+1) c)).symm.trans
      ((congrArg (homVertexEquiv p hp V (n+1))
        (congrArg (fun m => m c) ((cochainPullback F hF V).comm n (n+1))).symm).trans
        ((homVertexEquiv_d p hp V n ((cochainPullback F hF V).f n c)).symm.trans
          (congrArg (differential p hp V n)
            (homVertexEquiv_pullback p p' F f hsquare hp hp' hF V n c)))))

/-- The actual map on geometric local-system singular cochain complexes. -/
def localPullback (V : Rep ℚ G) : localCochains p' hp' V ⟶ localCochains p hp V where
  f n := ModuleCat.ofHom (vertexPullback p p' F f hsquare hp hp' hF V n)
  comm' i j hij := by
    obtain rfl : j=i+1 := hij.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    simp only [localCochains,CochainComplex.of_d]
    convert (differential_pullback p p' F f hsquare hp hp' hF V i c).symm using 1

/-- The genuine singular/local-system cochain isomorphisms commute with cover maps. -/
theorem cochainIso_pullback (V : Rep ℚ G) :
    cochainPullback F hF V ≫ (cochainIso p hp V).hom=
      (cochainIso p' hp' V).hom ≫ localPullback p p' F f hsquare hp hp' hF V := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact homVertexEquiv_pullback p p' F f hsquare hp hp' hF V n c

end TernaryPoly.SingularCoverNaturality
