module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Boundary
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Representatives

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCap
open CategoryTheory Homology
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SingularCoverNaturality

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  [IsCancelSMul G E] [IsCancelSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p' = p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G)

omit [MulAction G E'] [ContinuousConstSMul G E'] [IsCancelSMul G E'] in
/-- The absolute homology cap is represented by the actual geometric cap of any genuine cycles. -/
theorem absolute_representatives (a b : ℕ)
    (x : Cycles ((localCochains p hp V).sc' (a-1) a (a+1)))
    (c : Cycles ((scalarChains B).sc' (a+b+1) (a+b) (a+b-1))) :
    absolute p hp V a b (Descent.cochainClass _ a x) (Descent.chainClass _ (a+b) c) =
      Descent.chainClass (localChains p hp V) b ⟨cap p hp V a b x.val c.val,cap_cycles p hp V a b x c⟩ :=
by
  unfold absolute Descent.cochainClass Descent.chainClass
  erw [LinearMap.compr₂_apply,LinearMap.comp_apply,LinearMap.compl₂_apply]
  have hx := congrArg (fun f => f (cycleClass _ x))
    ((localCochains p hp V).homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).inv_hom_id
  have hc := congrArg (fun f => f (cycleClass _ c))
    ((scalarChains B).homologyIsoSc' (a+b+1) (a+b) (a+b-1) (down_prev _) (down_next _)).inv_hom_id
  change ((localCochains p hp V).homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).hom
    (((localCochains p hp V).homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).inv
      (cycleClass _ x)) = cycleClass _ x at hx
  change ((scalarChains B).homologyIsoSc' (a+b+1) (a+b) (a+b-1) (down_prev _) (down_next _)).hom
    (((scalarChains B).homologyIsoSc' (a+b+1) (a+b) (a+b-1) (down_prev _) (down_next _)).inv
      (cycleClass _ c)) = cycleClass _ c at hc
  erw [hx,hc]
  unfold absoluteSC induced
  erw [descend_cycleClass]
  rfl

/-- The relative homology cap has its actual cokernel-chain representative. -/
theorem relativeCapHomology_representatives (a b : ℕ)
    (x : Cycles ((localCochains p' hp' V).sc' (a-1) a (a+1)))
    (c : Cycles ((relativeScalarChains f).sc' (a+b+1) (a+b) (a+b-1))) :
    relativeCapHomology p p' F f hsquare hp hp' hF V a b
      (Descent.cochainClass _ a x) (Descent.chainClass _ (a+b) c) =
      Descent.chainClass (relativeLocalChains p p' F hp hp' hF V) b
        ⟨relativeCap p p' F f hsquare hp hp' hF V a b x.val c.val,
          Descent.cycles _ _ _ _ (relativeCap_leibniz p p' F f hsquare hp hp' hF V) a b x c⟩ :=
  Descent.homology_representatives _ _ _ _ (relativeCap_leibniz p p' F f hsquare hp hp' hF V) a b x c

/-- Relative-cochain cap on homology is represented by the actual kernel-cochain/cokernel-chain operation. -/
theorem relativeCochainCapHomology_representatives (a b : ℕ)
    (x : Cycles ((relativeLocalCochains p p' F f hsquare hp hp' hF V).sc' (a-1) a (a+1)))
    (c : Cycles ((relativeScalarChains f).sc' (a+b+1) (a+b) (a+b-1))) :
    relativeCochainCapHomology p p' F f hsquare hp hp' hF V a b
      (Descent.cochainClass _ a x) (Descent.chainClass _ (a+b) c) =
      Descent.chainClass (localChains p' hp' V) b
        ⟨relativeCochainCap p p' F f hsquare hp hp' hF V a b x.val c.val,
          Descent.cycles _ _ _ _ (relativeCochainCap_leibniz p p' F f hsquare hp hp' hF V) a b x c⟩ :=
  Descent.homology_representatives _ _ _ _ (relativeCochainCap_leibniz p p' F f hsquare hp hp' hF V) a b x c

end TernaryPoly.SingularLocalCap
