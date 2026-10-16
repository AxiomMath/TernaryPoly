module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.KroneckerRep
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.PairingClass
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Bridge
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.SingularDiag
public import TernaryPeriodPolynomials.GroupCohomology.Relative.CapConnectingCompactAbsolute

@[expose] public section


/-!
# The geometric pairing as the invariant functional `pairFun` on an equivariant chain

On a compact oriented manifold `B` covered by a quotient covering `p : E ⟶ B` with deck group `G`, let `ω` be a chain of
the equivariant singular chains of `E` whose pushforward is a cycle representing the ordinary fundamental class.  Then
for cocycles `b : C_2(E) ⟶ V`, `a : C_2(E) ⟶ V^*`, the Kronecker pairing `⟨[a], [B] ∩ [b]⟩` of the library is the value
`(pairFun (singDiagSystem E) (evalRep V) b a) ω`, where `evalRep V : V ⊗ V^* ⟶ 𝟙_` is the evaluation.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalHomology
  TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.SingularLocalDuality TernaryPoly.CompactOrdinaryCap TernaryPoly.RationalLocalOrientation
  TernaryPoly.EquivariantSingularCohomology TernaryPoly.RelativeCapConnecting TernaryPoly.SingularLocalCompactCap TernaryPoly.HalfSpaceBoundaryOrientation
  TernaryPoly.SingularLocalCompactCap.Algebra RationalManifoldCompact SphereOddDegree.AffineBarycentricSubdivision
open TernaryPeriodPolynomials.Argument.KroneckerRep

open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {G : Type} [Group G]

theorem evalBilin_invariant (V : Rep.{0} ℚ G) (g : G) (v : V) (φ : dualRepresentation V) :
    dualValue ((dualRepresentation V).ρ g φ) (V.ρ g v) = dualValue φ v := by
  rw [dualRepresentation_apply]
  have : g⁻¹ • (V.ρ g v) = v := by
    change V.ρ g⁻¹ (V.ρ g v) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  rw [this]

/-- The evaluation pairing `V ⊗ V^* → ℚ` as a morphism of representations. -/
def evalRep (V : Rep.{0} ℚ G) : V ⊗ dualRepresentation V ⟶ 𝟙_ (Rep.{0} ℚ G) :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ (Representation.trivial ℚ G ℚ)
    (TensorProduct.lift (LinearMap.flip (LinearMap.id : Module.Dual ℚ V →ₗ[ℚ] Module.Dual ℚ V)))
    (fun g x => by
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul v φ =>
        show dualValue ((dualRepresentation V).ρ g φ) (V.ρ g v) =
          ((Representation.trivial ℚ G ℚ) g) (dualValue φ v)
        rw [evalBilin_invariant]
        rfl))

theorem evalRep_tmul (V : Rep.{0} ℚ G) (v : V) (φ : dualRepresentation V) :
    (evalRep V).hom (v ⊗ₜ[ℚ] φ) = dualValue φ v := rfl

section Geo

variable {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

omit [IsCancelSMul G E] in
theorem homVertex_cocycle (n : ℕ) (f : chainRep G E n ⟶ V) (hf : (equivariantChains G E).d (n+1) n ≫ f = 0) :
    ((localCochains p hp.out V).d n (n+1)).hom (homVertexEquiv p hp.out V n f) = 0 := by
  have h := homVertexEquiv_d p hp.out V n f
  have h0 : (cochains G E V).d n (n+1) f = 0 := hf
  have e : ((localCochains p hp.out V).d n (n+1)).hom (homVertexEquiv p hp.out V n f) =
      differential p hp.out V n (homVertexEquiv p hp.out V n f) := by
    simp only [localCochains, CochainComplex.of_d]
    rfl
  rw [e, h, h0]
  exact map_zero _

omit [IsCancelSMul G E] in
/-- The local cochain cycle attached to an equivariant cochain cocycle. -/
def cocycleOf (n : ℕ) (f : chainRep G E n ⟶ V) (hf : (equivariantChains G E).d (n+1) n ≫ f = 0) :
    Homology.Cycles ((localCochains p hp.out V).sc' (n-1) n (n+1)) :=
  ⟨homVertexEquiv p hp.out V n f, homVertex_cocycle p V n f hf⟩

variable {H : Type} [TopologicalSpace H] [T2Space B] [SecondCountableTopology B] [ChartedSpace H B]
  [CompactSpace B] (e : H ≃ₜ EuclideanSpace ℝ (Fin (2+2))) (o : Orientation (2+2) B)

omit [SecondCountableTopology B] in
theorem geoPairing_eq_pairFun (b : chainRep G E 2 ⟶ V) (hb : (equivariantChains G E).d (2+1) 2 ≫ b = 0)
    (a : chainRep G E 2 ⟶ dualRepresentation V) (ha : (equivariantChains G E).d (2+1) 2 ≫ a = 0)
    (ω : chainRep G E (2+2))
    (c : Homology.Cycles ((scalarChains B).sc' (2+2+1) (2+2) (2+2-1)))
    (hc : c.val = (singularChainMap ℚ p (2+2)).hom ω)
    (hcls : chainClass (scalarChains B) (2+2) c =
      homologyDegreeChange (scalarChains B) (2+2) (2+2) rfl (ordinaryFundamentalClass 2 e o)) :
    homologyPairing p hp.out V 2 (cochainClass _ 2 (cocycleOf p (dualRepresentation V) 2 a ha))
      (ordinaryCapMap p V 2 e o 2 2 rfl (cochainClass _ 2 (cocycleOf p V 2 b hb))) =
      (pairFun (singDiagSystem E) (evalRep V) b a).hom ω := by
  rw [ordinaryCap_eq_absolute p V 2 e o 2 2 rfl, ← hcls, absolute_representatives p hp.out V 2 2 _ c,
    homologyPairing_cochainClass_chainClass p hp.out V 2 _ _]
  show degreeDuality p hp.out V 2 (homVertexEquiv p hp.out (dualRepresentation V) 2 a)
    (cap p hp.out V 2 2 (homVertexEquiv p hp.out V 2 b) c.val) = _
  have hb' := cap_bridge p hp.out V 2 2 b ω
  have e1 : cap p hp.out V 2 2 (homVertexEquiv p hp.out V 2 b) ((singularChainMap ℚ p (2+2)).hom ω) =
      degreeEquiv p hp.out V 2 (Representation.Coinvariants.mk (V.ρ.tprod (chainRep G E 2).ρ)
        ((capE E V 2 2 b).hom ω)) := by
    rw [← (degreeEquiv p hp.out V 2).apply_symm_apply
      (cap p hp.out V 2 2 (homVertexEquiv p hp.out V 2 b) ((singularChainMap ℚ p (2+2)).hom ω)), hb']
    rfl
  rw [hc, e1, degreeDuality_degreeEquiv_mk p hp.out V 2 a]
  have e2 : (pairFun (singDiagSystem E) (evalRep V) b a).hom ω =
      (evalRep V).hom ((V ◁ a).hom ((capE E V 2 2 b).hom ω)) := by
    have hcap : (singDiagSystem E).Δ 2 2 (2+2) rfl ≫ (b ▷ chainRep G E 2) = capE E V 2 2 b :=
      singDiagSystem_cap E b hb 2
    have e3 : ∀ (X : Rep.{0} ℚ G) (b' : X ⟶ V) (a' : X ⟶ dualRepresentation V),
        b' ⊗ₘ a' = (b' ▷ X) ≫ (V ◁ a') := fun X b' a' => MonoidalCategory.tensorHom_def _ _
    have e4 : pairFun (singDiagSystem E) (evalRep V) b a = capE E V 2 2 b ≫ (V ◁ a) ≫ evalRep V := by
      unfold pairFun
      rw [e3 ((equivariantChains G E).X 2) b a, ← hcap]
      simp only [Category.assoc]
      rfl
    rw [e4]
    rfl
  rw [e2]
  have e5 : ∀ ζ : V ⊗[ℚ] chainRep G E 2,
      TensorProduct.lift (pairB V 2 a) ζ = (evalRep V).hom ((V ◁ a).hom ζ) := by
    intro ζ
    induction ζ using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v s =>
      rw [TensorProduct.lift.tmul]
      change dualValue (a.hom s) v = (evalRep V).hom (v ⊗ₜ[ℚ] a.hom s)
      rfl
  exact e5 _

end Geo

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
