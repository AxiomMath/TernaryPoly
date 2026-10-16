module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.SingularCap
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Naturality

@[expose] public section


/-!
# Bridge from the equivariant cap to the library's quotient-level local-coefficient cap

For a quotient covering `p : E ⟶ B` with deck group `G`, a cochain `f : C_a(E) ⟶ V` and an equivariant chain
`ω ∈ C_{a+b}(E)`, the library's cap of the corresponding local cochain `homVertexEquiv f` with the pushed-forward scalar
chain `p_# ω` is, under the identification `degreeEquiv` of local chains with the coinvariants `(V ⊗ C_b(E))_G`,
the coinvariant class of the equivariant cap `capE f ω` (`cap_bridge`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory MonoidalCategory
open TernaryPoly TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalHomology
open TernaryPoly.FreeActionLinearization TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalCap
open SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep ℚ G)

theorem cap_bridge_chainElement (a b : ℕ) (f : chainRep G E a ⟶ V) (σ : SingularSimplex E (a+b)) :
    (degreeEquiv p hp V b).symm
      (cap p hp V a b (homVertexEquiv p hp V a f)
        ((singularChainMap ℚ p (a+b)).hom (chainElement G E (a+b) σ))) =
    Representation.Coinvariants.mk (V ⊗ chainRep G E b).ρ (capElem E V a b f σ) := by
  have h1 : (singularChainMap ℚ p (a+b)).hom (chainElement G E (a+b) σ) =
      chainGenerator ℚ B (a+b) (CoveringSingularOrbits.projection p (a+b) σ) :=
    singularChainMap_generator ℚ p (a+b) σ
  rw [h1, cap_generator]
  rw [capSimplex_lift p hp V a b (homVertexEquiv p hp V a f) (σ := CoveringSingularOrbits.projection p (a+b) σ)
    ⟨σ, rfl⟩]
  change (generator G E V b (backSimplex E a b σ))
      (CoveringSingularOrbits.vertexToFunction p hp ((homVertexEquiv p hp V a) f) (frontSimplex E a b σ)) = _
  rw [vertexToFunction_homVertexEquiv]
  rfl

theorem cap_bridge (a b : ℕ) (f : chainRep G E a ⟶ V) (ω : chainRep G E (a+b)) :
    (degreeEquiv p hp V b).symm
      (cap p hp V a b (homVertexEquiv p hp V a f) ((singularChainMap ℚ p (a+b)).hom ω)) =
    ((Rep.coinvariantsMk ℚ G).app (V ⊗ chainRep G E b)).hom ((capE E V a b f).hom ω) := by
  have h : ((degreeEquiv p hp V b).symm.toLinearMap ∘ₗ cap p hp V a b (homVertexEquiv p hp V a f)) ∘ₗ
        (singularChainMap ℚ p (a+b)).hom =
      ((Rep.coinvariantsMk ℚ G).app (V ⊗ chainRep G E b)).hom ∘ₗ (capE E V a b f).hom.toLinearMap := by
    apply chainRep_linear_ext E
    intro σ
    have e := cap_bridge_chainElement p hp V a b f σ
    refine e.trans ?_
    change _ = ((Rep.coinvariantsMk ℚ G).app (V ⊗ chainRep G E b)).hom ((capE E V a b f).hom (chainElement G E (a+b) σ))
    rw [capE_chainElement]
    rfl
  exact LinearMap.congr_fun h ω

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
