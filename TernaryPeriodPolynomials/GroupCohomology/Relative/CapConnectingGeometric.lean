module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.CapConnectingPairing
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap
public import TernaryPeriodPolynomials.GroupCohomology.Relative.CochainSequence

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeCapConnecting
open CategoryTheory Limits HomologicalComplex
open SingularLocalCap SingularLocalCoefficient SingularLocalHomology SingularCoverNaturality

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  [IsCancelSMul G E] [IsCancelSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p' = p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G)

omit [MulAction G E'] [ContinuousConstSMul G E'] [IsCancelSMul G E'] in
/-- The original absolute cap and the general Leibniz descent are the same literal pairing. -/
theorem absolute_eq_descent (a b : ℕ) :
    absolute p hp V a b =
      Descent.homology (localCochains p hp V) (scalarChains B) (localChains p hp V)
        (capLinear p hp V) (cap_leibniz_complex p hp V) a b := rfl

/-- Genuine geometric cap commutes with the two relative connecting morphisms. The equality
has positive sign: its chain-level discrepancy is the explicit signed Leibniz boundary. -/
theorem geometric_connecting_cap
    [Mono (scalarSpaceMap f)] [Epi (localPullback p p' F f hsquare hp hp' hF V)]
    (a b : ℕ) (x : (localCochains p hp V).homology a)
    (c : (relativeScalarChains f).homology (a+b+1)) :
    homologyMap (localSpaceMap F hF V p p' hp hp') b
      (absolute p hp V a b x (RelativeChainSequence.connecting (scalarSpaceMap f) (a+b) c)) =
      relativeCochainCapHomology p p' F f hsquare hp hp' hF V (a+1) b
        (RelativeCochainSequence.connecting (localPullback p p' F f hsquare hp hp' hF V) a x)
        (eqToHom (congrArg (fun i => (relativeScalarChains f).homology i)
          (show a+b+1 = a+1+b by omega)) c) := by
  rw [absolute_eq_descent]
  exact connecting_pairing_homology
    (RelativeCochainSequence.sequence (localPullback p p' F f hsquare hp hp' hF V))
    (RelativeCochainSequence.shortExact (localPullback p p' F f hsquare hp hp' hF V))
    (RelativeChainSequence.sequence (scalarSpaceMap f))
    (RelativeChainSequence.shortExact (scalarSpaceMap f))
    (localSpaceMap F hF V p p' hp hp')
    (relativeCochainCap p p' F f hsquare hp hp' hF V)
    (capLinear p' hp' V) (capLinear p hp V)
    (relativeCochainCap_leibniz p p' F f hsquare hp hp' hF V)
    (cap_leibniz_complex p' hp' V) (cap_leibniz_complex p hp V)
    (relativeCochainCap_projection p p' F f hsquare hp hp' hF V)
    (cap_natural p p' F f hsquare hp hp' hF V) a b x c

end TernaryPoly.RelativeCapConnecting
