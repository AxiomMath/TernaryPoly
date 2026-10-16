module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVRelativeLocalization
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVPairing
public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.CapOpen

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCompactCap SingularLocalCap SingularLocalHomology
open EquivariantSingularSmall SphereOddDegree RationalRelativeSingular RationalLocalOrientation

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  [IsCancelSMul G E] (A K : Set B) (hAK : A ⊆ Kᶜ) (hK : IsClosed K)
  (U : Opens B) (hKU : K ⊆ U) (𝒰 : OpenCoverData B)
  (href : ∀ n (σ : singularSimplices B n), IsSmallSimplex 𝒰 σ →
    IsSmallSimplex (supportOpenCover K hK U hKU) σ)

/-- The actual support cochains cap actual relative-small scalar chains to genuine local
chains on the specified open neighborhood. -/
def localizedPairing (a b : ℕ) : (supportCochains p V K).X a →ₗ[ℚ]
    (cokernel (smallPush (sInclusion A) 𝒰)).X (a+b) →ₗ[ℚ]
      (localChains (restrictedProjection p U) (restrictedQuotientCovering p U) V).X b :=
  pullPairing (supportToOpen p V U K) (relativeLocalizeScalar A K hAK hK U hKU 𝒰 href)
    (supportCap (restrictedProjection p U) V ((Subtype.val : U → B) ⁻¹' K)) a b

/-- Localization preserves the exact geometric cap Leibniz identity in all degrees. -/
theorem localizedPairing_leibniz :
    Descent.Leibniz (supportCochains p V K) (cokernel (smallPush (sInclusion A) 𝒰))
      (localChains (restrictedProjection p U) (restrictedQuotientCovering p U) V)
        (localizedPairing p V A K hAK hK U hKU 𝒰 href) :=
  pullPairing_leibniz _ _ _ (supportCap_leibniz (restrictedProjection p U) V _)

/-- Genuine local inclusion of the localized cap is exactly the ambient support cap after
the literal relative-small comparison and support restriction. -/
theorem localizedPairing_inclusion (a b : ℕ) (x : (supportCochains p V K).X a)
    (c : (cokernel (smallPush (sInclusion A) 𝒰)).X (a+b)) :
    (openLocalChainMap p V U).f b (localizedPairing p V A K hAK hK U hKU 𝒰 href a b x c) =
      supportCap p V K a b x
        ((relativeSmallMap A 𝒰 ≫ relativeMap (ContinuousMap.id B) A Kᶜ hAK).f (a+b) c) := by
  change (openLocalChainMap p V U).f b
    (supportCap (restrictedProjection p U) V ((Subtype.val : U → B) ⁻¹' K) a b
      ((supportToOpen p V U K).f a x) ((relativeLocalizeScalar A K hAK hK U hKU 𝒰 href).f (a+b) c)) = _
  exact (supportCap_toOpen p V U K a b x
    ((relativeLocalizeScalar A K hAK hK U hKU 𝒰 href).f (a+b) c)).trans
      (congrArg (supportCap p V K a b x) (congrArg (fun f => f c)
        (HomologicalComplex.congr_hom (relativeLocalizeScalar_excision A K hAK hK U hKU 𝒰 href) (a+b))))

/-- The localized pairing induces exactly the actual cap pairing on the open support
cohomology and the actual localized scalar support homology. -/
theorem localizedPairing_homology (a b : ℕ) (x : (supportCochains p V K).homology a)
    (c : (cokernel (smallPush (sInclusion A) 𝒰)).homology (a+b)) :
    Descent.homology _ _ _ (localizedPairing p V A K hAK hK U hKU 𝒰 href)
      (localizedPairing_leibniz p V A K hAK hK U hKU 𝒰 href) a b x c =
      supportCapHomology (restrictedProjection p U) V ((Subtype.val : U → B) ⁻¹' K) a b
        (homologyMap (supportToOpen p V U K) a x)
        (homologyMap (relativeLocalizeScalar A K hAK hK U hKU 𝒰 href) (a+b) c) :=
  pullPairing_homology _ _ _ (supportCap_leibniz (restrictedProjection p U) V _) a b x c

end TernaryPoly.SingularLocalCompactCapMV
