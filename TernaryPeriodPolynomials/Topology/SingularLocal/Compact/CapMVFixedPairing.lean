module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVLocalPairing
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVBiprodPairing
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVCover

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalCap SingularLocalSupport SingularLocalCompactCap SingularLocalHomology
open EquivariantSingularSmall SphereOddDegree RationalManifoldCompact

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  (K L : Set B) (hK : IsClosed K) (hL : IsClosed L) (U D : Opens B) (hKU : K ⊆ U) (hLD : L ⊆ D)

/-- The actual common refinement localizing both supported cap pieces and their intersection. -/
abbrev supportRefinement := intersectCover (supportOpenCover K hK U hKU) (supportOpenCover L hL D hLD)

/-- A common actual relative-small scalar complex for the two supported cap pieces. -/
abbrev supportScalarSmall := cokernel (smallPush (sInclusion (K ∪ L)ᶜ) (supportRefinement K L hK hL U D hKU hLD))

/-- The actual left support cap, with scalar chains canonically localized into the left open. -/
def leftPairing := localizedPairing p V (K ∪ L)ᶜ K
  (fun _ hx hk => hx (Or.inl hk)) hK U hKU (supportRefinement K L hK hL U D hKU hLD)
  (intersectCover_left _ _)

/-- The actual right support cap, with scalar chains canonically localized into the right open. -/
def rightPairing := localizedPairing p V (K ∪ L)ᶜ L
  (fun _ hx hl => hx (Or.inr hl)) hL D hLD (supportRefinement K L hK hL U D hKU hLD)
  (intersectCover_right _ _)

/-- The actual intersection cap, with scalar chains canonically localized into the intersection open. -/
def intersectionPairing := localizedPairing p V (K ∪ L)ᶜ (K ∩ L)
  (fun _ hx h => hx (Or.inl h.1)) (hK.inter hL) (U ⊓ D) (Set.inter_subset_inter hKU hLD)
  (supportRefinement K L hK hL U D hKU hLD) (intersectSupportCover_intersection K L hK hL U D hKU hLD)

/-- The actual middle cap pairing into the genuine pair of open local-chain complexes. -/
def middlePairing := biprodPairing (leftPairing p V K L hK hL U D hKU hLD)
  (rightPairing p V K L hK hL U D hKU hLD)

/-- The actual ambient support cap pulled back through the genuine relative-small comparison. -/
def ambientPairing := pullPairing (𝟙 (supportCochains p V (K ∪ L)))
  (relativeSmallMap (K ∪ L)ᶜ (supportRefinement K L hK hL U D hKU hLD))
    (supportCap p V (K ∪ L))

/-- The actual left localized cap has the Leibniz convention. -/
theorem leftPairing_leibniz : Descent.Leibniz (supportCochains p V K)
    (supportScalarSmall K L hK hL U D hKU hLD)
    (localChains (restrictedProjection p U) (restrictedQuotientCovering p U) V)
      (leftPairing p V K L hK hL U D hKU hLD) := localizedPairing_leibniz _ _ _ _ _ _ _ _ _ _

/-- The actual right localized cap has the Leibniz convention. -/
theorem rightPairing_leibniz : Descent.Leibniz (supportCochains p V L)
    (supportScalarSmall K L hK hL U D hKU hLD)
    (localChains (restrictedProjection p D) (restrictedQuotientCovering p D) V)
      (rightPairing p V K L hK hL U D hKU hLD) := localizedPairing_leibniz _ _ _ _ _ _ _ _ _ _

/-- The actual intersection localized cap has the Leibniz convention. -/
theorem intersectionPairing_leibniz : Descent.Leibniz (supportCochains p V (K ∩ L))
    (supportScalarSmall K L hK hL U D hKU hLD)
    (localChains (restrictedProjection p (U ⊓ D : Opens B)) (restrictedQuotientCovering p (U ⊓ D : Opens B)) V)
      (intersectionPairing p V K L hK hL U D hKU hLD) := localizedPairing_leibniz _ _ _ _ _ _ _ _ _ _

/-- The actual middle localized cap has the Leibniz convention. -/
theorem middlePairing_leibniz : Descent.Leibniz (supportCochains p V K ⊞ supportCochains p V L)
    (supportScalarSmall K L hK hL U D hKU hLD)
    (SingularLocalExcision.restrictedLocalChains p U V ⊞ SingularLocalExcision.restrictedLocalChains p D V)
      (middlePairing p V K L hK hL U D hKU hLD) :=
  biprodPairing_leibniz _ _ (leftPairing_leibniz p V K L hK hL U D hKU hLD)
    (rightPairing_leibniz p V K L hK hL U D hKU hLD)

/-- The actual ambient cap on common relative-small scalar chains has the Leibniz convention. -/
theorem ambientPairing_leibniz : Descent.Leibniz (supportCochains p V (K ∪ L))
    (supportScalarSmall K L hK hL U D hKU hLD) (localChains p hp.out V)
      (ambientPairing p V K L hK hL U D hKU hLD) :=
  pullPairing_leibniz _ _ _ (supportCap_leibniz p V (K ∪ L))

/-- The actual left localized cap maps to the ambient cap of its enlarged-support cochain. -/
theorem leftPairing_inclusion (a b : ℕ) (x : (supportCochains p V K).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    (openLocalChainMap p V U).f b (leftPairing p V K L hK hL U D hKU hLD a b x c) =
      ambientPairing p V K L hK hL U D hKU hLD a b
        ((supportMap p V K (K ∪ L) Set.subset_union_left).f a x) c :=
  (localizedPairing_inclusion p V _ _ _ _ _ _ _ _ a b x c).trans
    (supportCap_enlargement p V K (K ∪ L) Set.subset_union_left a b x _).symm

/-- The actual right localized cap maps to the ambient cap of its enlarged-support cochain. -/
theorem rightPairing_inclusion (a b : ℕ) (x : (supportCochains p V L).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    (openLocalChainMap p V D).f b (rightPairing p V K L hK hL U D hKU hLD a b x c) =
      ambientPairing p V K L hK hL U D hKU hLD a b
        ((supportMap p V L (K ∪ L) Set.subset_union_right).f a x) c :=
  (localizedPairing_inclusion p V _ _ _ _ _ _ _ _ a b x c).trans
    (supportCap_enlargement p V L (K ∪ L) Set.subset_union_right a b x _).symm

/-- The actual intersection localized cap maps to the ambient cap of the same supported cochain. -/
theorem intersectionPairing_inclusion (a b : ℕ) (x : (supportCochains p V (K ∩ L)).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    (openLocalChainMap p V (U ⊓ D : Opens B)).f b (intersectionPairing p V K L hK hL U D hKU hLD a b x c) =
      ambientPairing p V K L hK hL U D hKU hLD a b
        ((supportMap p V (K ∩ L) (K ∪ L) (Set.inter_subset_left.trans Set.subset_union_left)).f a x) c :=
  (localizedPairing_inclusion p V _ _ _ _ _ _ _ _ a b x c).trans
    (supportCap_enlargement p V (K ∩ L) (K ∪ L) (Set.inter_subset_left.trans Set.subset_union_left) a b x _).symm

end TernaryPoly.SingularLocalCompactCapMV
