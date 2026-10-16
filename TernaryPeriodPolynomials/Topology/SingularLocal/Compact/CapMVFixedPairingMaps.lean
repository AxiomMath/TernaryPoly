module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVFixedPairing
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVPairComponents
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVChainMono

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalCap SingularLocalSupport SingularLocalCompactCap SingularLocalCompactMV SingularLocalExcision

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  (K L : Set B) (hK : IsClosed K) (hL : IsClosed L) (U D : Opens B) (hKU : K ⊆ U) (hLD : L ⊆ D)

/-- The actual sum of localized cap pieces is the ambient cap of the actual support sum. -/
theorem middlePairing_sum (hUD : U ⊔ D = ⊤) (a b : ℕ)
    (x : (supportCochains p V K ⊞ supportCochains p V L).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    ((ordinarySequence p V U D hUD).g ≫ smallToLocal p V U D hUD).f b
      (middlePairing p V K L hK hL U D hKU hLD a b x c) =
    ambientPairing p V K L hK hL U D hKU hLD a b ((supportSum p V K L).f a x) c := by
  rw [ordinarySequence_g]
  erw [complexBiprod_desc_apply]
  simp only [middlePairing,biprodPairing_fst,biprodPairing_snd]
  change (openLocalChainMap p V U).f b (leftPairing p V K L hK hL U D hKU hLD a b
      ((biprod.fst : supportCochains p V K ⊞ supportCochains p V L ⟶ _).f a x) c) +
    (openLocalChainMap p V D).f b (rightPairing p V K L hK hL U D hKU hLD a b
      ((biprod.snd : supportCochains p V K ⊞ supportCochains p V L ⟶ _).f a x) c) = _
  rw [leftPairing_inclusion,rightPairing_inclusion,supportSum,complexBiprod_desc_apply]
  exact (congrArg (fun f => f c) (map_add (ambientPairing p V K L hK hL U D hKU hLD a b) _ _)).symm

/-- The actual intersection cap agrees in the left open with the left cap of the same cochain. -/
theorem intersectionPairing_left (a b : ℕ) (x : (supportCochains p V (K ∩ L)).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    (nestedLocalInclusion p ((U : Set B) ∩ (D : Set B)) U Set.inter_subset_left V).f b
      (intersectionPairing p V K L hK hL U D hKU hLD a b x c) =
    leftPairing p V K L hK hL U D hKU hLD a b
      ((supportMap p V (K ∩ L) K Set.inter_subset_left).f a x) c := by
  apply (ModuleCat.mono_iff_injective ((localInclusion p U V).f b)).mp inferInstance
  have hi := congrArg (fun f => f (intersectionPairing p V K L hK hL U D hKU hLD a b x c))
    (HomologicalComplex.congr_hom (nestedLocalInclusion_inclusion p ((U : Set B) ∩ (D : Set B)) U
      Set.inter_subset_left V) b)
  change (localInclusion p U V).f b ((nestedLocalInclusion p ((U : Set B) ∩ (D : Set B)) U
    Set.inter_subset_left V).f b _) = (openLocalChainMap p V (U ⊓ D : Opens B)).f b _ at hi
  rw [hi,intersectionPairing_inclusion]
  change _ = (openLocalChainMap p V U).f b _
  rw [leftPairing_inclusion]
  have hs := congrArg (fun f => f x) (HomologicalComplex.congr_hom
    (supportMap_comp p V (K ∩ L) K (K ∪ L) Set.inter_subset_left Set.subset_union_left) a)
  exact (congrArg (fun y => ambientPairing p V K L hK hL U D hKU hLD a b y c) hs).symm

/-- The actual intersection cap agrees in the right open with the right cap of the same cochain. -/
theorem intersectionPairing_right (a b : ℕ) (x : (supportCochains p V (K ∩ L)).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    (nestedLocalInclusion p ((U : Set B) ∩ (D : Set B)) D Set.inter_subset_right V).f b
      (intersectionPairing p V K L hK hL U D hKU hLD a b x c) =
    rightPairing p V K L hK hL U D hKU hLD a b
      ((supportMap p V (K ∩ L) L Set.inter_subset_right).f a x) c := by
  apply (ModuleCat.mono_iff_injective ((localInclusion p D V).f b)).mp inferInstance
  have hi := congrArg (fun f => f (intersectionPairing p V K L hK hL U D hKU hLD a b x c))
    (HomologicalComplex.congr_hom (nestedLocalInclusion_inclusion p ((U : Set B) ∩ (D : Set B)) D
      Set.inter_subset_right V) b)
  change (localInclusion p D V).f b ((nestedLocalInclusion p ((U : Set B) ∩ (D : Set B)) D
    Set.inter_subset_right V).f b _) = (openLocalChainMap p V (U ⊓ D : Opens B)).f b _ at hi
  rw [hi,intersectionPairing_inclusion]
  change _ = (openLocalChainMap p V D).f b _
  rw [rightPairing_inclusion]
  have hs := congrArg (fun f => f x) (HomologicalComplex.congr_hom
    (supportMap_comp p V (K ∩ L) L (K ∪ L) Set.inter_subset_right Set.subset_union_right) a)
  exact (congrArg (fun y => ambientPairing p V K L hK hL U D hKU hLD a b y c) hs).symm

/-- The actual signed chain diagonal intertwines the intersection cap and supported-cochain diagonal. -/
theorem intersectionPairing_diagonal (hUD : U ⊔ D = ⊤) (a b : ℕ)
    (x : (supportCochains p V (K ∩ L)).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    (ordinarySequence p V U D hUD).f.f b
      (intersectionPairing p V K L hK hL U D hKU hLD a b x c) =
    middlePairing p V K L hK hL U D hKU hLD a b ((supportDiagonal p V K L).f a x) c := by
  rw [ordinarySequence_f]
  apply complexBiprod_ext (restrictedLocalChains p U V) (restrictedLocalChains p D V) b
  · erw [complexBiprod_lift_fst]
    simp only [middlePairing,biprodPairing_fst,supportDiagonal]
    erw [complexBiprod_lift_fst]
    exact intersectionPairing_left p V K L hK hL U D hKU hLD a b x c
  · erw [complexBiprod_lift_snd]
    simp only [middlePairing,biprodPairing_snd,supportDiagonal]
    erw [complexBiprod_lift_snd]
    change -((nestedLocalInclusion p ((U : Set B) ∩ (D : Set B)) D Set.inter_subset_right V).f b
      (intersectionPairing p V K L hK hL U D hKU hLD a b x c)) =
      rightPairing p V K L hK hL U D hKU hLD a b
        (-((supportMap p V (K ∩ L) L Set.inter_subset_right).f a x)) c
    rw [map_neg,LinearMap.neg_apply]
    exact congrArg Neg.neg (intersectionPairing_right p V K L hK hL U D hKU hLD a b x c)

end TernaryPoly.SingularLocalCompactCapMV
