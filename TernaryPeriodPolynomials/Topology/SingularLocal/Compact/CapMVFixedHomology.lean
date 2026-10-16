module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVSmallPairing
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVConnectingPairing
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVHomology

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCompactCap SingularLocalCompactMV SingularLocalCap

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  (K L : Set B) (hK : IsClosed K) (hL : IsClosed L) (U D : Opens B) (hKU : K ⊆ U) (hLD : L ⊆ D)
  (hUD : U ⊔ D = ⊤)

/-- The genuine kernel cap and genuine intersection cap agree under the actual
intersection-support quasi-isomorphism, on actual homology. -/
theorem kernelPairing_homology_intersection (a b : ℕ)
    (x : (supportCochains p V (K ∩ L)).homology a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).homology (a+b)) :
    Descent.homology _ _ _ (intersectionPairing p V K L hK hL U D hKU hLD)
      (intersectionPairing_leibniz p V K L hK hL U D hKU hLD) a b x c =
    Descent.homology _ _ _ (kernelPairing p V K L hK hL U D hKU hLD hUD)
      (kernelPairing_leibniz p V K L hK hL U D hKU hLD hUD) a b
      (homologyMap (intersectionComparison p V K L) a x) c := by
  have h := pairing_homology_natural (intersectionComparison p V K L) (𝟙 _) (𝟙 _)
    (intersectionPairing p V K L hK hL U D hKU hLD)
    (kernelPairing p V K L hK hL U D hKU hLD hUD)
    (intersectionPairing_leibniz p V K L hK hL U D hKU hLD)
    (kernelPairing_leibniz p V K L hK hL U D hKU hLD hUD)
    (fun a b x c => (kernelPairing_intersection p V K L hK hL U D hKU hLD hUD a b x c).symm) a b x c
  simp only [homologyMap_id,ModuleCat.id_apply] at h
  exact h

omit [IsCancelSMul G E] in
/-- The actual fixed-support connecting map followed by the comparison recovers the kernel LES map. -/
theorem fixedConnecting_comparison (a : ℕ) :
    fixedConnecting p V K L hK hL a ≫ homologyMap (intersectionComparison p V K L) (a+1) =
      (fixedKernelSequence_shortExact p V K L).δ a (a+1) rfl := by
  change ((fixedKernelSequence_shortExact p V K L).δ a (a+1) rfl ≫
    (intersectionCohomologyIso p V K L hK hL (a+1)).inv) ≫
      (intersectionCohomologyIso p V K L hK hL (a+1)).hom = _
  erw [Category.assoc,Iso.inv_hom_id,Category.comp_id]

/-- The genuine small-chain cap gives exactly the ambient support cap under small inclusion. -/
theorem smallPairing_homology_inclusion (a b : ℕ)
    (x : (supportCochains p V (K ∪ L)).homology a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).homology (a+b)) :
    homologyMap (smallToLocal p V U D hUD) b
      (Descent.homology _ _ _ (smallPairing p V K L hK hL U D hKU hLD hUD)
        (smallPairing_leibniz p V K L hK hL U D hKU hLD hUD) a b x c) =
    Descent.homology _ _ _ (ambientPairing p V K L hK hL U D hKU hLD)
      (ambientPairing_leibniz p V K L hK hL U D hKU hLD) a b x c := by
  have h := pairing_homology_natural (𝟙 _) (𝟙 _) (smallToLocal p V U D hUD)
    (smallPairing p V K L hK hL U D hKU hLD hUD)
    (ambientPairing p V K L hK hL U D hKU hLD)
    (smallPairing_leibniz p V K L hK hL U D hKU hLD hUD)
    (ambientPairing_leibniz p V K L hK hL U D hKU hLD)
    (smallPairing_inclusion p V K L hK hL U D hKU hLD hUD) a b x c
  simp only [homologyMap_id,ModuleCat.id_apply] at h
  exact h

/-- The actual ambient connecting map preserves the genuine small-chain LES boundary. -/
theorem ordinaryConnecting_inclusion (b : ℕ) :
    homologyMap (smallToLocal p V U D hUD) (b+1) ≫ ordinaryConnecting p V U D hUD b =
      (ordinarySequence_shortExact p V U D hUD).δ (b+1) b rfl := by
  change (ordinaryAmbientIso p V U D hUD (b+1)).hom ≫
    (ordinaryAmbientIso p V U D hUD (b+1)).inv ≫ _ = _
  erw [Iso.hom_inv_id_assoc]

/-- The actual fixed-support cap/Mayer–Vietoris connecting identity, on a common genuine
relative-small scalar cycle, has exactly the Leibniz sign (-1)^(a+1). -/
theorem fixedConnecting_pairing (a b : ℕ) (x : (supportCochains p V (K ∪ L)).homology a)
    (c : Homology.Cycles ((supportScalarSmall K L hK hL U D hKU hLD).sc' (a+b+2) (a+b+1) (a+b))) :
    ordinaryConnecting p V U D hUD b
      (Descent.homology _ _ _ (ambientPairing p V K L hK hL U D hKU hLD)
        (ambientPairing_leibniz p V K L hK hL U D hKU hLD) a (b+1) x
        (Descent.chainClass _ (a+b+1) c)) =
      (-1 : ℤ)^(a+1) • Descent.homology _ _ _ (intersectionPairing p V K L hK hL U D hKU hLD)
        (intersectionPairing_leibniz p V K L hK hL U D hKU hLD) (a+1) b
        (fixedConnecting p V K L hK hL a x)
        (Descent.chainClass _ (a+1+b) (castChainCycle _ (by omega) c)) := by
  rw [← smallPairing_homology_inclusion p V K L hK hL U D hKU hLD hUD a (b+1)]
  have hl := congrArg (fun f => f
    (Descent.homology _ _ _ (smallPairing p V K L hK hL U D hKU hLD hUD)
      (smallPairing_leibniz p V K L hK hL U D hKU hLD hUD) a (b+1) x (Descent.chainClass _ (a+b+1) c)))
    (ordinaryConnecting_inclusion p V U D hUD b)
  change ordinaryConnecting p V U D hUD b (homologyMap (smallToLocal p V U D hUD) (b+1) _) =
    (ordinarySequence_shortExact p V U D hUD).δ (b+1) b rfl _ at hl
  rw [hl,kernelPairing_homology_intersection p V K L hK hL U D hKU hLD hUD]
  have hr := congrArg (fun f => f x) (fixedConnecting_comparison p V K L hK hL a)
  change homologyMap (intersectionComparison p V K L) (a+1) (fixedConnecting p V K L hK hL a x) =
    (fixedKernelSequence_shortExact p V K L).δ a (a+1) rfl x at hr
  rw [hr]
  exact connecting_pairing (fixedKernelSequence p V K L) (fixedKernelSequence_shortExact p V K L)
    (ordinarySequence p V U D hUD) (ordinarySequence_shortExact p V U D hUD)
    (supportScalarSmall K L hK hL U D hKU hLD)
    (kernelPairing p V K L hK hL U D hKU hLD hUD) (middlePairing p V K L hK hL U D hKU hLD)
    (smallPairing p V K L hK hL U D hKU hLD hUD)
    (kernelPairing_leibniz p V K L hK hL U D hKU hLD hUD) (middlePairing_leibniz p V K L hK hL U D hKU hLD)
    (smallPairing_leibniz p V K L hK hL U D hKU hLD hUD)
    (kernelPairing_inclusion p V K L hK hL U D hKU hLD hUD)
    (smallPairing_sum p V K L hK hL U D hKU hLD hUD) a b x c

end TernaryPoly.SingularLocalCompactCapMV
