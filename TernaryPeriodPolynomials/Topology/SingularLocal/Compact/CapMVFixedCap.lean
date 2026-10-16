module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVFixedHomology
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVAmbientHomology
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVFundamental
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapBetween

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalCap SingularLocalSupport SingularLocalCompactCap SingularLocalCompactMV
open RationalManifoldCompact RationalLocalOrientation EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)
  (K L : Compacts B) (U D : Opens B) [ChartedSpace H (U ⊓ D : Opens B)]
  (hKU : (K : Set B) ⊆ U) (hLD : (L : Set B) ⊆ D)

omit [ChartedSpace H (U ⊓ D : Opens B)] in
/-- Evaluating the genuine ambient pairing on a relative-small fundamental class is the actual cap. -/
theorem ambientPairing_fundamental (a b : ℕ) (hab : a+b = n+2)
    (x : (supportCochains p V (K ⊔ L : Compacts B)).homology a)
    (c : (supportScalarSmall K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD).homology (a+b))
    (hc : homologyMap (relativeSmallMap (K ∪ L)ᶜ
      (supportRefinement K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD)) (a+b) c =
        capFundamentalClass n e o (K ⊔ L) a b hab) :
    Descent.homology _ _ _ (ambientPairing p V K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD)
      (ambientPairing_leibniz p V K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD) a b x c =
        compactCapAt p V n e o (K ⊔ L) a b hab x := by
  have h := ambientPairing_homology p V K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD a b x c
  rw [hc] at h
  exact h

/-- Evaluating the genuine intersection pairing on the ambient fundamental class is the actual
intersection cap with the canonical restricted orientation. -/
theorem intersectionPairing_fundamental (a b : ℕ) (hab : a+b = n+2)
    (x : (supportCochains p V (K ⊓ L : Compacts B)).homology a)
    (c : (supportScalarSmall K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD).homology (a+b))
    (hc : homologyMap (relativeSmallMap (K ∪ L)ᶜ
      (supportRefinement K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD)) (a+b) c =
        capFundamentalClass n e o (K ⊔ L) a b hab) :
    Descent.homology _ _ _ (intersectionPairing p V K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD)
      (intersectionPairing_leibniz p V K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD) a b x c =
      compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e (openOrientation n e o (U ⊓ D)) a b hab
        (classInOpen p V (U ⊓ D) (K ⊓ L) (Set.inter_subset_inter hKU hLD) a x) := by
  have h := localizedPairing_homology p V (K ∪ L)ᶜ (K ∩ L)
    (fun _ hx h => hx (Or.inl h.1)) (K.isCompact.isClosed.inter L.isCompact.isClosed)
    (U ⊓ D) (Set.inter_subset_inter hKU hLD)
    (supportRefinement K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD)
    (intersectSupportCover_intersection K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD) a b x c
  have hf := relativeLocalizeScalar_fundamental n e o (K ⊔ L) (K ⊓ L)
    (inf_le_left.trans le_sup_left) (U ⊓ D) (Set.inter_subset_inter hKU hLD)
    (supportRefinement K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD)
    (intersectSupportCover_intersection K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD) a b hab c hc
  have he := congrArg (fun f => f x) (classInOpen_capMap p V n e (U ⊓ D)
    (openOrientation n e o (U ⊓ D)) (K ⊓ L) (Set.inter_subset_inter hKU hLD) a b hab)
  exact h.trans ((congrArg (fun c => supportCapHomology (restrictedProjection p (U ⊓ D : Opens B)) V
    ((Subtype.val : (U ⊓ D : Opens B) → B) ⁻¹' (K ∩ L)) a b
      (homologyMap (supportToOpen p V (U ⊓ D : Opens B) (K ∩ L)) a x) c) hf).trans he.symm)

/-- The literal fixed-support cap/Mayer–Vietoris connecting square, including its derived sign. -/
theorem fixedConnecting_cap (hUD : U ⊔ D = ⊤) (a b : ℕ) (hab : a+(b+1) = n+2) :
    compactCapAt p V n e o (K ⊔ L) a (b+1) hab ≫ ordinaryConnecting p V U D hUD b =
      (-1 : ℤ)^(a+1) • (fixedConnecting p V K L K.isCompact.isClosed L.isCompact.isClosed a ≫
        classInOpen p V (U ⊓ D) (K ⊓ L) (Set.inter_subset_inter hKU hLD) (a+1) ≫
          compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
            (openOrientation n e o (U ⊓ D)) (a+1) b (by omega)) := by
  let C := supportScalarSmall K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD
  let q := relativeSmallMap (K ∪ L)ᶜ
    (supportRefinement K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD)
  obtain ⟨c,hc⟩ := (ModuleCat.epi_iff_surjective (homologyMap q (a+b+1))).mp inferInstance
    (capFundamentalClass n e o (K ⊔ L) a (b+1) hab)
  obtain ⟨z,rfl⟩ := Algebra.chainClass_surjective C (a+b+1) c
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := fixedConnecting_pairing p V K L K.isCompact.isClosed L.isCompact.isClosed U D hKU hLD hUD a b x z
  rw [ambientPairing_fundamental p V n e o K L U D hKU hLD a (b+1) hab x _ hc,
    intersectionPairing_fundamental p V n e o K L U D hKU hLD (a+1) b (by omega) _ _
      (fundamental_representative_cast n e o (K ⊔ L) C q a b hab z hc)] at h
  exact h

end TernaryPoly.SingularLocalCompactCapMV
