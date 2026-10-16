module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVComplement
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVEpi
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex SingularLocalSupport EquivariantSingularMayerVietoris
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  (K L : Set B) (hK : IsClosed K) (hL : IsClosed L)

/-- The actual signed comparison identifies intersection-support cohomology with the sum kernel. -/
def intersectionCohomologyIso (n : ℕ) :
    (supportCochains p V (K ∩ L)).homology n ≅ (kernel (supportSum p V K L)).homology n := by
  have := intersectionComparison_quasiIso p V K L hK hL
  exact isoOfQuasiIsoAt (intersectionComparison p V K L) n

/-- Cohomology of the two support complexes splits into their actual cohomology groups. -/
def supportPairCohomologyIso (n : ℕ) :
    (supportCochains p V K ⊞ supportCochains p V L).homology n ≅
      (supportCochains p V K).homology n ⊞ (supportCochains p V L).homology n :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapBiprod _ _

/-- The genuine signed pair of support-cohomology enlargements. -/
def fixedDiagonal (n : ℕ) :
    (supportCochains p V (K ∩ L)).homology n ⟶
      (supportCochains p V K).homology n ⊞ (supportCochains p V L).homology n :=
  biprod.lift (homologyMap (supportMap p V (K ∩ L) K Set.inter_subset_left) n)
    (-homologyMap (supportMap p V (K ∩ L) L Set.inter_subset_right) n)

/-- The genuine sum of support-cohomology enlargements. -/
def fixedSum (n : ℕ) :
    (supportCochains p V K).homology n ⊞ (supportCochains p V L).homology n ⟶
      (supportCochains p V (K ∪ L)).homology n :=
  biprod.desc (homologyMap (supportMap p V K (K ∪ L) Set.subset_union_left) n)
    (homologyMap (supportMap p V L (K ∪ L) Set.subset_union_right) n)

/-- The actual connecting homomorphism from union support to intersection support. -/
def fixedConnecting (n : ℕ) :
    (supportCochains p V (K ∪ L)).homology n ⟶ (supportCochains p V (K ∩ L)).homology (n+1) :=
  (fixedKernelSequence_shortExact p V K L).δ n (n+1) rfl ≫
    (intersectionCohomologyIso p V K L hK hL (n+1)).inv

/-- The transported fixed-support segment centered on the two support groups. -/
def fixedMiddleSegment (n : ℕ) : ShortComplex (ModuleCat ℚ) :=
  transportShortComplex ((fixedKernelSequence p V K L).map
    (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n))
    (intersectionCohomologyIso p V K L hK hL n).symm (supportPairCohomologyIso p V K L n) (Iso.refl _)

/-- The transported fixed-support segment centered on union support. -/
def fixedUnionSegment (n : ℕ) : ShortComplex (ModuleCat ℚ) :=
  transportShortComplex (ShortComplex.mk _ _ ((fixedKernelSequence_shortExact p V K L).comp_δ n (n+1) rfl))
    (supportPairCohomologyIso p V K L n) (Iso.refl _) (intersectionCohomologyIso p V K L hK hL (n+1)).symm

/-- The transported fixed-support segment centered on intersection support in positive degree. -/
def fixedIntersectionSegment (n : ℕ) : ShortComplex (ModuleCat ℚ) :=
  transportShortComplex (ShortComplex.mk _ _ ((fixedKernelSequence_shortExact p V K L).δ_comp n (n+1) rfl))
    (Iso.refl _) (intersectionCohomologyIso p V K L hK hL (n+1)).symm (supportPairCohomologyIso p V K L (n+1))

/-- Genuine fixed-support Mayer–Vietoris is exact at the two support groups in every degree. -/
theorem fixedMiddleSegment_exact (n : ℕ) : (fixedMiddleSegment p V K L hK hL n).Exact :=
  ShortComplex.exact_of_iso (transportShortComplexIso _ _ _ _)
    ((fixedKernelSequence_shortExact p V K L).homology_exact₂ n)

/-- Genuine fixed-support Mayer–Vietoris is exact at union support in every degree. -/
theorem fixedUnionSegment_exact (n : ℕ) : (fixedUnionSegment p V K L hK hL n).Exact :=
  ShortComplex.exact_of_iso (transportShortComplexIso _ _ _ _)
    ((fixedKernelSequence_shortExact p V K L).homology_exact₃ n (n+1) rfl)

/-- Genuine fixed-support Mayer–Vietoris is exact at intersection support in every positive degree. -/
theorem fixedIntersectionSegment_exact (n : ℕ) : (fixedIntersectionSegment p V K L hK hL n).Exact :=
  ShortComplex.exact_of_iso (transportShortComplexIso _ _ _ _)
    ((fixedKernelSequence_shortExact p V K L).homology_exact₁ n (n+1) rfl)

/-- The first transported map retains the literal signed support enlargements. -/
theorem fixedMiddleSegment_f (n : ℕ) : (fixedMiddleSegment p V K L hK hL n).f = fixedDiagonal p V K L n := by
  change homologyMap (intersectionComparison p V K L) n ≫
    homologyMap (kernel.ι (supportSum p V K L)) n ≫ (supportPairCohomologyIso p V K L n).hom = _
  rw [← Category.assoc, ← homologyMap_comp, intersectionComparison_inclusion]
  change (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).map (biprod.lift _ _) ≫
    ((homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapBiprod _ _).hom = _
  rw [biprod.map_lift_mapBiprod]
  simp only [Functor.map_neg, fixedDiagonal]
  rfl

/-- The second transported map retains the literal sum of support enlargements. -/
theorem fixedMiddleSegment_g (n : ℕ) : (fixedMiddleSegment p V K L hK hL n).g = fixedSum p V K L n := by
  change (supportPairCohomologyIso p V K L n).inv ≫ homologyMap (supportSum p V K L) n ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact biprod.mapBiprod_inv_map_desc (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n) _ _ _ _

/-- The two adjacent segments retain the same actual sum map. -/
theorem fixedUnionSegment_f (n : ℕ) : (fixedUnionSegment p V K L hK hL n).f = fixedSum p V K L n :=
  fixedMiddleSegment_g p V K L hK hL n

/-- The union segment retains the actual connecting morphism. -/
theorem fixedUnionSegment_g (n : ℕ) : (fixedUnionSegment p V K L hK hL n).g = fixedConnecting p V K L hK hL n := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- The intersection segment retains the same actual connecting morphism. -/
theorem fixedIntersectionSegment_f (n : ℕ) : (fixedIntersectionSegment p V K L hK hL n).f = fixedConnecting p V K L hK hL n := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- The intersection segment retains the actual signed diagonal in the next degree. -/
theorem fixedIntersectionSegment_g (n : ℕ) : (fixedIntersectionSegment p V K L hK hL n).g = fixedDiagonal p V K L (n+1) :=
  fixedMiddleSegment_f p V K L hK hL (n+1)

include hK hL in
/-- The signed intersection-support map is injective in degree zero, completing the start of the LES. -/
theorem fixedDiagonal_zero_mono : Mono (fixedDiagonal p V K L 0) := by
  have : Mono (homologyMap (kernel.ι (supportSum p V K L)) 0) :=
    mono_homologyMap_of_mono_of_not_rel _ 0 (by intro i hi; exact Nat.not_succ_le_zero i (Nat.le_of_eq hi))
  rw [← fixedMiddleSegment_f p V K L hK hL 0]
  change Mono ((intersectionCohomologyIso p V K L hK hL 0).hom ≫
    homologyMap (kernel.ι (supportSum p V K L)) 0 ≫ (supportPairCohomologyIso p V K L 0).hom)
  infer_instance

end TernaryPoly.SingularLocalCompactMV
