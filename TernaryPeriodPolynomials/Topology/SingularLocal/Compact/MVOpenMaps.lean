module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVFixed
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.ExtensionBetween

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalSupport EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [T2Space B]
  (U D : Opens B)

/-- The actual signed open-extension map from the intersection to the two opens. -/
def compactDiagonal (n : ℕ) : compactCohomology (restrictedProjection p (U ⊓ D : Opens B)) V n ⟶
    compactCohomology (restrictedProjection p U) V n ⊞ compactCohomology (restrictedProjection p D) V n :=
  biprod.lift (openExtensionBetween p V (U ⊓ D) U inf_le_left n)
    (-openExtensionBetween p V (U ⊓ D) D inf_le_right n)

/-- The actual sum of open-extension maps into ambient compact-support cohomology. -/
def compactSum (n : ℕ) :
    compactCohomology (restrictedProjection p U) V n ⊞ compactCohomology (restrictedProjection p D) V n ⟶
      compactCohomology p V n := biprod.desc (openExtension p V U n) (openExtension p V D n)

/-- The actual fixed-support signed diagonal represents the signed open-extension map. -/
theorem fixedDiagonal_classInOpen (K L : Compacts B) (hKU : (K : Set B) ⊆ U) (hLD : (L : Set B) ⊆ D) (n : ℕ) :
    fixedDiagonal p V K L n ≫ biprod.map (classInOpen p V U K hKU n) (classInOpen p V D L hLD n) =
      classInOpen p V (U ⊓ D) (K ⊓ L) (fun _ hx => ⟨hKU hx.1,hLD hx.2⟩) n ≫ compactDiagonal p V U D n := by
  apply biprod.hom_ext
  · erw [Category.assoc,biprod.map_fst,← Category.assoc,fixedDiagonal,biprod.lift_fst,
      Category.assoc,compactDiagonal,biprod.lift_fst]
    erw [classInOpen_natural p V U (K ⊓ L) K Set.inter_subset_left hKU n,
      classInOpen_between]
  · erw [Category.assoc,biprod.map_snd,← Category.assoc,fixedDiagonal,biprod.lift_snd,Preadditive.neg_comp,
      Category.assoc,compactDiagonal,biprod.lift_snd,Preadditive.comp_neg]
    erw [classInOpen_natural p V D (K ⊓ L) L Set.inter_subset_right hLD n,
      classInOpen_between]

/-- The actual fixed-support sum represents the sum of the two genuine open extensions. -/
theorem fixedSum_classInOpen (K L : Compacts B) (hKU : (K : Set B) ⊆ U) (hLD : (L : Set B) ⊆ D) (n : ℕ) :
    fixedSum p V K L n ≫ compactClassMap p V (K ⊔ L) n =
      biprod.map (classInOpen p V U K hKU n) (classInOpen p V D L hLD n) ≫ compactSum p V U D n := by
  apply biprod.hom_ext'
  · erw [fixedSum,biprod.inl_desc_assoc,biprod.inl_map_assoc,compactSum,biprod.inl_desc,
      compactClassMap_natural p V K (K ⊔ L) Set.subset_union_left n,classInOpen_extension]
  · erw [fixedSum,biprod.inr_desc_assoc,biprod.inr_map_assoc,compactSum,biprod.inr_desc,
      compactClassMap_natural p V L (K ⊔ L) Set.subset_union_right n,classInOpen_extension]

end TernaryPoly.SingularLocalCompactMV
