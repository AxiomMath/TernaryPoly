module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVDiagrams
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVPairColimit
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.ExtensionBetween

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalSupport EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [T2Space B]
  (U D : Opens B)

/-- Actual excision identifies the left ambient-support diagram with genuine support cohomology on the open set. -/
def leftDiagramIso (n : ℕ) : leftDiagram p V U D n ≅
    CategoryTheory.Prod.fst (Compacts U) (Compacts D) ⋙ compactCohomologyDiagram (restrictedProjection p U) V n :=
  NatIso.ofComponents (fun P => openSupportIso p V U P.1 n) (fun f =>
    openSupportIso_natural p V U _ _ (leOfHom f.1) n)

/-- Actual excision identifies the right ambient-support diagram with genuine support cohomology on the open set. -/
def rightDiagramIso (n : ℕ) : rightDiagram p V U D n ≅
    CategoryTheory.Prod.snd (Compacts U) (Compacts D) ⋙ compactCohomologyDiagram (restrictedProjection p D) V n :=
  NatIso.ofComponents (fun P => openSupportIso p V D P.2 n) (fun f =>
    openSupportIso_natural p V D _ _ (leOfHom f.2) n)

/-- Actual excision identifies the intersection diagram with genuine compact supports in the intersection open set. -/
def intersectionDiagramIso (n : ℕ) : intersectionDiagram p V U D n ≅
    compactIntersectionFunctor U D ⋙ compactCohomologyDiagram (restrictedProjection p (U ⊓ D : Opens B)) V n :=
  NatIso.ofComponents (fun P => supportExcisionIso p V (U ⊓ D) (compactIntersection U D P)
    (compactIntersection U D P).isCompact.isClosed (compactIntersection_subset U D P) n) (by
      intro P Q f
      change homologyMap _ n ≫ homologyMap _ n = homologyMap _ n ≫ homologyMap _ n
      erw [← homologyMap_comp,← homologyMap_comp,
        supportToOpen_natural p V (U ⊓ D) (compactIntersection U D P) (compactIntersection U D Q)
          ((intersectionSupportOrder U D).monotone ⟨leOfHom f.1,leOfHom f.2⟩)]
      rfl)

/-- The left pair-indexed colimit is actual compact-support cohomology on the left open set. -/
def leftColimitIso (n : ℕ) : colimit (leftDiagram p V U D n) ≅ compactCohomology (restrictedProjection p U) V n :=
  colim.mapIso (leftDiagramIso p V U D n) ≪≫
    Functor.Final.colimitIso (CategoryTheory.Prod.fst (Compacts U) (Compacts D)) (compactCohomologyDiagram (restrictedProjection p U) V n)

/-- The right pair-indexed colimit is actual compact-support cohomology on the right open set. -/
def rightColimitIso (n : ℕ) : colimit (rightDiagram p V U D n) ≅ compactCohomology (restrictedProjection p D) V n :=
  colim.mapIso (rightDiagramIso p V U D n) ≪≫
    Functor.Final.colimitIso (CategoryTheory.Prod.snd (Compacts U) (Compacts D)) (compactCohomologyDiagram (restrictedProjection p D) V n)

/-- The intersection-pair colimit is actual compact-support cohomology on the intersection open set. -/
def intersectionColimitIso (n : ℕ) : colimit (intersectionDiagram p V U D n) ≅
    compactCohomology (restrictedProjection p (U ⊓ D : Opens B)) V n := by
  have := compactIntersectionFunctor_final U D
  exact colim.mapIso (intersectionDiagramIso p V U D n) ≪≫
    Functor.Final.colimitIso (compactIntersectionFunctor U D)
      (compactCohomologyDiagram (restrictedProjection p (U ⊓ D : Opens B)) V n)

/-- The pair-diagram colimit is the pair of actual compact-support cohomology groups. -/
def pairColimitIso (n : ℕ) : colimit (pairDiagram p V U D n) ≅
    compactCohomology (restrictedProjection p U) V n ⊞ compactCohomology (restrictedProjection p D) V n :=
  pointwisePairColimitIso (leftDiagram p V U D n) (rightDiagram p V U D n) ≪≫
    biprod.mapIso (leftColimitIso p V U D n) (rightColimitIso p V U D n)

/-- The left colimit identification retains actual ambient compact-support representatives. -/
theorem leftColimitIso_ι (n : ℕ) (P : Compacts U × Compacts D) :
    colimit.ι (leftDiagram p V U D n) P ≫ (leftColimitIso p V U D n).hom =
      classInOpen p V U (compactOpenImage U P.1) (compactOpenImage_subset U P.1) n := by
  change _ ≫ (colim.map (leftDiagramIso p V U D n).hom ≫ _) = _
  erw [← Category.assoc,colimit.ι_map,Category.assoc,Functor.Final.ι_colimitIso_hom]
  exact (classInOpen_image p V U P.1 n).symm

/-- The right colimit identification retains actual ambient compact-support representatives. -/
theorem rightColimitIso_ι (n : ℕ) (P : Compacts U × Compacts D) :
    colimit.ι (rightDiagram p V U D n) P ≫ (rightColimitIso p V U D n).hom =
      classInOpen p V D (compactOpenImage D P.2) (compactOpenImage_subset D P.2) n := by
  change _ ≫ (colim.map (rightDiagramIso p V U D n).hom ≫ _) = _
  erw [← Category.assoc,colimit.ι_map,Category.assoc,Functor.Final.ι_colimitIso_hom]
  exact (classInOpen_image p V D P.2 n).symm

/-- The intersection colimit identification retains the actual restricted ambient support class. -/
theorem intersectionColimitIso_ι (n : ℕ) (P : Compacts U × Compacts D) :
    colimit.ι (intersectionDiagram p V U D n) P ≫ (intersectionColimitIso p V U D n).hom =
      classInOpen p V (U ⊓ D) (compactIntersection U D P) (compactIntersection_subset U D P) n := by
  change _ ≫ (colim.map (intersectionDiagramIso p V U D n).hom ≫ _) = _
  erw [← Category.assoc,colimit.ι_map,Category.assoc,Functor.Final.ι_colimitIso_hom]
  rfl

/-- Composition of two actual binary-pair maps retains the two component compositions. -/
theorem biprodMap_comp {A B C D E F : ModuleCat.{0} ℚ}
    (a : A ⟶ C) (b : B ⟶ D) (c : C ⟶ E) (d : D ⟶ F) :
    biprod.map a b ≫ biprod.map c d = biprod.map (a ≫ c) (b ≫ d) := by
  apply biprod.hom_ext
  · simp only [Category.assoc,biprod.map_fst,biprod.map_fst_assoc]
  · simp only [Category.assoc,biprod.map_snd,biprod.map_snd_assoc]

/-- The pair-colimit identification retains both actual compact-support representatives. -/
theorem pairColimitIso_ι (n : ℕ) (P : Compacts U × Compacts D) :
    colimit.ι (pairDiagram p V U D n) P ≫ (pairColimitIso p V U D n).hom =
      biprod.map (classInOpen p V U (compactOpenImage U P.1) (compactOpenImage_subset U P.1) n)
        (classInOpen p V D (compactOpenImage D P.2) (compactOpenImage_subset D P.2) n) := by
  change _ ≫ ((pointwisePairColimitIso (leftDiagram p V U D n) (rightDiagram p V U D n)).hom ≫ _) = _
  erw [← Category.assoc,pointwisePairColimitIso_ι]
  change biprod.map (colimit.ι (leftDiagram p V U D n) P) (colimit.ι (rightDiagram p V U D n) P) ≫
    biprod.map (leftColimitIso p V U D n).hom (rightColimitIso p V U D n).hom = _
  erw [biprodMap_comp,leftColimitIso_ι,rightColimitIso_ι]
  rfl

variable [LocallyCompactSpace B] (hUD : U ⊔ D = ⊤)

/-- The union-pair colimit is actual ambient compact-support cohomology. -/
def unionColimitIso (n : ℕ) : colimit (unionDiagram p V U D n) ≅ compactCohomology p V n := by
  have := compactUnionFunctor_final U D hUD
  exact Functor.Final.colimitIso (compactUnionFunctor U D) (compactCohomologyDiagram p V n)

/-- The union colimit identification retains the actual ambient compact support. -/
theorem unionColimitIso_ι (n : ℕ) (P : Compacts U × Compacts D) :
    colimit.ι (unionDiagram p V U D n) P ≫ (unionColimitIso p V U D hUD n).hom =
      compactClassMap p V (compactUnion U D P) n := by
  have := compactUnionFunctor_final U D hUD
  exact Functor.Final.ι_colimitIso_hom (compactUnionFunctor U D) (compactCohomologyDiagram p V n) P

end TernaryPoly.SingularLocalCompactMV
