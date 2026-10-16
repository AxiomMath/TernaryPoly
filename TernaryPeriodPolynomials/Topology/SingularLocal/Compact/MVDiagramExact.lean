module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVDiagrams
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVColimitAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalSupport

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [T2Space B]
  (U D : Opens B)

/-- The actual pair-indexed middle segment, retaining the genuine maps. -/
def diagramMiddleSegment (n : ℕ) : ShortComplex ((Compacts U × Compacts D) ⥤ ModuleCat ℚ) :=
  ShortComplex.mk (diagonalTransformation p V U D n) (sumTransformation p V U D n) (by
    apply NatTrans.ext
    funext P
    change (diagonalTransformation p V U D n).app P ≫ (sumTransformation p V U D n).app P = 0
    rw [show (diagonalTransformation p V U D n).app P = _ from
      (fixedMiddleSegment_f p V (compactOpenImage U P.1) (compactOpenImage D P.2)
        (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).symm,
      show (sumTransformation p V U D n).app P = _ from
      (fixedMiddleSegment_g p V (compactOpenImage U P.1) (compactOpenImage D P.2)
        (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).symm]
    exact (fixedMiddleSegment p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).zero)

/-- The actual middle diagram is exact at every compact support pair. -/
theorem diagramMiddleSegment_exact_obj (n : ℕ) (P : Compacts U × Compacts D) :
    ((diagramMiddleSegment p V U D n).map ((evaluation _ _).obj P)).Exact := by
  refine ShortComplex.exact_of_iso (ShortComplex.isoMk (S₁ := fixedMiddleSegment p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_)
    (fixedMiddleSegment_exact p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n)
  · dsimp only [Iso.refl_hom]
    erw [Category.id_comp, Category.comp_id]
    exact (fixedMiddleSegment_f p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).symm
  · dsimp only [Iso.refl_hom]
    erw [Category.id_comp, Category.comp_id]
    exact (fixedMiddleSegment_g p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).symm

/-- Filtered colimits preserve exactness of the actual compact-pair middle segment. -/
theorem diagramMiddleSegment_colimit_exact (n : ℕ) :
    ((diagramMiddleSegment p V U D n).map colim).Exact :=
  filteredColimit_exact _ (diagramMiddleSegment_exact_obj p V U D n)

/-- The actual pair-indexed union segment, retaining the genuine maps. -/
def diagramUnionSegment (n : ℕ) : ShortComplex ((Compacts U × Compacts D) ⥤ ModuleCat ℚ) :=
  ShortComplex.mk (sumTransformation p V U D n) (connectingTransformation p V U D n) (by
    apply NatTrans.ext
    funext P
    change (sumTransformation p V U D n).app P ≫ (connectingTransformation p V U D n).app P = 0
    rw [show (sumTransformation p V U D n).app P = _ from
      (fixedUnionSegment_f p V (compactOpenImage U P.1) (compactOpenImage D P.2)
        (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).symm,
      show (connectingTransformation p V U D n).app P = _ from
      (fixedUnionSegment_g p V (compactOpenImage U P.1) (compactOpenImage D P.2)
        (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).symm]
    exact (fixedUnionSegment p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).zero)

/-- The actual union diagram is exact at every compact support pair. -/
theorem diagramUnionSegment_exact_obj (n : ℕ) (P : Compacts U × Compacts D) :
    ((diagramUnionSegment p V U D n).map ((evaluation _ _).obj P)).Exact := by
  refine ShortComplex.exact_of_iso (ShortComplex.isoMk (S₁ := fixedUnionSegment p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_)
    (fixedUnionSegment_exact p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n)
  · dsimp only [Iso.refl_hom]
    erw [Category.id_comp, Category.comp_id]
    exact (fixedUnionSegment_f p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).symm
  · dsimp only [Iso.refl_hom]
    erw [Category.id_comp]

/-- Filtered colimits preserve exactness of the actual compact-pair union segment. -/
theorem diagramUnionSegment_colimit_exact (n : ℕ) :
    ((diagramUnionSegment p V U D n).map colim).Exact :=
  filteredColimit_exact _ (diagramUnionSegment_exact_obj p V U D n)

/-- The actual pair-indexed intersection segment, retaining the genuine maps. -/
def diagramIntersectionSegment (n : ℕ) : ShortComplex ((Compacts U × Compacts D) ⥤ ModuleCat ℚ) :=
  ShortComplex.mk (connectingTransformation p V U D n) (diagonalTransformation p V U D (n+1)) (by
    apply NatTrans.ext
    funext P
    change (connectingTransformation p V U D n).app P ≫ (diagonalTransformation p V U D (n+1)).app P = 0
    rw [show (connectingTransformation p V U D n).app P = _ from
      (fixedIntersectionSegment_f p V (compactOpenImage U P.1) (compactOpenImage D P.2)
        (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).symm,
      show (diagonalTransformation p V U D (n+1)).app P = _ from
      (fixedIntersectionSegment_g p V (compactOpenImage U P.1) (compactOpenImage D P.2)
        (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).symm]
    exact (fixedIntersectionSegment p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).zero)

/-- The actual intersection diagram is exact at every compact support pair. -/
theorem diagramIntersectionSegment_exact_obj (n : ℕ) (P : Compacts U × Compacts D) :
    ((diagramIntersectionSegment p V U D n).map ((evaluation _ _).obj P)).Exact := by
  refine ShortComplex.exact_of_iso (ShortComplex.isoMk (S₁ := fixedIntersectionSegment p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_)
    (fixedIntersectionSegment_exact p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n)
  · dsimp only [Iso.refl_hom]
    erw [Category.id_comp]
  · dsimp only [Iso.refl_hom]
    erw [Category.id_comp, Category.comp_id]
    exact (fixedIntersectionSegment_g p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n).symm

/-- Filtered colimits preserve exactness of the actual compact-pair intersection segment. -/
theorem diagramIntersectionSegment_colimit_exact (n : ℕ) :
    ((diagramIntersectionSegment p V U D n).map colim).Exact :=
  filteredColimit_exact _ (diagramIntersectionSegment_exact_obj p V U D n)

end TernaryPoly.SingularLocalCompactMV
