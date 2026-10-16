module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVFixedNaturality
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVIntersectionIndex
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Cohomology

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalSupport

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [T2Space B]
  (U D : Opens B)

/-- The first compact support in a pair, viewed in the actual ambient space. -/
def leftSupportOrder : (Compacts U × Compacts D) →o Compacts B where
  toFun P := compactOpenImage U P.1
  monotone' _ _ h := compactOpenImage_monotone U h.1

/-- The second compact support in a pair, viewed in the actual ambient space. -/
def rightSupportOrder : (Compacts U × Compacts D) →o Compacts B where
  toFun P := compactOpenImage D P.2
  monotone' _ _ h := compactOpenImage_monotone D h.2

/-- The literal ambient intersection of a pair of compact supports, as an order map. -/
def intersectionSupportOrder : (Compacts U × Compacts D) →o Compacts B where
  toFun P := compactIntersection U D P
  monotone' _ _ h := inf_le_inf (compactOpenImage_monotone U h.1) (compactOpenImage_monotone D h.2)

/-- An actual monotone support assignment gives a functor on the product index category. -/
def pairSupportFunctor (s : (Compacts U × Compacts D) →o Compacts B) :
    (Compacts U × Compacts D) ⥤ Compacts B where
  obj P := s P
  map f := homOfLE (s.monotone ⟨leOfHom f.1,leOfHom f.2⟩)

/-- The actual support-cohomology diagram associated to a compact support assignment. -/
def pairSupportCohomology (s : (Compacts U × Compacts D) →o Compacts B) (n : ℕ) :
    (Compacts U × Compacts D) ⥤ ModuleCat ℚ :=
  pairSupportFunctor U D s ⋙ compactCohomologyDiagram p V n

/-- Actual intersection-support cohomology over the genuine compact-pair index. -/
abbrev intersectionDiagram (n : ℕ) := pairSupportCohomology p V U D (intersectionSupportOrder U D) n

/-- Actual left-support cohomology over the genuine compact-pair index. -/
abbrev leftDiagram (n : ℕ) := pairSupportCohomology p V U D (leftSupportOrder U D) n

/-- Actual right-support cohomology over the genuine compact-pair index. -/
abbrev rightDiagram (n : ℕ) := pairSupportCohomology p V U D (rightSupportOrder U D) n

/-- Actual union-support cohomology over the genuine compact-pair index. -/
abbrev unionDiagram (n : ℕ) := pairSupportCohomology p V U D (compactUnion U D) n

/-- The actual pair of support-cohomology groups, with their genuine enlargement maps. -/
def pairDiagram (n : ℕ) : (Compacts U × Compacts D) ⥤ ModuleCat ℚ where
  obj P := (leftDiagram p V U D n).obj P ⊞ (rightDiagram p V U D n).obj P
  map f := biprod.map ((leftDiagram p V U D n).map f) ((rightDiagram p V U D n).map f)
  map_id P := by apply biprod.hom_ext <;> simp
  map_comp f g := by apply biprod.hom_ext <;> simp only [Functor.map_comp, Category.assoc, biprod.map_fst, biprod.map_snd, biprod.map_fst_assoc, biprod.map_snd_assoc]

/-- The genuine signed diagonal is a natural transformation of the actual compact-support diagrams. -/
def diagonalTransformation (n : ℕ) : intersectionDiagram p V U D n ⟶ pairDiagram p V U D n where
  app P := fixedDiagonal p V (compactOpenImage U P.1) (compactOpenImage D P.2) n
  naturality {P Q} f := fixedDiagonal_natural p V
    (compactOpenImage U P.1) (compactOpenImage D P.2) (compactOpenImage U Q.1) (compactOpenImage D Q.2)
    (Set.image_mono (leOfHom f.1)) (Set.image_mono (leOfHom f.2)) n

/-- The genuine support sum is a natural transformation of the actual compact-support diagrams. -/
def sumTransformation (n : ℕ) : pairDiagram p V U D n ⟶ unionDiagram p V U D n where
  app P := fixedSum p V (compactOpenImage U P.1) (compactOpenImage D P.2) n
  naturality {P Q} f := (fixedSum_natural p V
    (compactOpenImage U P.1) (compactOpenImage D P.2) (compactOpenImage U Q.1) (compactOpenImage D Q.2)
    (Set.image_mono (leOfHom f.1)) (Set.image_mono (leOfHom f.2)) n).symm

/-- The actual connecting maps are a natural transformation over compact support pairs. -/
def connectingTransformation (n : ℕ) : unionDiagram p V U D n ⟶ intersectionDiagram p V U D (n+1) where
  app P := fixedConnecting p V (compactOpenImage U P.1) (compactOpenImage D P.2)
    (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n
  naturality {P Q} f := (fixedConnecting_natural p V
    (compactOpenImage U P.1) (compactOpenImage D P.2) (compactOpenImage U Q.1) (compactOpenImage D Q.2)
    (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed
    (compactOpenImage U Q.1).isCompact.isClosed (compactOpenImage D Q.2).isCompact.isClosed
    (Set.image_mono (leOfHom f.1)) (Set.image_mono (leOfHom f.2)) n).symm

end TernaryPoly.SingularLocalCompactMV
