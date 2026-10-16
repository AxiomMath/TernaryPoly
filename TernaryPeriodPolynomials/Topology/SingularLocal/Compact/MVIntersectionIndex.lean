module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVIndex

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open TopologicalSpace CategoryTheory

variable {X : Type} [TopologicalSpace X] [T2Space X]

/-- The literal intersection of the two ambient compact supports. -/
def compactIntersection (U V : Opens X) (P : Compacts U × Compacts V) : Compacts X :=
  compactOpenImage U P.1 ⊓ compactOpenImage V P.2

/-- Intersecting the two support images remains inside the actual intersection open set. -/
theorem compactIntersection_subset (U V : Opens X) (P : Compacts U × Compacts V) :
    (compactIntersection U V P : Set X) ⊆ U ⊓ V := by
  intro x hx
  exact ⟨compactOpenImage_subset U P.1 hx.1,compactOpenImage_subset V P.2 hx.2⟩

/-- The actual compact intersection support, regarded as compact in the intersection open set. -/
def compactIntersectionInOpen (U V : Opens X) (P : Compacts U × Compacts V) : Compacts ↥(U ⊓ V) :=
  compactInOpen (U ⊓ V) (compactIntersection U V P) (compactIntersection U V P).isCompact
    (compactIntersection_subset U V P)

/-- The ambient image of the compact intersection is exactly the intersection of the original images. -/
theorem compactIntersectionInOpen_image (U V : Opens X) (P : Compacts U × Compacts V) :
    (compactOpenImage (U ⊓ V) (compactIntersectionInOpen U V P) : Set X) = compactIntersection U V P :=
  compactOpenImage_compactInOpen _ _ _ _

/-- Actual pairwise support inclusions give inclusions of compact supports in the intersection open set. -/
theorem compactIntersectionInOpen_monotone (U V : Opens X) : Monotone (compactIntersectionInOpen U V) := by
  intro P Q h x hx
  exact ⟨Set.image_mono h.1 hx.1,Set.image_mono h.2 hx.2⟩

/-- The actual intersection-support functor on the compact-pair index. -/
def compactIntersectionFunctor (U V : Opens X) : (Compacts U × Compacts V) ⥤ Compacts ↥(U ⊓ V) where
  obj P := compactIntersectionInOpen U V P
  map f := homOfLE (compactIntersectionInOpen_monotone U V ⟨leOfHom f.1,leOfHom f.2⟩)

/-- Every actual compact support in the intersection occurs in the pair-indexed intersection diagram. -/
theorem compactIntersectionInOpen_surjective (U V : Opens X) : Function.Surjective (compactIntersectionInOpen U V) := by
  intro S
  let T := compactOpenImage (U ⊓ V) S
  have hTU : (T : Set X) ⊆ U := fun x hx => (compactOpenImage_subset (U ⊓ V) S hx).1
  have hTV : (T : Set X) ⊆ V := fun x hx => (compactOpenImage_subset (U ⊓ V) S hx).2
  refine ⟨⟨compactInOpen U T T.isCompact hTU,compactInOpen V T T.isCompact hTV⟩,?_⟩
  apply SetLike.coe_injective
  change Subtype.val ⁻¹' ((compactOpenImage U (compactInOpen U T T.isCompact hTU) : Set X) ∩
    (compactOpenImage V (compactInOpen V T T.isCompact hTV) : Set X)) = (S : Set ↥(U ⊓ V))
  rw [compactOpenImage_compactInOpen,compactOpenImage_compactInOpen,Set.inter_self]
  exact Set.preimage_image_eq _ Subtype.val_injective

/-- The compact-intersection functor is final and computes the actual compact-support colimit on the intersection. -/
theorem compactIntersectionFunctor_final (U V : Opens X) : (compactIntersectionFunctor U V).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro S
    obtain ⟨P,hP⟩ := compactIntersectionInOpen_surjective U V S
    exact ⟨P,⟨homOfLE (le_of_eq hP.symm)⟩⟩
  · intro S P f g
    exact ⟨P,𝟙 _,Subsingleton.elim _ _⟩

end TernaryPoly.SingularLocalCompactMV
