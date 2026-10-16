module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVRefinement
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Products.Bifunctor

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open TopologicalSpace CategoryTheory

variable {X : Type} [TopologicalSpace X]

/-- Actual compact support in an open subset, viewed inside the ambient space. -/
def compactOpenImage (U : Opens X) (K : Compacts U) : Compacts X :=
  K.map (Subtype.val : U → X) continuous_subtype_val

/-- The image of a genuine compact support remains inside its open subset. -/
theorem compactOpenImage_subset (U : Opens X) (K : Compacts U) :
    (compactOpenImage U K : Set X) ⊆ U := by
  rintro x ⟨y,_,rfl⟩
  exact y.property

/-- Actual support inclusions stay inclusions under the ambient compact-support map. -/
theorem compactOpenImage_monotone (U : Opens X) : Monotone (compactOpenImage U) :=
  fun _ _ h => Set.image_mono h

/-- The finite support-pair index maps to ambient compact support by literal union. -/
def compactUnion (U V : Opens X) : Compacts U × Compacts V →o Compacts X where
  toFun P := compactOpenImage U P.1 ⊔ compactOpenImage V P.2
  monotone' _ _ h := sup_le_sup (compactOpenImage_monotone U h.1) (compactOpenImage_monotone V h.2)

/-- The union operation gives the actual functor on compact-support indices. -/
def compactUnionFunctor (U V : Opens X) : (Compacts U × Compacts V) ⥤ Compacts X where
  obj P := compactUnion U V P
  map f := homOfLE ((compactUnion U V).monotone ⟨leOfHom f.1,leOfHom f.2⟩)

/-- Pairs of genuine compact supports form a filtered index category. -/
theorem compactPair_isFiltered (U V : Opens X) : IsFiltered (Compacts U × Compacts V) := inferInstance

variable [T2Space X] [LocallyCompactSpace X]

omit [T2Space X] [LocallyCompactSpace X] in
/-- Restriction of an ambient compact support contained in an open subset preserves its literal image. -/
theorem compactOpenImage_compactInOpen (U : Opens X) (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U) :
    (compactOpenImage U (compactInOpen U K hK hKU) : Set X) = K := by
  apply Set.image_preimage_eq_of_subset
  exact fun x hx => ⟨⟨x,hKU hx⟩,rfl⟩

/-- Every ambient compact support is exactly a union from the two-piece compact-support index. -/
theorem compactUnion_surjective (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    Function.Surjective (compactUnion U V) := by
  intro S
  obtain ⟨K,L,hK,hL,_,_,hKU,hLV,hKL⟩ := compact_binary_refinement U V hUV S S.isCompact
  refine ⟨⟨compactInOpen U K hK hKU,compactInOpen V L hL hLV⟩,?_⟩
  apply SetLike.coe_injective
  change (compactOpenImage U (compactInOpen U K hK hKU) : Set X) ∪
    (compactOpenImage V (compactInOpen V L hL hLV) : Set X) = S
  rw [compactOpenImage_compactInOpen,compactOpenImage_compactInOpen,hKL]

/-- The literal compact union functor is final, so it computes the genuine ambient compact-support colimit. -/
theorem compactUnionFunctor_final (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (compactUnionFunctor U V).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro S
    obtain ⟨P,hP⟩ := compactUnion_surjective U V hUV S
    exact ⟨P,⟨homOfLE (le_of_eq hP.symm)⟩⟩
  · intro S P f g
    exact ⟨P,𝟙 _,Subsingleton.elim _ _⟩

end TernaryPoly.SingularLocalCompactMV
