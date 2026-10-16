module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportGluing
public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportSetIso
public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportEndpoint
public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportNaturalityHomology

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- Literal rational homology supported on a subset, relative to its complement. -/
abbrev supportHomology (A : Set X) (k : ℕ) :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).obj (relativeChains Aᶜ)

/-- The literal restriction of relative homology from a larger support to a smaller support. -/
def supportRestriction (A B : Set X) (hAB : A ⊆ B) (k : ℕ) : supportHomology B k ⟶ supportHomology A k :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).map
    (relativeInclusion Bᶜ Aᶜ (Set.compl_subset_compl.mpr hAB))

/-- The open exclusion associated with a closed support. -/
def complementOpen (A : Set X) (hA : IsClosed A) : Opens X := ⟨Aᶜ, hA.isOpen_compl⟩

/-- The actual unsigned restriction pair for two closed supports. -/
def closedPair (A B : Set X) (k : ℕ) :
    supportHomology (A ∪ B) k ⟶ supportHomology A k ⊞ supportHomology B k :=
  biprod.lift (supportRestriction A (A ∪ B) Set.subset_union_left k)
    (supportRestriction B (A ∪ B) Set.subset_union_right k)

/-- The actual difference of restrictions to the intersection of two supports. -/
def closedDifference (A B : Set X) (k : ℕ) :
    supportHomology A k ⊞ supportHomology B k ⟶ supportHomology (A ∩ B) k :=
  biprod.desc (supportRestriction (A ∩ B) A Set.inter_subset_left k)
    (-(supportRestriction (A ∩ B) B Set.inter_subset_right k))

/-- The complement-of-union identity induces an actual isomorphism of relative homology groups. -/
def closedUnionIso (A B : Set X) (k : ℕ) :
    supportHomology (A ∪ B) k ≅ (relativeChains (Aᶜ ∩ Bᶜ)).homology k :=
  relativeHomologySetIso (A ∪ B)ᶜ (Aᶜ ∩ Bᶜ) (Set.compl_union A B) k

/-- The complement-of-intersection identity induces an actual isomorphism of relative homology groups. -/
def closedIntersectionIso (A B : Set X) (k : ℕ) :
    supportHomology (A ∩ B) k ≅ (relativeChains (Aᶜ ∪ Bᶜ)).homology k :=
  relativeHomologySetIso (A ∩ B)ᶜ (Aᶜ ∪ Bᶜ) (Set.compl_inter A B) k

/-- The unsigned literal restriction pair commutes with the complement-of-union isomorphism. -/
theorem closedPair_comm (A B : Set X) (k : ℕ) :
    (closedUnionIso A B k).hom ≫ homologyRestrictionPair Aᶜ Bᶜ k = closedPair A B k := by
  apply biprod.hom_ext <;>
    simp only [closedPair, homologyRestrictionPair, Category.assoc, biprod.lift_fst, biprod.lift_snd]
  · erw [biprod.lift_fst]
    exact relativeHomologySetIso_hom_inclusion (A ∪ B)ᶜ (Aᶜ ∩ Bᶜ) Aᶜ (Set.compl_union A B)
      (Set.compl_subset_compl.mpr Set.subset_union_left) Set.inter_subset_left k
  · erw [biprod.lift_snd]
    exact relativeHomologySetIso_hom_inclusion (A ∪ B)ᶜ (Aᶜ ∩ Bᶜ) Bᶜ (Set.compl_union A B)
      (Set.compl_subset_compl.mpr Set.subset_union_right) Set.inter_subset_right k

/-- The literal difference map commutes with the complement-of-intersection isomorphism. -/
theorem closedDifference_comm (A B : Set X) (k : ℕ) :
    closedDifference A B k ≫ (closedIntersectionIso A B k).hom = homologyRestrictionDifference Aᶜ Bᶜ k := by
  apply biprod.hom_ext' <;>
    simp only [closedDifference, homologyRestrictionDifference, biprod.inl_desc_assoc,
      biprod.inr_desc_assoc, Preadditive.neg_comp]
  · erw [biprod.inl_desc]
    exact homologyInclusion_setIso Aᶜ (A ∩ B)ᶜ (Aᶜ ∪ Bᶜ) (Set.compl_inter A B)
      (Set.compl_subset_compl.mpr Set.inter_subset_left) Set.subset_union_left k
  · erw [biprod.inr_desc]
    exact congrArg Neg.neg (homologyInclusion_setIso Bᶜ (A ∩ B)ᶜ (Aᶜ ∪ Bᶜ) (Set.compl_inter A B)
      (Set.compl_subset_compl.mpr Set.inter_subset_right) Set.subset_union_right k)

/-- The genuine boundary from intersection support to union support, with explicit complement isomorphisms. -/
def closedConnecting (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (k : ℕ) :
    supportHomology (A ∩ B) (k+1) ⟶ supportHomology (A ∪ B) k :=
  (closedIntersectionIso A B (k+1)).hom ≫
    supportConnecting (complementOpen A hA) (complementOpen B hB) k ≫ (closedUnionIso A B k).inv

end TernaryPoly.RationalRelativeSupport
