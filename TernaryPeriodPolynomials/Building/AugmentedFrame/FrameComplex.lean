module

public import TernaryPeriodPolynomials.Building.ModThreeGoodAction
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.AugmentedFrameComplex
open ModThreeGoodAction

/-- Rational line vertices, with their actual dimension condition. -/
abbrev RationalLine := {L : RationalSubspace // Module.finrank ℚ L = 1}

/-- The rational line spanned by an actual nonzero vector. -/
def vectorLine (v : Space) (hv : v ≠ 0) : RationalLine :=
  ⟨Submodule.span ℚ {v},finrank_span_singleton hv⟩

/-- The standard augmented basis vectors, with the signed core represented by e0+e1. -/
def template : Fin 4 → Space :=
  ![Pi.single 0 1,Pi.single 1 1,Pi.single 2 1,Pi.single 0 1 + Pi.single 1 1]

theorem template_ne_zero (i : Fin 4) : template i ≠ 0 := by
  intro h
  fin_cases i
  · have he := congrFun h 0
    norm_num [template] at he
  · have he := congrFun h 1
    norm_num [template] at he
  · have he := congrFun h 2
    norm_num [template] at he
  · have he := congrFun h 0
    norm_num [template] at he

/-- The four actual rational lines in an arbitrary integral augmented basis. -/
def augmentedLine (g : IntegralGL) (i : Fin 4) : RationalLine :=
  vectorLine (rationalRepresentation g (template i))
    (fun h => template_ne_zero i ((rationalRepresentation g).injective
      (h.trans (map_zero (rationalRepresentation g)).symm)))

/-- The genuine finite augmented frame, parametrized by an invertible integer matrix. -/
def augmentedFrame (g : IntegralGL) : Finset RationalLine :=
  Finset.univ.image (augmentedLine g)

/-- Nonempty faces are exactly subsets of actual integral augmented frames. -/
def IsFace (s : Finset RationalLine) : Prop :=
  s.Nonempty ∧ ∃ g : IntegralGL, s ⊆ augmentedFrame g

/-- The actual augmented-frame precomplex. Singleton fullness is a separate lattice theorem. -/
def ambient : PreAbstractSimplicialComplex RationalLine where
  faces := {s | IsFace s}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro t hts ht
    exact ⟨ht,hs.2.imp (fun _ hg => hts.trans hg)⟩

/-- The full subcomplex on vertices satisfying the literal mod-three lattice predicate. -/
def good : PreAbstractSimplicialComplex RationalLine where
  faces := {s | IsFace s ∧ ∀ L ∈ s, Good L.val}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1.1,?_⟩
    intro t hts ht
    exact ⟨⟨ht,hs.1.2.imp (fun _ hg => hts.trans hg)⟩,
      fun L hL => hs.2 L (hts hL)⟩

theorem good_le_ambient : good ≤ ambient := fun _ h => h.1

/-- Every actual integral augmented frame is an ambient face. -/
theorem augmentedFrame_mem (g : IntegralGL) : augmentedFrame g ∈ ambient := by
  refine ⟨?_,g,Finset.Subset.refl _⟩
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

/-- Every nonempty subset of a displayed actual frame is an ambient face. -/
theorem subset_augmentedFrame_mem (g : IntegralGL) {s : Finset RationalLine}
    (hs : s.Nonempty) (hsub : s ⊆ augmentedFrame g) : s ∈ ambient := ⟨hs,g,hsub⟩

/-- The actual rational span of a finite set of line vertices. -/
def faceSpan (s : Finset RationalLine) : RationalSubspace := s.sup Subtype.val

theorem faceSpan_mono {s t : Finset RationalLine} (h : s ⊆ t) : faceSpan s ≤ faceSpan t :=
  Finset.sup_mono h

/-- Proper-span faces form a genuine subcomplex of the good augmented complex. -/
def properGood : PreAbstractSimplicialComplex RationalLine where
  faces := {s | s ∈ good ∧ Module.finrank ℚ (faceSpan s) ≤ 2}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(good.isRelLowerSet_faces hs.1).1,?_⟩
    intro t hts ht
    exact ⟨(good.isRelLowerSet_faces hs.1).2 hts ht,
      (Submodule.finrank_mono (faceSpan_mono hts)).trans hs.2⟩

theorem properGood_le_good : properGood ≤ good := fun _ h => h.1

end TernaryPoly.AugmentedFrameComplex
