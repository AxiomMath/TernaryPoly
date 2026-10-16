module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Apartment.Frames

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryRelativeChains
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains AugmentedChainAction
open GoodRelativeChains
local instance : DecidableEq RationalLine := Classical.decEq _

/-- All actual ambient faces whose rational span is proper. -/
def properAmbient : PreAbstractSimplicialComplex RationalLine where
  faces := {s | s∈ambient ∧ Module.finrank ℚ (faceSpan s)≤2}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(ambient.isRelLowerSet_faces hs.1).1,?_⟩
    intro t hts ht
    exact ⟨(ambient.isRelLowerSet_faces hs.1).2 hts ht,
      (Submodule.finrank_mono (faceSpan_mono hts)).trans hs.2⟩

theorem properAmbient_le_ambient : properAmbient≤ambient := fun _ h => h.1

abbrev AmbientTwo := chains ambient 3
abbrev ProperTwo := chains properAmbient 3

def properInclusion : ProperTwo →ₗ[ℚ] AmbientTwo :=
  Submodule.inclusion (chains_mono properAmbient_le_ambient 3)

def properSubmodule : Submodule ℚ AmbientTwo := properInclusion.range

def nullSubmodule : Submodule ℚ AmbientTwo := properSubmodule ⊔ (differential ambient 3).range

abbrev RelativeBoundaryTwo := AmbientTwo ⧸ nullSubmodule

def quotientMap : AmbientTwo →ₗ[ℚ] RelativeBoundaryTwo := nullSubmodule.mkQ

theorem quotientMap_proper (x : ProperTwo) : quotientMap (properInclusion x)=0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (show properSubmodule≤nullSubmodule from le_sup_left) ⟨x,rfl⟩

theorem quotientMap_boundary (x : chains ambient 4) :
    quotientMap (differential ambient 3 x)=0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (show (differential ambient 3).range≤nullSubmodule from le_sup_right) ⟨x,rfl⟩

theorem allowed_frame_list (g : IntegralGL) (l : List RationalLine)
    (hl : l≠[]) (hs : ∀ L∈l,∃ i : Fin 4,augmentedLine g i=L) : Allowed ambient l := by
  refine Or.inr ⟨(List.toFinset_nonempty_iff l).mpr hl,g,?_⟩
  intro L hL
  exact (AugmentedChainAction.mem_augmentedFrame_iff _ _).mpr (hs L (List.mem_toFinset.mp hL))

theorem triangleList_allowed (g : IntegralGL) : Allowed ambient (triangleList g) := by
  apply allowed_frame_list g _ (by simp [triangleList])
  intro L hL
  simp only [triangleList,List.mem_cons,List.not_mem_nil,or_false] at hL
  rcases hL with rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

def triangle (g : IntegralGL) : AmbientTwo :=
  ⟨simplex (triangleList g),by
    have h := simplex_mem_chains ambient _ (triangleList_allowed g)
    change simplex (triangleList g)∈chains ambient 3 at h
    exact h⟩

theorem triangle_norm_boundary (g : IntegralGL) :
    simplex (triangleList g)+simplex (triangleList (g*ReferenceCoefficientMatrices.a))+
      simplex (triangleList (g*ReferenceCoefficientMatrices.a^2))=
      boundary (simplex (tetrahedronList g))+simplex (coreList g) := by
  have h0 := congrArg (fun x : GoodRelativeChains.GoodTwo => x.val)
    (GoodRelativeChains.triangle_norm_boundary (1 : K))
  change simplex (triangleList 1)+simplex (triangleList (1*ReferenceCoefficientMatrices.a))+
    simplex (triangleList (1*ReferenceCoefficientMatrices.a^2))=
    boundary (simplex (tetrahedronList 1))+simplex (coreList 1) at h0
  have h := congrArg (chainAction g) h0
  simpa only [map_add,←boundary_chainAction,chainAction_simplex,triangleList,tetrahedronList,coreList,
    List.map_cons,List.map_nil,lineAction_augmentedLine,one_mul,mul_one] using h

theorem coreList_finrank (g : IntegralGL) : Module.finrank ℚ (faceSpan (coreList g).toFinset)≤2 := by
  let P := (augmentedLine g 0).val ⊔ (augmentedLine g 1).val
  have hsum : (augmentedLine g 3).val≤P := by
    apply Submodule.span_le.mpr
    rintro v (rfl : v=_)
    change rationalRepresentation g (Pi.single 0 1+Pi.single 1 1)∈P
    rw [map_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hspan : faceSpan (coreList g).toFinset≤P := by
    simp only [coreList,List.toFinset_cons,List.toFinset_nil,faceSpan,
      Finset.sup_insert,Finset.sup_empty,sup_bot_eq]
    exact sup_le le_sup_left (sup_le le_sup_right hsum)
  have hd := Submodule.finrank_add_le_finrank_add_finrank (augmentedLine g 0).val (augmentedLine g 1).val
  rw [(augmentedLine g 0).property,(augmentedLine g 1).property] at hd
  exact (Submodule.finrank_mono hspan).trans hd

theorem triangleList_finrank_ge (g : IntegralGL) :
    3≤Module.finrank ℚ (faceSpan (triangleList g).toFinset) := by
  convert AmbientDependentTriangles.basis_face_finrank_ge g using 1
  apply congrArg (fun s : Finset RationalLine => Module.finrank ℚ (faceSpan s))
  ext L
  simp only [triangleList,List.mem_toFinset]

theorem not_triangleList_of_proper (l : List RationalLine)
    (hd : Module.finrank ℚ (faceSpan l.toFinset)≤2) : ¬∃ g : IntegralGL,triangleList g=l := by
  rintro ⟨g,rfl⟩
  have hh := triangleList_finrank_ge g
  omega

/-- Every nondegenerate ambient tetrahedron is an actual integral augmented frame, in some order. -/
theorem ambient_tetrahedron_perm (l : List RationalLine) (hlen : l.length=4)
    (hn : l.Nodup) (hf : l.toFinset∈ambient) : ∃ g : IntegralGL,l.Perm (tetrahedronList g) := by
  obtain ⟨g,hg⟩ := GoodRelativePresentationFrames.four_face_eq_augmentedFrame l hlen hn hf
  refine ⟨g,List.perm_of_nodup_nodup_toFinset_eq hn ?_ ?_⟩
  · have hn' : ([0,1,3,2] : List (Fin 4)).Nodup := by decide
    exact hn'.map (AugmentedBadFaces.augmentedLine_injective g)
  · rw [hg]
    ext L
    simp only [augmentedFrame,Finset.mem_image,Finset.mem_univ,true_and,
      tetrahedronList,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨3,rfl⟩
      · exact ⟨2,rfl⟩

end TernaryPoly.OrdinaryRelativeChains
