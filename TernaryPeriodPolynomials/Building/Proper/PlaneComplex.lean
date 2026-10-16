module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.FrameComplex
public import TernaryPeriodPolynomials.Building.OrientedChain.ListChains

@[expose] public section

noncomputable section
namespace TernaryPoly.ProperPlaneComplex
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains

/-- Actual Good augmented faces contained in one specified rational subspace. -/
def planeComplex (P : RationalSubspace) : PreAbstractSimplicialComplex RationalLine where
  faces := {s | s ∈ good ∧ ∀ L ∈ s, L.val ≤ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(good.isRelLowerSet_faces hs.1).1,?_⟩
    intro t hts ht
    exact ⟨(good.isRelLowerSet_faces hs.1).2 hts ht,fun L hL => hs.2 L (hts hL)⟩

theorem planeComplex_le_good (P : RationalSubspace) : planeComplex P ≤ good := fun _ h => h.1

theorem planeComplex_faceSpan_le (P : RationalSubspace) (s : Finset RationalLine)
    (hs : s ∈ planeComplex P) : faceSpan s ≤ P := Finset.sup_le hs.2

/-- A genuine plane carries only proper-span Good faces. -/
theorem planeComplex_le_properGood (P : RationalSubspace) (hP : Module.finrank ℚ P ≤ 2) :
    planeComplex P ≤ properGood := by
  intro s hs
  exact ⟨hs.1,(Submodule.finrank_mono (planeComplex_faceSpan_le P s hs)).trans hP⟩

/-- The precise per-plane H1 input, stated on actual finite Good simplex chains. -/
def PerPlaneFilling : Prop :=
  ∀ P : RationalSubspace, Module.finrank ℚ P = 2 →
    ∀ c : Chain RationalLine, c ∈ chains (planeComplex P) 2 → boundary c = 0 →
      ∃ b : Chain RationalLine, b ∈ chains (planeComplex P) 3 ∧ boundary b = c

end TernaryPoly.ProperPlaneComplex
