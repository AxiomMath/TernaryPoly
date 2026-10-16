module

public import TernaryPeriodPolynomials.Building.BadVertex.SimplexNormalForm
public import TernaryPeriodPolynomials.Building.OrientedChain.ImageFaceBoundary

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexImageSupport
open ModThreeGoodAction AugmentedFrameComplex GoodLinkExtraction
open OrientedListChains OrientedImageFaceProjection OrientedImageFaceBoundary
open BadVertexSimplexNormalForm
local instance : DecidableEq RationalLine := Classical.decEq _
local instance : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _

/-- Every local projected complement has two or three distinct actual quotient lines. -/
theorem normal_image_card (q : RankTwoAugmentedFrames.IntegralGL) (i : Fin 4) :
    2 ≤ (List.ofFn (fun j => RankTwoAugmentedFrames.augmentedLine q (normalFiber i j))).toFinset.card := by
  have hinj := RankTwoAugmentedFrames.augmentedLine_injective q
  have h01 : RankTwoAugmentedFrames.augmentedLine q 0 ≠ RankTwoAugmentedFrames.augmentedLine q 1 :=
    fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)
  have h02 : RankTwoAugmentedFrames.augmentedLine q 0 ≠ RankTwoAugmentedFrames.augmentedLine q 2 :=
    fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h)
  have h12 : RankTwoAugmentedFrames.augmentedLine q 1 ≠ RankTwoAugmentedFrames.augmentedLine q 2 :=
    fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h)
  fin_cases i <;> simp [normalFiber,List.ofFn_succ,h01,h02,h12]

/-- An actual nondegenerate link triangle never lies above a single base vertex. -/
theorem triangle_image_card (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (l : List RationalLine) (hlen : l.length = 3) (hn : l.Nodup)
    (hl : l.toFinset ∈ augmentedGoodLink {augmentedLine g 0}) :
    2 ≤ (imageFace (BadVertexProjection.vertex g) l).card := by
  obtain ⟨h,i,hi,_,hp,_⟩ := triangle_projected_chart g hbad l hlen hn hl
  have hc := normal_image_card
    (BadVertexProjection.lowerGL (g⁻¹ * (h * BadVertexProjection.templateChange i))
      (BadVertexProjection.first_column_lower_zero g (h * BadVertexProjection.templateChange i)
        ((BadVertexProjection.templateChange_line h i).trans hi))) i
  convert hc using 1
  congr 1
  ext L
  simpa only [imageFace,List.mem_toFinset] using (hp.mem_iff (a := L))

/-- Every two-chain in the actual link has zero component above any base set of size below two. -/
theorem small_project_eq_zero (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (s : Finset RankTwoAugmentedFrames.RationalLine2) (hs : s.card < 2)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3) :
    project (BadVertexProjection.vertex g) s c = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases hn : l.Nodup
    · have hl' : l.toFinset ∈ augmentedGoodLink {augmentedLine g 0} :=
        hl.resolve_left (fun he => by subst l; simp at hlen)
      have hb := triangle_image_card g hbad l hlen hn hl'
      have he : imageFace (BadVertexProjection.vertex g) l ≠ s := by
        intro h
        rw [h] at hb
        omega
      rw [project_simplex,ite_eq_right he]
    · rw [simplex_eq_zero_of_not_nodup l hn,map_zero]
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => rw [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => rw [map_smul,ih,smul_zero]

/-- The three-vertex grading gives the exact upper bound on projected support. -/
theorem link_two_imageBounded (g : IntegralGL) {c : Chain RationalLine}
    (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3) :
    c ∈ imageBounded (BadVertexProjection.vertex g) 3 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,_,rfl⟩ := hc
    apply simplex_mem_imageBounded
    exact (List.toFinset_card_le _).trans_eq ((List.length_map _).trans hlen)
  | zero => exact (imageBounded _ _).zero_mem
  | add c d hc hd ihc ihd => exact (imageBounded _ _).add_mem ihc ihd
  | smul q c hc ih => exact (imageBounded _ _).smul_mem q ih

end TernaryPoly.BadVertexImageSupport
