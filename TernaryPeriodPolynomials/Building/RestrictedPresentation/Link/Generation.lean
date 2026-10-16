module

public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Link.Defs
public import TernaryPeriodPolynomials.Building.BadVertex.LinkFilling
public import TernaryPeriodPolynomials.Building.BadVertex.MixedFilling
public import TernaryPeriodPolynomials.Building.BadVertex.CoherentElimination
public import TernaryPeriodPolynomials.Building.BadVertex.PrismSupport
public import TernaryPeriodPolynomials.Building.BadVertex.ImageSupport

@[expose] public section


/-!
# Lemma A.1, item 4: generation of `H₂(L_b)` by the tetrahedral and prism spheres

Formalized by Claude Sonnet 5.5.
Paper: Lemma A.1.

The library proves that every two-cycle of `L_b` bounds in the Good complex by the reduction
`c = ∂T + R` (`BadVertexCoherentElimination.eliminate_coherent`) followed by a filling of the mixed
cycle `R` (`BadVertexMixedFilling`).  Here the same reduction is run while tracking the
filling: every cap that is used has a boundary which is a prism sphere (coherent part) or a
tetrahedral sphere (mixed part), so that the cycle lies in the span of the two sphere families.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixALink

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.AugmentedFrameComplex
  TernaryPoly.OrientedListChains TernaryPoly.GoodLinkExtraction TernaryPoly.CoherentPrismReduction
  TernaryPoly.BadVertexProjection TernaryPoly.OrientedImageFaceProjection
  TernaryPoly.OrientedImageFaceBoundary TernaryPoly.OrientedImageFaceDecomposition

local instance instDecRLG : DecidableEq RationalLine := Classical.decEq _
local instance instDecRLTwoG : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _
local notation "res" => AugmentedPrismCaps.columnResidue

/-- Every generator is a cycle, hence so is every element of the span. -/
theorem boundary_eq_zero_of_mem_sphereSpan {b : RationalLine} {c : Chain RationalLine}
    (hc : c ∈ sphereSpan b) : boundary c = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    rcases hc with ⟨g,k,l,_,_,_,rfl⟩ | ⟨g,_,_,_,_,rfl⟩
    · exact boundary_squared _
    · exact AugmentedPrismCaps.boundary_prismSphere g
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add,hx,hy,add_zero]
  | smul q x _ h => rw [map_smul,h,smul_zero]

theorem tetra_mem_sphereSpan {b : RationalLine} (g : IntegralGL) (hgb : augmentedLine g 0 = b)
    (hx : Good (xFiber g 0).val) (hy : Good (yFiber g 0).val) (k l : ℤ) :
    tetraSphere g k l ∈ sphereSpan b :=
  Submodule.subset_span (Or.inl ⟨g,k,l,hgb,hx,hy,rfl⟩)

theorem prism_mem_sphereSpan {b : RationalLine} (g : IntegralGL) (hgb : augmentedLine g 0 = b)
    (hb : res g 0 = 0) (hX : res g 1 ≠ 0) (hY : res g 2 ≠ 0) (hZ : res g 1 + res g 2 ≠ 0) :
    AugmentedPrismCaps.prismSphere g ∈ sphereSpan b :=
  Submodule.subset_span (Or.inr ⟨g,hgb,fiberLine_good g hb hX hY hZ 0 0,
    fiberLine_good g hb hX hY hZ 1 0,fiberLine_good g hb hX hY hZ 2 0,rfl⟩)

/-- The residues of the affine bases `affineBasis g p`. -/
theorem affine_residues (g : IntegralGL) (hb : res g 0 = 0) (hX : res g 1 ≠ 0)
    (hY : res g 2 ≠ 0) (hZ : res g 1 + res g 2 ≠ 0) (p : ℤ × ℤ) :
    res (affineBasis g p) 0 = 0 ∧ res (affineBasis g p) 1 ≠ 0 ∧ res (affineBasis g p) 2 ≠ 0 ∧
      res (affineBasis g p) 1 + res (affineBasis g p) 2 ≠ 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · rwa [affineBasis_residue_zero]
  · simpa only [affineBasis_residue_one,hb,zero_mul,zero_add] using hX
  · simpa only [affineBasis_residue_two,hb,zero_mul,zero_add] using hY
  · simpa only [affineBasis_residue_one,affineBasis_residue_two,hb,zero_mul,zero_add] using hZ

theorem swap_residues (g : IntegralGL) (hb : res g 0 = 0) (hX : res g 1 ≠ 0)
    (hY : res g 2 ≠ 0) (hZ : res g 1 + res g 2 ≠ 0) :
    res (g * swapGL) 0 = 0 ∧ res (g * swapGL) 1 ≠ 0 ∧ res (g * swapGL) 2 ≠ 0 ∧
      res (g * swapGL) 1 + res (g * swapGL) 2 ≠ 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [swapGL_residue]; exact hb
  · rw [swapGL_residue]; exact hY
  · rw [swapGL_residue]; exact hX
  · rw [swapGL_residue,swapGL_residue]
    change res g 2 + res g 1 ≠ 0
    rwa [add_comm]

/-- Each prism cap used in the coherent reduction has a prism sphere as its boundary. -/
theorem boundary_neighborCap_mem {b : RationalLine} (g : IntegralGL) (hgb : augmentedLine g 0 = b)
    (hb : res g 0 = 0) (hX : res g 1 ≠ 0) (hY : res g 2 ≠ 0) (hZ : res g 1 + res g 2 ≠ 0)
    (e : IntegerGridExactness.Edge) : boundary (neighborCap g e) ∈ sphereSpan b := by
  unfold neighborCap
  split
  · unfold horizontalCap
    rw [AugmentedPrismCaps.boundary_prismCap]
    obtain ⟨h0,h1,h2,h3⟩ := affine_residues g hb hX hY hZ e.1
    exact prism_mem_sphereSpan _ ((BadVertexPrismSupport.affineBasis_line_zero g e.1).trans hgb)
      h0 h1 h2 h3
  · unfold verticalCap
    rw [map_neg,AugmentedPrismCaps.boundary_prismCap]
    apply (sphereSpan b).neg_mem
    obtain ⟨s0,s1,s2,s3⟩ := swap_residues g hb hX hY hZ
    obtain ⟨h0,h1,h2,h3⟩ := affine_residues (g * swapGL) s0 s1 s2 s3 (e.1.2,e.1.1)
    exact prism_mem_sphereSpan _ ((BadVertexPrismSupport.affineBasis_line_zero _ _).trans
      ((BadVertexMixedCharts.swap_base g).trans hgb)) h0 h1 h2 h3

theorem boundary_capLinear_mem {b : RationalLine} (g : IntegralGL) (hgb : augmentedLine g 0 = b)
    (hb : res g 0 = 0) (hX : res g 1 ≠ 0) (hY : res g 2 ≠ 0) (hZ : res g 1 + res g 2 ≠ 0)
    (a : IntegerGridExactness.C₁) : boundary (capLinear g a) ∈ sphereSpan b := by
  induction a using Finsupp.induction_linear with
  | zero => rw [map_zero,map_zero]; exact (sphereSpan b).zero_mem
  | add a a' ha ha' => rw [map_add,map_add]; exact (sphereSpan b).add_mem ha ha'
  | single e q =>
    rw [capLinear,Finsupp.linearCombination_single,map_smul]
    exact (sphereSpan b).smul_mem q (boundary_neighborCap_mem g hgb hb hX hY hZ e)

/-- The coherent component over the standard base triangle is a sum of prism spheres plus a
literal mixed residual. -/
theorem coherent_component_reduction' (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (hX : res g 1 ≠ 0) (hY : res g 2 ≠ 0) (hZ : res g 1 + res g 2 ≠ 0)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hd : boundary c = 0) :
    ∃ P r : Chain RationalLine, P ∈ sphereSpan (augmentedLine g 0) ∧ r ∈ MixedSpan g ∧
      project (vertex g) BadVertexCoherentBlocks.baseFace c = P + r := by
  obtain ⟨a,ha⟩ := BadVertexCoherentBlocks.project_mem_coherent_range g hbad hc
  have hz : OrientedChainMap.map (vertex g) (coherentLinear g a) = 0 := by
    rw [ha]
    exact BadVertexCoherentProjection.component_projected_zero g hbad hc hd _
  have haug := BadVertexCoherentProjection.augmentation_eq_zero_of_projected g a hz
  have hb : res g 0 = 0 := AugmentedBadFaces.bad_augmentedLine_residue g 0 hbad
  have hred := coherent_reduction g a
  rw [haug,zero_smul,sub_zero] at hred
  exact ⟨_,_,boundary_capLinear_mem g rfl hb hX hY hZ _,residualLinear_mem g _,ha.symm.trans hred⟩

theorem triangle_component_reduction' (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (s : Finset RankTwoAugmentedFrames.RationalLine2) (hs : s.card = 3)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hd : boundary c = 0) (hne : project (vertex g) s c ≠ 0) :
    ∃ P r : Chain RationalLine, P ∈ sphereSpan (augmentedLine g 0) ∧
      r ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 ∧
      r ∈ imageBounded (vertex g) 2 ∧ project (vertex g) s c = P + r := by
  obtain ⟨h,hh,hb,hX,hY,hZ,hface⟩ := BadVertexFaceCharts.coherent_face_chart g hbad s hs hc hne
  have hbad_h : ¬Good (augmentedLine h 0).val := by rwa [hh]
  have hc_h : c ∈ chains (augmentedGoodLink {augmentedLine h 0}) 3 := by rwa [hh]
  obtain ⟨P,r,hP,hr,he⟩ := coherent_component_reduction' h hbad_h hX hY hZ hc_h hd
  have hp := BadVertexProjectionChange.project_change g h hh hbad
    BadVertexCoherentBlocks.baseFace 3 hc
  rw [BadVertexCoherentElimination.baseFace_image,← hface] at hp
  have hrl : r ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 := by
    have hhlink := BadVertexPrismSupport.MixedSpan_le_link h hb hX hY hZ hr
    rwa [hh] at hhlink
  refine ⟨P,r,?_,hrl,BadVertexPrismSupport.MixedSpan_le_imageBounded g h hh hr,hp.trans he⟩
  rwa [hh] at hP

theorem component_reduction' (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hd : boundary c = 0) (s : Finset RankTwoAugmentedFrames.RationalLine2) :
    ∃ P r : Chain RationalLine, P ∈ sphereSpan (augmentedLine g 0) ∧
      r ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 ∧
      r ∈ imageBounded (vertex g) 2 ∧ project (vertex g) s c = P + r := by
  classical
  by_cases hz : project (vertex g) s c = 0
  · exact ⟨0,0,(sphereSpan _).zero_mem,(chains _ _).zero_mem,(imageBounded _ _).zero_mem,
      by simp only [hz,add_zero]⟩
  rcases BadVertexFaceCharts.component_card g hbad s hc hz with hs | hs
  · refine ⟨0,project (vertex g) s c,(sphereSpan _).zero_mem,project_mem_chains _ _ _ _ hc,?_,
      by simp⟩
    simpa only [hs] using project_mem_imageBounded (vertex g) s c
  · exact triangle_component_reduction' g hbad s hs hc hd hz

/-- Every two-cycle of the link is a sum of prism spheres plus a mixed-support cycle. -/
theorem eliminate_coherent' (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hd : boundary c = 0) :
    ∃ P R : Chain RationalLine, P ∈ sphereSpan (augmentedLine g 0) ∧
      R ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 ∧
      R ∈ imageBounded (vertex g) 2 ∧ boundary R = 0 ∧ c = P + R := by
  classical
  obtain ⟨S,hS,_⟩ := exists_decomposition (vertex g) c
  choose P r hP hr him he using component_reduction' g hbad hc hd
  have hT : ∑ s ∈ S, P s ∈ sphereSpan (augmentedLine g 0) :=
    Submodule.sum_mem _ (fun s _ => hP s)
  have hR : ∑ s ∈ S, r s ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 :=
    Submodule.sum_mem _ (fun s _ => hr s)
  have hI : ∑ s ∈ S, r s ∈ imageBounded (vertex g) 2 := Submodule.sum_mem _ (fun s _ => him s)
  have hE : c = ∑ s ∈ S, P s + ∑ s ∈ S, r s := by
    rw [← Finset.sum_add_distrib]
    calc c = ∑ s ∈ S, project (vertex g) s c := hS.symm
      _ = _ := Finset.sum_congr rfl (fun s _ => he s)
  have hD : boundary (∑ s ∈ S, r s) = 0 := by
    have h := congrArg boundary hE
    rw [map_add,hd,boundary_eq_zero_of_mem_sphereSpan hT,zero_add] at h
    exact h.symm
  exact ⟨_,_,hT,hR,hI,hD,hE⟩

/-- A mixed block over the standard base edge with vanishing cross boundary lies in the span of
the tetrahedral spheres. -/
theorem edge_component_in_span_std (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (hX : res g 1 ≠ 0) (hY : res g 2 ≠ 0)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (him : c ∈ imageBounded (vertex g) 2) (hd : boundary c = 0) :
    project (vertex g) BadVertexMixedProjection.baseEdge c ∈ sphereSpan (augmentedLine g 0) := by
  have hb : res g 0 = 0 := AugmentedBadFaces.bad_augmentedLine_residue g 0 hbad
  obtain ⟨z,hz⟩ := BadVertexMixedBlocks.exists_mixed_coefficients g hbad hc
  have him' : c ∈ imageBounded (vertex g) BadVertexMixedProjection.baseEdge.card := by
    rwa [BadVertexMixedBlocks.baseEdge_card]
  have hcross : project (vertex g) BadVertexMixedProjection.baseEdge
      (boundary (BadVertexSquareCaps.mixed g z)) = 0 := by
    rw [hz]
    exact project_boundary_project_eq_zero (vertex g) _ him' hd
  have hz0 := BadVertexMixedProjection.cross_zero_of_projected_boundary g z hcross
  have hcaps : ∀ p : IntegerGridExactness.Vertex, ∃ t : Chain RationalLine,
      t ∈ (sphereSpan (augmentedLine g 0)).comap boundary ∧
      boundary t = OrientedChainMap.map (BadVertexSquareCaps.fiberMap g)
        (boundary (IntegerPathJoinCycles.tetrahedron p)) := by
    intro p
    refine ⟨OrientedChainMap.map (BadVertexSquareCaps.fiberMap g)
      (IntegerPathJoinCycles.tetrahedron p),?_,OrientedChainMap.boundary_map _ _⟩
    rw [Submodule.mem_comap,OrientedChainMap.boundary_map]
    have he : OrientedChainMap.map (BadVertexSquareCaps.fiberMap g)
        (boundary (IntegerPathJoinCycles.tetrahedron p)) = -tetraSphere g p.1 p.2 := by
      rw [← OrientedChainMap.boundary_map]
      simp only [IntegerPathJoinCycles.tetrahedron,map_neg,OrientedChainMap.map_simplex,
        List.map_cons,List.map_nil,BadVertexSquareCaps.fiberMap,IntegerPathJoinCycles.left,
        IntegerPathJoinCycles.right,Sum.elim_inl,Sum.elim_inr,tetraSphere]
    rw [he]
    exact (sphereSpan _).neg_mem (tetra_mem_sphereSpan g rfl
      ((BadVertexSimplexNormalForm.fiberLine_good_iff g hb 0 0).mpr hX)
      ((BadVertexSimplexNormalForm.fiberLine_good_iff g hb 1 0).mpr hY) _ _)
  obtain ⟨t,ht,hdt⟩ := IntegerPathJoinCycles.mapped_mixed_filling (BadVertexSquareCaps.fiberMap g)
    _ hcaps hz0
  rw [← hz]
  change BadVertexSquareCaps.mixed g z ∈ _
  have : BadVertexSquareCaps.mixed g z = boundary t := hdt.symm
  rw [this]
  exact ht

theorem edge_component_in_span (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (s : Finset RankTwoAugmentedFrames.RationalLine2) (hs : s.card = 2)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (him : c ∈ imageBounded (vertex g) 2) (hd : boundary c = 0)
    (hne : project (vertex g) s c ≠ 0) :
    project (vertex g) s c ∈ sphereSpan (augmentedLine g 0) := by
  obtain ⟨h,hh,_,hX,hY,hface⟩ := BadVertexFaceCharts.mixed_face_chart g hbad s hs hc hne
  have hbad_h : ¬Good (augmentedLine h 0).val := by rwa [hh]
  have hc_h : c ∈ chains (augmentedGoodLink {augmentedLine h 0}) 3 := by rwa [hh]
  have him_h : c ∈ imageBounded (vertex h) 2 :=
    BadVertexProjectionChange.imageBounded_change g h hh hbad 3 2 hc him
  have h1 := edge_component_in_span_std h hbad_h hX hY hc_h him_h hd
  have he := BadVertexProjectionChange.project_change g h hh hbad
    BadVertexMixedProjection.baseEdge 3 hc
  rw [BadVertexMixedFilling.baseEdge_image g h hh,← hface] at he
  rw [he]
  rwa [hh] at h1

theorem mixed_cycle_in_span (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    {R : Chain RationalLine} (hR : R ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (him : R ∈ imageBounded (vertex g) 2) (hd : boundary R = 0) :
    R ∈ sphereSpan (augmentedLine g 0) := by
  classical
  obtain ⟨S,hS,_⟩ := exists_decomposition (vertex g) R
  rw [← hS]
  apply Submodule.sum_mem
  intro s _
  by_cases hz : project (vertex g) s R = 0
  · rw [hz]; exact (sphereSpan _).zero_mem
  rcases lt_trichotomy s.card 2 with hs | hs | hs
  · exact (hz (BadVertexImageSupport.small_project_eq_zero g hbad s hs hR)).elim
  · exact edge_component_in_span g hbad s hs hR him hd hz
  · exact (hz (project_eq_zero_of_card_lt (vertex g) him s hs)).elim

/-- **Lemma A.1, generation.** Every two-cycle of `L_b` is a combination of tetrahedral and prism
spheres. -/
theorem generation (b : RationalLine) (hb : ¬Good b.val) {c : Chain RationalLine}
    (hc : c ∈ chains (badLink b) 3) (hd : boundary c = 0) : c ∈ sphereSpan b := by
  obtain ⟨g,rfl⟩ := RationalLineBasis.rationalLine_eq_augmentedLine b
  obtain ⟨P,R,hP,hR,him,hdR,he⟩ := eliminate_coherent' g hb hc hd
  rw [he]
  exact (sphereSpan _).add_mem hP (mixed_cycle_in_span g hb hR him hdR)

end TernaryPeriodPolynomials.Argument.AppendixALink
