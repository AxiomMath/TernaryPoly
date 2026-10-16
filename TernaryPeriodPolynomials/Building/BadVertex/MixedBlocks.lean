module

public import TernaryPeriodPolynomials.Building.BadVertex.SimplexNormalForm
public import TernaryPeriodPolynomials.Building.BadVertex.CoherentCharts
public import TernaryPeriodPolynomials.Building.BadVertex.MixedCharts
public import TernaryPeriodPolynomials.Building.BadVertex.MixedProjection
public import TernaryPeriodPolynomials.Building.OrientedChain.ImageFaceBoundary

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexMixedBlocks
open ModThreeGoodAction AugmentedFrameComplex GoodLinkExtraction OrientedListChains
open CoherentPrismReduction BadVertexProjection BadVertexFibers BadVertexMixedCharts
open BadVertexSimplexNormalForm BadVertexCoherentCharts BadVertexMixedProjection
open OrientedImageFaceProjection OrientedImageFaceBoundary

local instance : DecidableEq RationalLine := Classical.decEq _
local instance : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _

/-- The fixed quotient edge has exactly two vertices. -/
theorem baseEdge_card : baseEdge.card = 2 := by
  simp [baseEdge,base_vertices_distinct]

/-- Set equality of two unordered endpoint pairs permits only alignment or swapping. -/
theorem pair_alignment {W : Type*} [DecidableEq W] (a b x y : W)
    (he : ({a,b} : Finset W) = {x,y}) :
    (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  apply Set.pair_eq_pair_iff.mp
  simpa only [Finset.coe_insert,Finset.coe_singleton] using
    congrArg (fun s : Finset W => (s : Set W)) he

/-- The quotient of a local affine fiber is independent of its integer coordinate. -/
theorem vertex_fiber_origin (g h : IntegralGL) (hh : augmentedLine h 0 = augmentedLine g 0)
    (i : Fin 3) (k : ℤ) : vertex g (fiberLine h i k) = vertex g (fiberLine h i 0) := by
  rw [fiber_projection g h hh,fiber_projection g h hh]

/-- An adapted coherent triple has three distinct actual quotient vertices. -/
theorem coherent_image_card (g h : IntegralGL) (hh : augmentedLine h 0 = augmentedLine g 0) :
    (imageFace (vertex g) [xFiber h 0,yFiber h 0,zFiber h 0]).card = 3 := by
  let q := lowerGL (g⁻¹ * h) (first_column_lower_zero g h hh)
  have hinj := RankTwoAugmentedFrames.augmentedLine_injective q
  have h01 : RankTwoAugmentedFrames.augmentedLine q 0 ≠ RankTwoAugmentedFrames.augmentedLine q 1 :=
    fun he => (by decide : (0 : Fin 3) ≠ 1) (hinj he)
  have h02 : RankTwoAugmentedFrames.augmentedLine q 0 ≠ RankTwoAugmentedFrames.augmentedLine q 2 :=
    fun he => (by decide : (0 : Fin 3) ≠ 2) (hinj he)
  have h12 : RankTwoAugmentedFrames.augmentedLine q 1 ≠ RankTwoAugmentedFrames.augmentedLine q 2 :=
    fun he => (by decide : (1 : Fin 3) ≠ 2) (hinj he)
  simp only [imageFace,List.map_cons,List.map_nil,xFiber,yFiber,zFiber,fiber_projection g h hh]
  change ([(RankTwoAugmentedFrames.augmentedLine q 0),
    RankTwoAugmentedFrames.augmentedLine q 1,RankTwoAugmentedFrames.augmentedLine q 2].toFinset).card = 3
  simp [h01,h02,h12]

/-- A mixed local triangle projects onto precisely its two actual quotient endpoints. -/
theorem horizontal_imageFace (g h : IntegralGL) (hh : augmentedLine h 0 = augmentedLine g 0)
    (k l : ℤ) : imageFace (vertex g) [xFiber h k,xFiber h (k+1),yFiber h l] =
      {vertex g (xFiber h 0),vertex g (yFiber h 0)} := by
  simp only [imageFace,List.map_cons,List.map_nil,xFiber,yFiber,vertex_fiber_origin g h hh]
  simp

/-- A projected endpoint-pair equality determines the ordered or reversed chart comparison. -/
theorem compatible_or_swapped (g h : IntegralGL) (hh : augmentedLine h 0 = augmentedLine g 0)
    (he : {vertex g (xFiber h 0),vertex g (yFiber h 0)} = baseEdge) :
    Compatible g h ∨
      (vertex g (xFiber h 0) = vertex g (yFiber g 0) ∧
        vertex g (yFiber h 0) = vertex g (xFiber g 0)) := by
  have he' : ({vertex g (xFiber h 0),vertex g (yFiber h 0)} :
      Finset RankTwoAugmentedFrames.RationalLine2) =
      {vertex g (xFiber g 0),vertex g (yFiber g 0)} := by
    simpa only [xFiber,yFiber,prism_fiber_vertex,baseEdge] using he
  rcases pair_alignment _ _ _ _ he' with hp | hp
  · exact Or.inl ⟨hh,hp⟩
  · exact Or.inr hp

/-- Exact fixed-edge support puts every literal nondegenerate link triangle in the fixed
integer-grid mixed range. The coherent alternative is ruled out by its three quotient vertices. -/
theorem triangle_mem_mixed_range (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (l : List RationalLine) (hlen : l.length = 3) (hn : l.Nodup)
    (hl : l.toFinset ∈ augmentedGoodLink {augmentedLine g 0})
    (he : imageFace (vertex g) l = baseEdge) :
    simplex l ∈ LinearMap.range (BadVertexSquareCaps.mixed g) := by
  obtain ⟨h,hh,_,_,_,hc⟩ := triangle_normal_form _ hbad l hlen hn hl
  rcases hc with ⟨_,hp⟩ | ⟨k,_,hp⟩
  · have he' : imageFace (vertex g) [xFiber h 0,yFiber h 0,zFiber h 0] = baseEdge :=
      (imageFace_perm (vertex g) hp).symm.trans he
    have hcard := coherent_image_card g h hh
    rw [he',baseEdge_card] at hcard
    exact (by decide : (2 : ℕ) ≠ 3) hcard |>.elim
  · have hep : {vertex g (xFiber h 0),vertex g (yFiber h 0)} = baseEdge :=
      (horizontal_imageFace g h hh k 0).symm.trans ((imageFace_perm (vertex g) hp).symm.trans he)
    apply simplex_mem_of_perm (LinearMap.range (BadVertexSquareCaps.mixed g)) hp
    rcases compatible_or_swapped g h hh hep with hc | hc
    · exact horizontal_mem_range g h hc k 0
    · exact horizontal_mem_range_swapped g h ⟨hh,hc⟩ k 0

/-- Actual finite range lifting for the exact base-edge component of every Good link two-chain. -/
theorem project_mem_mixed_range (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3) :
    project (vertex g) baseEdge c ∈ LinearMap.range (BadVertexSquareCaps.mixed g) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases hn : l.Nodup
    · have hf : l.toFinset ∈ augmentedGoodLink {augmentedLine g 0} :=
        hl.resolve_left (fun he => by subst l; simp at hlen)
      by_cases he : imageFace (vertex g) l = baseEdge
      · rw [project_simplex,ite_eq_left he]
        exact triangle_mem_mixed_range g hbad l hlen hn hf he
      · rw [project_simplex,ite_eq_right he]
        exact (LinearMap.range (BadVertexSquareCaps.mixed g)).zero_mem
    · rw [simplex_eq_zero_of_not_nodup l hn,map_zero]
      exact (LinearMap.range (BadVertexSquareCaps.mixed g)).zero_mem
  | zero => simpa only [map_zero] using (LinearMap.range (BadVertexSquareCaps.mixed g)).zero_mem
  | add c d hc hd ihc ihd =>
    simpa only [map_add] using (LinearMap.range (BadVertexSquareCaps.mixed g)).add_mem ihc ihd
  | smul q c hc ih =>
    simpa only [map_smul] using (LinearMap.range (BadVertexSquareCaps.mixed g)).smul_mem q ih

/-- An explicit finitely supported coefficient witness for each actual exact edge component. -/
theorem exists_mixed_coefficients (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3) :
    ∃ z : IntegerGridExactness.C₁, BadVertexSquareCaps.mixed g z =
      project (vertex g) baseEdge c := project_mem_mixed_range g hbad hc

/-- Every exact fixed-edge component of an actual two-image-bounded Good link cycle has
an actual Good4 filling. Only its projected cross boundary is separated; no block-cycle
assumption is introduced. -/
theorem edge_component_good_filling (g : IntegralGL)
    (hbad : ¬Good (augmentedLine g 0).val)
    (hX : AugmentedBadFaces.columnResidue g 1 ≠ 0)
    (hY : AugmentedBadFaces.columnResidue g 2 ≠ 0)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (him : c ∈ imageBounded (vertex g) 2) (hd : boundary c = 0) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧
      boundary t = project (vertex g) baseEdge c := by
  obtain ⟨z,hz⟩ := exists_mixed_coefficients g hbad hc
  have him' : c ∈ imageBounded (vertex g) baseEdge.card := by
    rwa [baseEdge_card]
  have hcross : project (vertex g) baseEdge (boundary (BadVertexSquareCaps.mixed g z)) = 0 := by
    rw [hz]
    exact project_boundary_project_eq_zero (vertex g) baseEdge him' hd
  obtain ⟨t,ht,hdt⟩ := good_filling_of_projected_boundary g
    (AugmentedBadFaces.bad_augmentedLine_residue g 0 hbad) hX hY z hcross
  exact ⟨t,ht,hdt.trans hz⟩

end TernaryPoly.BadVertexMixedBlocks
