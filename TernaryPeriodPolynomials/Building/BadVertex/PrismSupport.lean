module

public import TernaryPeriodPolynomials.Building.BadVertex.CoherentProjection
public import TernaryPeriodPolynomials.Building.BadVertex.CoherentCharts
public import TernaryPeriodPolynomials.Building.BadVertex.SimplexNormalForm
public import TernaryPeriodPolynomials.Building.OrientedChain.ImageFaceBoundary

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexPrismSupport
open ModThreeGoodAction AugmentedFrameComplex GoodLinkExtraction OrientedListChains
open CoherentPrismReduction BadVertexProjection BadVertexCoherentCharts
open BadVertexSimplexNormalForm OrientedImageFaceProjection OrientedImageFaceBoundary

local instance : DecidableEq RationalLine := Classical.decEq _
local instance : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _
local notation "residue" => AugmentedPrismCaps.columnResidue

/-- The displayed mixed basis preserves the actual first-column line. -/
theorem mixedGL_line_zero (g : IntegralGL) (i j : Fin 3) (hij : i ≠ j) (k l : ℤ) :
    augmentedLine (g * mixedGL i j hij k l) 0 = augmentedLine g 0 := by
  have hv : (mixedGL i j hij k l).val.mulVec (Pi.single 0 1) = Pi.single 0 1 := by
    change (mixedMatrix i j k l).mulVec (Pi.single 0 1) = _
    rw [Matrix.mulVec_single_one]
    funext r
    fin_cases r <;> rfl
  have he : template 0 = rationalVector (Pi.single 0 1) := by
    funext r
    fin_cases r <;> rfl
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * mixedGL i j hij k l) (template 0)} = _
  rw [map_mul,LinearEquiv.mul_apply,he,← rationalVector_mulVec,hv]
  rfl

/-- The full actual augmented frame adjoins exactly the distinguished vertex to a mixed face. -/
theorem mixedGL_frame (g : IntegralGL) (i j : Fin 3) (hij : i ≠ j) (k l : ℤ) :
    augmentedFrame (g * mixedGL i j hij k l) =
      {augmentedLine g 0,fiberLine g i k,fiberLine g i (k+1),fiberLine g j l} := by
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide +kernel
  rw [augmentedFrame,hu]
  simp only [Finset.image_insert,Finset.image_singleton,mixedGL_line_zero,mixedGL_line_one,
    mixedGL_line_two,mixedGL_line_three]
  ext L
  simp only [Finset.mem_insert,Finset.mem_singleton]
  tauto

/-- Literal adjacent-fiber mixed triangles remain in the original Good link. -/
theorem mixed_face_link (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (hY : residue g 2 ≠ 0)
    (hZ : residue g 1 + residue g 2 ≠ 0)
    (i j : Fin 3) (hij : i ≠ j) (k l : ℤ) :
    {fiberLine g i k,fiberLine g i (k+1),fiberLine g j l} ∈
      augmentedGoodLink {augmentedLine g 0} := by
  refine ⟨⟨by simp,?_⟩,(mixed_face_good g hb hX hY hZ i j hij k l).2⟩
  rw [Finset.singleton_union,← mixedGL_frame g i j hij k l]
  exact augmentedFrame_mem _

/-- The independently defined mixed generator has an actual three-vertex list in some order. -/
theorem mixedGenerator_list (g : IntegralGL) {c : Chain RationalLine} (hc : MixedGenerator g c) :
    ∃ (i j : Fin 3) (k l : ℤ) (xs : List RationalLine), i ≠ j ∧ c = simplex xs ∧
      xs.length = 3 ∧ xs.toFinset = {fiberLine g i k,fiberLine g i (k+1),fiberLine g j l} := by
  obtain ⟨i,j,k,l,hij,hc⟩ := hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨i,j,k,l,_,hij,rfl,rfl,?_⟩
    ext L
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,
      Finset.mem_insert,Finset.mem_singleton]
    all_goals tauto

theorem mixedGenerator_mem_link (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (hY : residue g 2 ≠ 0)
    (hZ : residue g 1 + residue g 2 ≠ 0)
    {c : Chain RationalLine} (hc : MixedGenerator g c) :
    c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 := by
  obtain ⟨i,j,k,l,xs,hij,rfl,hlen,he⟩ := mixedGenerator_list g hc
  have hf : xs.toFinset ∈ augmentedGoodLink {augmentedLine g 0} :=
    he.symm ▸ mixed_face_link g hb hX hY hZ i j hij k l
  have hm := simplex_mem_chains (augmentedGoodLink {augmentedLine g 0}) xs (Or.inr hf)
  rwa [hlen] at hm

/-- Every mixed residual is still supported in the actual bad-vertex link. -/
theorem MixedSpan_le_link (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (hY : residue g 2 ≠ 0)
    (hZ : residue g 1 + residue g 2 ≠ 0) :
    MixedSpan g ≤ chains (augmentedGoodLink {augmentedLine g 0}) 3 := by
  apply Submodule.span_le.mpr
  exact fun _ hc => mixedGenerator_mem_link g hb hX hY hZ hc

/-- Finite image faces may be computed from the actual finite vertex set of a list. -/
theorem imageFace_eq_image {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (xs : List V) : imageFace f xs = xs.toFinset.image f := by
  ext w
  simp [imageFace]

/-- A mixed triangle uses only two quotient vertices in every adapted reference basis. -/
theorem mixedGenerator_mem_imageBounded (g₀ g : IntegralGL)
    (hh : augmentedLine g 0 = augmentedLine g₀ 0)
    {c : Chain RationalLine} (hc : MixedGenerator g c) :
    c ∈ imageBounded (vertex g₀) 2 := by
  obtain ⟨i,j,k,l,xs,_,rfl,_,he⟩ := mixedGenerator_list g hc
  apply simplex_mem_imageBounded
  rw [imageFace_eq_image,he]
  simp only [Finset.image_insert,Finset.image_singleton,fiber_projection g₀ g hh,
    Finset.insert_idem]
  exact Finset.card_le_two

/-- Every finite mixed residual has projected support bounded by two, in any common-base chart. -/
theorem MixedSpan_le_imageBounded (g₀ g : IntegralGL)
    (hh : augmentedLine g 0 = augmentedLine g₀ 0) :
    MixedSpan g ≤ imageBounded (vertex g₀) 2 := by
  apply Submodule.span_le.mpr
  exact fun _ hc => mixedGenerator_mem_imageBounded g₀ g hh hc

/-- Reorder a genuine basis so its first two vectors are the coherent additive core. -/
theorem coherent_zero_frame (g : IntegralGL) :
    augmentedFrame (g * (templateChange 2)⁻¹) =
      {augmentedLine g 0,xFiber g 0,yFiber g 0,zFiber g 0} := by
  let h := g * (templateChange 2)⁻¹
  have hh : h * templateChange 2 = g := by simp [h]
  have h0 := normal_line h 2 0
  have h1 := normal_line h 2 1
  have h3 := normal_line h 2 2
  rw [hh] at h0 h1 h3
  change xFiber g 0 = augmentedLine h 0 at h0
  change yFiber g 0 = augmentedLine h 1 at h1
  change zFiber g 0 = augmentedLine h 3 at h3
  have h2 := templateChange_line h 2
  rw [hh] at h2
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide +kernel
  change augmentedFrame h = _
  rw [augmentedFrame,hu]
  simp only [Finset.image_insert,Finset.image_singleton,← h0,← h1,← h2,← h3]
  ext L
  simp only [Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem affineBasis_line_zero (g : IntegralGL) (p : ℤ × ℤ) :
    augmentedLine (affineBasis g p) 0 = augmentedLine g 0 := by
  have hv : (shearGL p).val.mulVec (Pi.single 0 1) = Pi.single 0 1 := by
    change (shearMatrix p).mulVec (Pi.single 0 1) = _
    rw [Matrix.mulVec_single_one]
    funext r
    fin_cases r <;> rfl
  have he : template 0 = rationalVector (Pi.single 0 1) := by
    funext r
    fin_cases r <;> rfl
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * shearGL p) (template 0)} = _
  rw [map_mul,LinearEquiv.mul_apply,he,← rationalVector_mulVec,hv]
  rfl

theorem affineBasis_x (g : IntegralGL) (p : ℤ × ℤ) :
    xFiber (affineBasis g p) 0 = xFiber g p.1 := prismLine_affineBasis g p 0

theorem affineBasis_y (g : IntegralGL) (p : ℤ × ℤ) :
    yFiber (affineBasis g p) 0 = yFiber g p.2 := prismLine_affineBasis g p 1

theorem affineBasis_z (g : IntegralGL) (p : ℤ × ℤ) :
    zFiber (affineBasis g p) 0 = zFiber g (p.1+p.2) := prismLine_affineBasis g p 2

/-- Coherent triangles together with the original bad vertex are actual integral augmented frames. -/
theorem coherent_frame (g : IntegralGL) (p : ℤ × ℤ) :
    augmentedFrame (affineBasis g p * (templateChange 2)⁻¹) =
      {augmentedLine g 0,xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)} := by
  rw [coherent_zero_frame,affineBasis_line_zero,affineBasis_x,affineBasis_y,affineBasis_z]

theorem coherent_face_link (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (hY : residue g 2 ≠ 0)
    (hZ : residue g 1 + residue g 2 ≠ 0) (p : ℤ × ℤ) :
    {xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)} ∈
      augmentedGoodLink {augmentedLine g 0} := by
  refine ⟨⟨by simp,?_⟩,?_⟩
  · rw [Finset.singleton_union,← coherent_frame g p]
    exact augmentedFrame_mem _
  · intro L hL
    simp only [Finset.mem_insert,Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl <;> exact fiberLine_good g hb hX hY hZ _ _

/-- Every literal coherent lift remains an actual triangle in the original Good link. -/
theorem coherent_mem_link (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (hY : residue g 2 ≠ 0)
    (hZ : residue g 1 + residue g 2 ≠ 0) (p : ℤ × ℤ) :
    coherent g p ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 := by
  have he : [xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)].toFinset =
      {xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)} := by
    ext L
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,
      Finset.mem_insert,Finset.mem_singleton]
  have hf := coherent_face_link g hb hX hY hZ p
  rw [← he] at hf
  have hm := simplex_mem_chains (augmentedGoodLink {augmentedLine g 0})
    [xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)] (Or.inr hf)
  change coherent g p ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 at hm
  exact hm

theorem coherentLinear_mem_link (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (hY : residue g 2 ≠ 0)
    (hZ : residue g 1 + residue g 2 ≠ 0) (a : IntegerGridExactness.C₀) :
    coherentLinear g a ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 := by
  induction a using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (chains (augmentedGoodLink {augmentedLine g 0}) 3).zero_mem
  | add a b ha hb' =>
    simpa only [map_add] using (chains (augmentedGoodLink {augmentedLine g 0}) 3).add_mem ha hb'
  | single p q =>
    rw [coherentLinear,Finsupp.linearCombination_single]
    exact (chains (augmentedGoodLink {augmentedLine g 0}) 3).smul_mem q
      (coherent_mem_link g hb hX hY hZ p)

/-- The existing projected reduction retains its actual original link and two-vertex image bound. -/
theorem projected_coherent_reduction (g₀ g : IntegralGL)
    (hh : augmentedLine g 0 = augmentedLine g₀ 0) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (hY : residue g 2 ≠ 0)
    (hZ : residue g 1 + residue g 2 ≠ 0) (a : IntegerGridExactness.C₀)
    (ha : OrientedChainMap.map (vertex g) (coherentLinear g a) = 0) :
    ∃ t r : Chain RationalLine, t ∈ chains good 4 ∧ r ∈ MixedSpan g ∧
      r ∈ chains (augmentedGoodLink {augmentedLine g₀ 0}) 3 ∧
      r ∈ imageBounded (vertex g₀) 2 ∧ coherentLinear g a = boundary t + r := by
  obtain ⟨t,r,ht,hr,he⟩ := BadVertexCoherentProjection.projected_coherent_reduction
    g hb hX hY hZ a ha
  refine ⟨t,r,ht,hr,?_,MixedSpan_le_imageBounded g₀ g hh hr,he⟩
  rw [← hh]
  exact MixedSpan_le_link g hb hX hY hZ hr

/-- Any adapted reference projection detects the same coherent coefficient augmentation. -/
theorem augmentation_eq_zero_of_reference_projected (g₀ g : IntegralGL)
    (hh : augmentedLine g 0 = augmentedLine g₀ 0) (a : IntegerGridExactness.C₀)
    (ha : OrientedChainMap.map (vertex g₀) (coherentLinear g a) = 0) :
    IntegerGridExactness.augmentation a = 0 := by
  let q := lowerGL (g₀⁻¹ * g) (first_column_lower_zero g₀ g hh)
  have hp (p : ℤ × ℤ) : [xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)].map (vertex g₀) =
      [RankTwoAugmentedFrames.augmentedLine q 0,
        RankTwoAugmentedFrames.augmentedLine q 1,RankTwoAugmentedFrames.augmentedLine q 2] := by
    simp only [List.map_cons,List.map_nil,xFiber,yFiber,zFiber,fiber_projection g₀ g hh]
    rfl
  have hn : [RankTwoAugmentedFrames.augmentedLine q 0,
      RankTwoAugmentedFrames.augmentedLine q 1,RankTwoAugmentedFrames.augmentedLine q 2].Nodup := by
    simpa only [List.map_cons,List.map_nil] using
      (List.nodup_cons.mpr ⟨by decide,List.nodup_cons.mpr ⟨by decide,
        List.nodup_cons.mpr ⟨by simp,List.nodup_nil⟩⟩⟩ : ([0,1,2] : List (Fin 3)).Nodup).map
          (RankTwoAugmentedFrames.augmentedLine_injective q)
  exact OrientedSimplexCoefficient.coefficientSum_eq_zero_of_map (vertex g₀)
    (fun p : ℤ × ℤ => [xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)]) _ hn hp a ha

/-- The strengthened reduction is valid using zero projection in any adapted reference chart. -/
theorem reference_projected_coherent_reduction (g₀ g : IntegralGL)
    (hh : augmentedLine g 0 = augmentedLine g₀ 0) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (hY : residue g 2 ≠ 0)
    (hZ : residue g 1 + residue g 2 ≠ 0) (a : IntegerGridExactness.C₀)
    (ha : OrientedChainMap.map (vertex g₀) (coherentLinear g a) = 0) :
    ∃ t r : Chain RationalLine, t ∈ chains good 4 ∧ r ∈ MixedSpan g ∧
      r ∈ chains (augmentedGoodLink {augmentedLine g₀ 0}) 3 ∧
      r ∈ imageBounded (vertex g₀) 2 ∧ coherentLinear g a = boundary t + r := by
  obtain ⟨t,r,ht,hr,he⟩ := coherent_augmentation_zero g hb hX hY hZ a
    (augmentation_eq_zero_of_reference_projected g₀ g hh a ha)
  refine ⟨t,r,ht,hr,?_,MixedSpan_le_imageBounded g₀ g hh hr,he⟩
  rw [← hh]
  exact MixedSpan_le_link g hb hX hY hZ hr

end TernaryPoly.BadVertexPrismSupport
