module

public import TernaryPeriodPolynomials.Building.Ambient.RelativeProjection
public import TernaryPeriodPolynomials.Building.RankTwo.HeightLinks

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientRelativeFibers
open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection BadVertexFibers
open AmbientRelativeProjection

/-- Primitive vectors on the two lines of an actual quotient edge form an integral basis. -/
theorem pair_det_isUnit (p q : Pair) (hp : PairPrimitive p) (hq : PairPrimitive q)
    (hne : quotientLine p hp ≠ quotientLine q hq)
    (he : {quotientLine p hp,quotientLine q hq} ∈ RankTwoAugmentedFrames.ambient) :
    IsUnit (p 0 * q 1 - q 0 * p 1) := by
  obtain ⟨b,hb0,hb1⟩ := RankTwoAugmentedFrames.edge_basis _ _ hne he
  have hsp : Submodule.span ℚ {RankTwoAugmentedFrames.rationalVector p} =
      Submodule.span ℚ {RankTwoAugmentedFrames.rationalVector (b.val.col 0)} := by
    change (quotientLine p hp).val = _
    rw [← hb0]
    change Submodule.span ℚ {(RankTwoAugmentedFrames.rationalRepresentation b
      (RankTwoAugmentedFrames.template (0 : Fin 2).castSucc))} = _
    rw [RankTwoVertexLinks.representation_column]
    rfl
  have hsq : Submodule.span ℚ {RankTwoAugmentedFrames.rationalVector q} =
      Submodule.span ℚ {RankTwoAugmentedFrames.rationalVector (b.val.col 1)} := by
    change (quotientLine q hq).val = _
    rw [← hb1]
    change Submodule.span ℚ {(RankTwoAugmentedFrames.rationalRepresentation b
      (RankTwoAugmentedFrames.template (1 : Fin 2).castSucc))} = _
    rw [RankTwoVertexLinks.representation_column]
    rfl
  have hu : IsUnit (b.val 0 0 * b.val 1 1 - b.val 0 1 * b.val 1 0) := by
    rw [← Matrix.det_fin_two]
    exact (Matrix.isUnit_iff_isUnit_det b.val).mp b.isUnit
  rcases RankTwoAugmentedFrames.primitive_eq_or_neg_of_span_eq hp
    (rankTwo_column_primitive b 0) hsp with rfl | rfl <;>
    rcases RankTwoAugmentedFrames.primitive_eq_or_neg_of_span_eq hq
      (rankTwo_column_primitive b 1) hsq with rfl | rfl
  · exact hu
  · convert hu.neg using 1
    simp [Matrix.col]
    ring
  · convert hu.neg using 1
    simp [Matrix.col]
    ring
  · simpa only [Pi.neg_apply,neg_mul_neg,Matrix.col,Matrix.transpose_apply] using hu

/-- A basis with the first line fixed and two arbitrary integral fiber coordinates. -/
def pairMatrix (p q : Pair) (k l : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1,k,l;0,p 0,q 0;0,p 1,q 1]

def pairGL (p q : Pair) (hu : IsUnit (p 0 * q 1 - q 0 * p 1)) (k l : ℤ) : IntegralGL :=
  Matrix.nonsingInvUnit (pairMatrix p q k l)
    (by simpa [pairMatrix,Matrix.det_fin_three] using hu)

theorem pairGL_template (p q : Pair) (hu : IsUnit (p 0 * q 1 - q 0 * p 1))
    (k l : ℤ) (i : Fin 4) :
    rationalRepresentation (pairGL p q hu k l) (template i) =
      (![template 0,rationalVector (coordinateVector p k),
        rationalVector (coordinateVector q l),rationalVector (coordinateVector p (k+1))] :
          Fin 4 → Space) i := by
  rw [rationalRepresentation_apply]
  change ((pairMatrix p q k l).map (Int.castRingHom ℚ)).mulVec _ = _
  fin_cases i <;> funext r <;> fin_cases r <;>
    simp [pairMatrix,template,coordinateVector,rationalVector,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three,add_comm]

theorem pairGL_base (g : IntegralGL) (p q : Pair)
    (hu : IsUnit (p 0 * q 1 - q 0 * p 1)) (k l : ℤ) :
    augmentedLine (g * pairGL p q hu k l) 0 = augmentedLine g 0 := by
  apply BadEdgeNormalForm.augmentedLine_mul_of_template
  exact pairGL_template p q hu k l 0

theorem pairGL_first (g : IntegralGL) (p q : Pair) (hp : PairPrimitive p)
    (hu : IsUnit (p 0 * q 1 - q 0 * p 1)) (k l : ℤ) :
    augmentedLine (g * pairGL p q hu k l) 1 = chart g p hp k := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * pairGL p q hu k l) (template 1)} = _
  rw [map_mul,LinearEquiv.mul_apply,pairGL_template]
  rfl

theorem pairGL_second (g : IntegralGL) (p q : Pair) (hq : PairPrimitive q)
    (hu : IsUnit (p 0 * q 1 - q 0 * p 1)) (k l : ℤ) :
    augmentedLine (g * pairGL p q hu k l) 2 = chart g q hq l := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * pairGL p q hu k l) (template 2)} = _
  rw [map_mul,LinearEquiv.mul_apply,pairGL_template]
  rfl

theorem pairGL_shift (g : IntegralGL) (p q : Pair) (hp : PairPrimitive p)
    (hu : IsUnit (p 0 * q 1 - q 0 * p 1)) (k l : ℤ) :
    augmentedLine (g * pairGL p q hu k l) 3 = chart g p hp (k+1) := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * pairGL p q hu k l) (template 3)} = _
  rw [map_mul,LinearEquiv.mul_apply,pairGL_template]
  rfl

/-- Every neighboring fiber edge can be coned to every point over an independent quotient neighbor. -/
theorem mixed_triangle (g : IntegralGL) (p q : Pair) (hp : PairPrimitive p) (hq : PairPrimitive q)
    (hu : IsUnit (p 0 * q 1 - q 0 * p 1)) (k l : ℤ) :
    {chart g p hp k,chart g p hp (k+1),chart g q hq l} ∈ link (augmentedLine g 0) := by
  apply (mem_link _ _).mpr
  refine ⟨by simp,?_,?_⟩
  · apply subset_augmentedFrame_mem (g * pairGL p q hu k l) (by simp)
    intro L hL
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,pairGL_base g p q hu k l⟩
    · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,pairGL_first g p q hp hu k l⟩
    · exact Finset.mem_image.mpr ⟨3,Finset.mem_univ _,pairGL_shift g p q hp hu k l⟩
    · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,pairGL_second g p q hq hu k l⟩
  · intro L hL
    simp only [Finset.mem_insert,Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl <;> exact chart_ne_base _ _ _ _

/-- The completion of a primitive quotient vector supplies an independent primitive neighbor. -/
theorem exists_pair_neighbor (p : Pair) (hp : PairPrimitive p) :
    ∃ q : Pair, PairPrimitive q ∧ IsUnit (p 0 * q 1 - q 0 * p 1) := by
  let b := RankTwoAugmentedFrames.primitiveCompletion p hp
  refine ⟨b.val.col 1,rankTwo_column_primitive b 1,?_⟩
  have hc := RankTwoAugmentedFrames.primitiveCompletion_first_column p hp
  have hd := RankTwoAugmentedFrames.primitiveCompletion_det p hp
  rw [Matrix.det_fin_two] at hd
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  change b.val 0 0 = p 0 at h0
  change b.val 1 0 = p 1 at h1
  change b.val 0 0 * b.val 1 1 - b.val 0 1 * b.val 1 0 = 1 at hd
  change IsUnit (p 0 * b.val 1 1 - b.val 0 1 * p 1)
  rw [← h0,← h1,hd]
  exact isUnit_one

/-- Every consecutive integer fiber pair is an actual unrestricted link edge. -/
theorem chart_edge (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    {chart g p hp k,chart g p hp (k+1)} ∈ link (augmentedLine g 0) := by
  obtain ⟨q,hq,hu⟩ := exists_pair_neighbor p hp
  exact ((link (augmentedLine g 0)).isRelLowerSet_faces
    (mixed_triangle g p q hp hq hu k 0)).2
    (by intro L hL; simp only [Finset.mem_insert,Finset.mem_singleton] at hL ⊢; tauto)
    (by simp)

/-- Every finite integer-path face maps to the actual fiber subcomplex. -/
theorem chart_mapsFaces (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) :
    OrientedChainMap.MapsFaces (chart g p hp) IntegerPathChains.pathComplex
      (link (augmentedLine g 0)) := by
  intro s hs
  obtain ⟨hn,k,hk⟩ := hs
  have hf : s.image (chart g p hp) ∈ link (augmentedLine g 0) := by
    apply ((link _).isRelLowerSet_faces (chart_edge g p hp k)).2 _ (hn.image _)
    intro L hL
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hL
    have he : a = k ∨ a = k+1 := by simpa using hk ha
    simpa only [Finset.mem_insert,Finset.mem_singleton] using
      he.imp (congrArg (chart g p hp)) (congrArg (chart g p hp))
  convert hf using 1
  ext L
  simp only [Finset.mem_image]

end TernaryPoly.AmbientRelativeFibers
