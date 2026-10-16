module

public import TernaryPeriodPolynomials.Building.RankTwo.HeightZero

@[expose] public section


noncomputable section
namespace TernaryPoly.RankTwoHeightEdges
open RankTwoAugmentedFrames RankTwoVertexLinks RankTwoHeightLinks RankTwoHeightZero
open OrientedListChains OrientedChainJoin

local instance : DecidableEq RationalLine2 := Classical.decEq _

/-- Heights of the other two literal augmented-frame lines. -/
theorem height_second (g : IntegralGL) : height (augmentedLine g 1) = (g.val 1 1).natAbs := by
  have he : coordinateLine g 0 = augmentedLine g 1 := by apply Subtype.ext; rfl
  rw [← he,height_coordinateLine]
  simp

theorem height_sum (g : IntegralGL) :
    height (augmentedLine g 2) = (g.val 1 0 + g.val 1 1).natAbs := by
  have he : coordinateLine g 1 = augmentedLine g 2 := by apply Subtype.ext; rfl
  rw [← he,height_coordinateLine]
  simp [add_comm]

/-- The full literal frame is an ambient triangle. -/
theorem frame_triangle (g : IntegralGL) :
    {augmentedLine g 0,augmentedLine g 1,augmentedLine g 2} ∈ ambient := by
  apply subset_augmentedFrame_mem g (by simp)
  intro L hL
  simp only [Finset.mem_insert,Finset.mem_singleton] at hL
  rcases hL with rfl | rfl | rfl <;> exact augmentedLine_mem_frame g _

/-- Two strictly lower neighbors of a vertex span an actual triangle with that vertex. -/
theorem lower_triangle (L M N : RationalLine2)
    (hm : height M < height L) (hn : height N < height L)
    (hLM : {L,M} ∈ ambient) (hLN : {L,N} ∈ ambient) : {L,M,N} ∈ ambient := by
  obtain ⟨g,hg⟩ := rationalLine_eq_augmentedLine L
  have hM : {M} ∈ lowLink g := by
    refine ⟨(singleton_mem_link_iff g M).mpr ⟨?_,by rwa [hg]⟩,?_⟩
    · intro he
      rw [hg] at he
      rw [he] at hm
      exact (Nat.lt_irrefl _) hm
    · intro P hP
      rw [Finset.mem_singleton] at hP
      subst P
      rwa [hg]
  have hN : {N} ∈ lowLink g := by
    refine ⟨(singleton_mem_link_iff g N).mpr ⟨?_,by rwa [hg]⟩,?_⟩
    · intro he
      rw [hg] at he
      rw [he] at hn
      exact (Nat.lt_irrefl _) hn
    · intro P hP
      rw [Finset.mem_singleton] at hP
      subst P
      rwa [hg]
  have ht : {augmentedLine g 0} ∪ {M,N} ∈ ambient := (low_pair_mem g M N hM hN).1.1.2
  simpa only [hg,Finset.singleton_union] using ht

def negateSecondMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![1,0;0,-1]

def negateSecond : IntegralGL :=
  ⟨negateSecondMatrix,negateSecondMatrix,by decide +kernel,by decide +kernel⟩

theorem negateSecond_first (g : IntegralGL) :
    augmentedLine (g * negateSecond) 0 = augmentedLine g 0 := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * negateSecond) (template 0)} = _
  rw [map_mul,LinearEquiv.mul_apply]
  have he : rationalRepresentation negateSecond (template 0) = template 0 := by
    rw [rationalRepresentation_apply]
    funext i
    fin_cases i <;> simp [negateSecond,negateSecondMatrix,template,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  rw [he]
  rfl

theorem negateSecond_second (g : IntegralGL) :
    augmentedLine (g * negateSecond) 1 = augmentedLine g 1 := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * negateSecond) (template 1)} = _
  rw [map_mul,LinearEquiv.mul_apply]
  have he : rationalRepresentation negateSecond (template 1) = (-1 : ℚ) • template 1 := by
    rw [rationalRepresentation_apply]
    funext i
    fin_cases i <;> simp [negateSecond,negateSecondMatrix,template,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  rw [he,map_smul,Submodule.span_singleton_smul_eq (by norm_num : IsUnit (-1 : ℚ))]
  rfl

/-- Equal positive-height endpoints admit the actual signed-difference subdivision of height zero. -/
theorem equal_height_subdivision (L M : RationalLine2) (hne : L ≠ M)
    (hLM : {L,M} ∈ ambient) (he : height L = height M) :
    ∃ N : RationalLine2, height N = 0 ∧ {L,M,N} ∈ ambient := by
  obtain ⟨g,hg0,hg1⟩ := edge_basis L M hne (by
    apply (ambient.isRelLowerSet_faces hLM).2
    · intro P hP
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hP
    · simp)
  have hh : (g.val 1 0).natAbs = (g.val 1 1).natAbs := by
    rw [← height_first,← height_second,hg0,hg1]
    exact he
  rcases Int.natAbs_eq_natAbs_iff.mp hh with hp | hn
  · refine ⟨augmentedLine (g * negateSecond) 2,?_,?_⟩
    · rw [height_sum]
      have h0 : (g * negateSecond).val 1 0 = g.val 1 0 := by
        change (g.val * negateSecondMatrix) 1 0 = _
        simp [Matrix.mul_apply,Fin.sum_univ_two,negateSecondMatrix]
      have h1 : (g * negateSecond).val 1 1 = -g.val 1 1 := by
        change (g.val * negateSecondMatrix) 1 1 = _
        simp [Matrix.mul_apply,Fin.sum_univ_two,negateSecondMatrix]
      rw [h0,h1,hp,add_neg_cancel]
      rfl
    · have ht := frame_triangle (g * negateSecond)
      rwa [negateSecond_first,negateSecond_second,hg0,hg1] at ht
  · refine ⟨augmentedLine g 2,?_,?_⟩
    · rw [height_sum,hn,neg_add_cancel]
      rfl
    · simpa only [hg0,hg1] using frame_triangle g

end TernaryPoly.RankTwoHeightEdges
