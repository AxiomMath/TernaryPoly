module

public import TernaryPeriodPolynomials.Building.Proper.PlaneChart
public import TernaryPeriodPolynomials.Building.Ambient.DependentTriangles

@[expose] public section


noncomputable section
namespace TernaryPoly.ProperPlaneFaces
open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection AmbientRelativeProjection
open ProperPlaneChart

/-- The quotient coordinates of two plane-supported basis columns. -/
def planeBlock (g h : IntegralGL) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => (g⁻¹*h).val i.succ j.castSucc

theorem relative_first_zero (g h : IntegralGL) (j : Fin 2)
    (hj : (augmentedLine h j.castSucc.castSucc).val ≤ plane g) :
    (g⁻¹*h).val 0 j.castSucc = 0 := by
  have hv := hj (Submodule.mem_span_singleton_self
    (rationalRepresentation h (template j.castSucc.castSucc)))
  have hz := (mem_plane_iff g _).mp hv
  rw [← LinearEquiv.mul_apply,← map_mul] at hz
  rw [show template j.castSucc.castSucc = Pi.single j.castSucc 1 by fin_cases j <;> rfl,
    AugmentedBadFaces.rationalRepresentation_basis] at hz
  change ((g⁻¹*h).val 0 j.castSucc : ℚ) = 0 at hz
  exact_mod_cast hz

theorem planeBlock_isUnit (g h : IntegralGL)
    (hz : ∀ j : Fin 2, (g⁻¹*h).val 0 j.castSucc = 0) : IsUnit (planeBlock g h).det := by
  have hd : (g⁻¹*h).val.det = (g⁻¹*h).val 0 2 * (planeBlock g h).det := by
    rw [Matrix.det_fin_three,Matrix.det_fin_two]
    have h0 := hz 0
    have h1 := hz 1
    change (g⁻¹*h).val 0 0 = 0 at h0
    change (g⁻¹*h).val 0 1 = 0 at h1
    simp only [h0,h1,zero_mul,sub_zero,zero_add,add_zero,planeBlock]
    change (g⁻¹*h).val 0 2 * (g⁻¹*h).val 1 0 * (g⁻¹*h).val 2 1 -
      (g⁻¹*h).val 0 2 * (g⁻¹*h).val 1 1 * (g⁻¹*h).val 2 0 =
      (g⁻¹*h).val 0 2 * ((g⁻¹*h).val 1 0 * (g⁻¹*h).val 2 1 -
        (g⁻¹*h).val 1 1 * (g⁻¹*h).val 2 0)
    ring
  apply isUnit_of_mul_isUnit_right (x := (g⁻¹*h).val 0 2)
  rw [← hd]
  exact (Matrix.isUnit_iff_isUnit_det (g⁻¹*h).val).mp (g⁻¹*h).isUnit

def planeGL (g h : IntegralGL) (hz : ∀ j : Fin 2, (g⁻¹*h).val 0 j.castSucc = 0) :
    RankTwoAugmentedFrames.IntegralGL :=
  Matrix.nonsingInvUnit (planeBlock g h) (planeBlock_isUnit g h hz)

theorem projection_core_vector (g h : IntegralGL)
    (hz : ∀ j : Fin 2, (g⁻¹*h).val 0 j.castSucc = 0) (i : Fin 3) :
    projection g (rationalRepresentation h (template (suspensionIndex i))) =
      RankTwoAugmentedFrames.rationalRepresentation (planeGL g h hz)
        (RankTwoAugmentedFrames.template i) := by
  change dropFirst (rationalRepresentation g⁻¹ (rationalRepresentation h _)) = _
  rw [← LinearEquiv.mul_apply,← map_mul,rationalRepresentation_apply,
    RankTwoAugmentedFrames.rationalRepresentation_apply]
  change dropFirst (((g⁻¹*h).val.map (Int.castRingHom ℚ)).mulVec _) =
    ((planeBlock g h).map (Int.castRingHom ℚ)).mulVec _
  fin_cases i <;> funext r <;> fin_cases r <;>
    simp [dropFirst,planeBlock,suspensionIndex,template,RankTwoAugmentedFrames.template,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three,Fin.sum_univ_two]

theorem core_le_plane (g h : IntegralGL)
    (hz : ∀ j : Fin 2, (g⁻¹*h).val 0 j.castSucc = 0) (i : Fin 3) :
    (augmentedLine h (suspensionIndex i)).val ≤ plane g := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with rfl
  apply (mem_plane_iff g _).mpr
  rw [← LinearEquiv.mul_apply,← map_mul,rationalRepresentation_apply]
  have h0 := hz 0
  have h1 := hz 1
  change (g⁻¹*h).val 0 0 = 0 at h0
  change (g⁻¹*h).val 0 1 = 0 at h1
  change (((g⁻¹*h).val.map (Int.castRingHom ℚ)).mulVec (template (suspensionIndex i))) 0 = 0
  generalize (g⁻¹*h) = r at *
  fin_cases i <;>
    simp [suspensionIndex,template,Matrix.mulVec,dotProduct,Fin.sum_univ_three,h0,h1]

/-- Projecting an actual plane-supported additive core gives one literal rank-two augmented frame. -/
theorem projection_core (g h : IntegralGL)
    (hz : ∀ j : Fin 2, (g⁻¹*h).val 0 j.castSucc = 0) (i : Fin 3) :
    vertex g (augmentedLine h (suspensionIndex i)) =
      RankTwoAugmentedFrames.augmentedLine (planeGL g h hz) i := by
  apply Subtype.ext
  rw [vertex_span g _ (ne_base_of_le_plane g _ (core_le_plane g h hz i))
    (v := rationalRepresentation h (template (suspensionIndex i))) rfl,
    projection_core_vector]
  rfl

/-- The ambient full subcomplex contained in a literal integral plane. -/
def planeComplex (g : IntegralGL) : PreAbstractSimplicialComplex RationalLine where
  faces := {s | s ∈ ambient ∧ ∀ L ∈ s, L.val ≤ plane g}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(ambient.isRelLowerSet_faces hs.1).1,?_⟩
    intro t hts ht
    exact ⟨(ambient.isRelLowerSet_faces hs.1).2 hts ht,fun L hL => hs.2 L (hts hL)⟩

theorem plane_face_finrank_le (g : IntegralGL) (s : Finset RationalLine)
    (hs : ∀ L ∈ s, L.val ≤ plane g) : Module.finrank ℚ (faceSpan s) ≤ 2 :=
  (Submodule.finrank_mono (Finset.sup_le hs)).trans (plane_finrank_le g)

/-- Four actual frame vertices cannot all lie in a rational plane. -/
theorem plane_face_card_le (g : IntegralGL) {s : Finset RationalLine}
    (hs : s ∈ planeComplex g) : s.card ≤ 3 := by
  obtain ⟨⟨hn,h,hsub⟩,hp⟩ := hs
  have hc : s.card ≤ 4 := by
    have he := Finset.card_le_card hsub
    rwa [AugmentedBadFaces.augmentedFrame_card] at he
  by_contra hcard
  have hcard4 : s.card = 4 := by omega
  have heq : s = augmentedFrame h := Finset.eq_of_subset_of_card_le hsub (by
    rw [hcard4,AugmentedBadFaces.augmentedFrame_card])
  have hplane : ∀ L ∈ [augmentedLine h 0,augmentedLine h 1,augmentedLine h 2].toFinset,
      L.val ≤ plane g := by
    intro L hL
    apply hp L
    rw [heq]
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hL
    rcases hL with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,rfl⟩
  have hlow := plane_face_finrank_le g _ hplane
  have hhigh := AmbientDependentTriangles.basis_face_finrank_ge h
  omega

/-- Every actual plane-supported ambient edge projects to an actual quotient edge. -/
theorem projection_edge (g : IntegralGL) (L M : RationalLine) (hne : L ≠ M)
    (he : {L,M} ∈ ambient) (hL : L.val ≤ plane g) (hM : M.val ≤ plane g) :
    {vertex g L,vertex g M} ∈ RankTwoAugmentedFrames.ambient := by
  obtain ⟨h,hhL,hhM⟩ := BadEdgeNormalForm.ordered_ambient_edge L M hne he
  have hz : ∀ j : Fin 2, (g⁻¹*h).val 0 j.castSucc = 0 := by
    intro j
    apply relative_first_zero
    fin_cases j
    · change (augmentedLine h 0).val ≤ plane g
      rwa [hhL]
    · change (augmentedLine h 1).val ≤ plane g
      rwa [hhM]
  have hp0 : vertex g L = RankTwoAugmentedFrames.augmentedLine (planeGL g h hz) 0 := by
    rw [← hhL]
    exact projection_core g h hz 0
  have hp1 : vertex g M = RankTwoAugmentedFrames.augmentedLine (planeGL g h hz) 1 := by
    rw [← hhM]
    exact projection_core g h hz 1
  rw [hp0,hp1]
  apply RankTwoAugmentedFrames.subset_augmentedFrame_mem _ (by simp)
  intro Q hQ
  simp only [Finset.mem_insert,Finset.mem_singleton] at hQ
  rcases hQ with rfl | rfl
  · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩

/-- Every actual plane-supported ambient triangle projects to an actual quotient triangle. -/
theorem projection_triangle (g : IntegralGL) (L M N : RationalLine)
    (hn : [L,M,N].Nodup) (hf : [L,M,N].toFinset ∈ planeComplex g) :
    ([L,M,N].toFinset).image (vertex g) ∈ RankTwoAugmentedFrames.ambient := by
  obtain ⟨h,hperm⟩ := AmbientDependentTriangles.dependent_triangle_core [L,M,N] rfl hn hf.1
    (plane_face_finrank_le g _ hf.2)
  have hp : ∀ i : Fin 3, (augmentedLine h (suspensionIndex i)).val ≤ plane g := by
    intro i
    apply hf.2 _
    apply List.mem_toFinset.mpr
    apply hperm.mem_iff.mpr
    fin_cases i <;> simp [suspensionIndex]
  have hz : ∀ j : Fin 2, (g⁻¹*h).val 0 j.castSucc = 0 := by
    intro j
    apply relative_first_zero
    fin_cases j
    · exact hp 0
    · exact hp 1
  apply RankTwoAugmentedFrames.subset_augmentedFrame_mem (planeGL g h hz) (by simp)
  intro Q hQ
  obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hQ
  have ha := hperm.mem_iff.mp (List.mem_toFinset.mp hA)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,(projection_core g h hz 0).symm⟩
  · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,(projection_core g h hz 1).symm⟩
  · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,(projection_core g h hz 2).symm⟩

/-- The actual inverse chart preserves every plane face, including singleton and edge faces. -/
theorem projection_mapsFaces (g : IntegralGL) :
    OrientedChainMap.MapsFaces (vertex g) (planeComplex g) RankTwoAugmentedFrames.ambient := by
  intro s hs
  have hcard := plane_face_card_le g hs
  have hpos := Finset.card_pos.mpr hs.1.1
  have hcases : s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  have hf : s.image (vertex g) ∈ RankTwoAugmentedFrames.ambient := by
    rcases hcases with hc | hc | hc
    · obtain ⟨L,rfl⟩ := Finset.card_eq_one.mp hc
      simpa using RankTwoAugmentedFrames.singleton_mem_ambient (vertex g L)
    · obtain ⟨L,M,hne,rfl⟩ := Finset.card_eq_two.mp hc
      simpa only [Finset.image_insert,Finset.image_singleton] using
        projection_edge g L M hne hs.1 (hs.2 L (by simp)) (hs.2 M (by simp))
    · obtain ⟨L,M,N,hLM,hLN,hMN,rfl⟩ := Finset.card_eq_three.mp hc
      have hn : [L,M,N].Nodup := by simp [hLM,hLN,hMN]
      have ht : [L,M,N].toFinset ∈ planeComplex g := by simpa using hs
      simpa using projection_triangle g L M N hn ht
  convert hf using 1
  ext Q
  simp only [Finset.mem_image]

/-- The section gives exactly the actual ambient faces in its integral plane. -/
theorem section_mapsFaces (g : IntegralGL) :
    OrientedChainMap.MapsFaces (sectionVertex g) RankTwoAugmentedFrames.ambient (planeComplex g) := by
  intro s hs
  have hh : s.image (sectionVertex g) ∈ link (augmentedLine g 0) := by
    convert AmbientRelativeProjection.section_mapsFaces g s hs using 1
    ext L
    simp only [Finset.mem_image]
  have ha : s.image (sectionVertex g) ∈ ambient :=
    (ambient.isRelLowerSet_faces ((mem_link _ _).mp hh).2.1).2
      Finset.subset_union_right ((mem_link _ _).mp hh).1
  have hp : s.image (sectionVertex g) ∈ planeComplex g := by
    refine ⟨ha,?_⟩
    intro L hL
    obtain ⟨Q,_,rfl⟩ := Finset.mem_image.mp hL
    exact section_le_plane g Q
  convert hp using 1
  ext L
  simp only [Finset.mem_image]

theorem section_face_iff (g : IntegralGL) (s : Finset RankTwoAugmentedFrames.RationalLine2) :
    s.image (sectionVertex g) ∈ planeComplex g ↔ s ∈ RankTwoAugmentedFrames.ambient := by
  constructor
  · intro hs
    have hp := projection_mapsFaces g _ hs
    convert hp using 1
    ext Q
    simp only [Finset.mem_image]
    constructor
    · intro hQ
      exact ⟨sectionVertex g Q,⟨Q,hQ,rfl⟩,vertex_section g Q⟩
    · rintro ⟨L,⟨R,hR,rfl⟩,hLQ⟩
      rw [vertex_section] at hLQ
      exact hLQ ▸ hR
  · intro hs
    convert section_mapsFaces g s hs using 1
    ext L
    simp only [Finset.mem_image]

end TernaryPoly.ProperPlaneFaces
