module

public import TernaryPeriodPolynomials.Building.Ambient.EdgeRetraction
public import TernaryPeriodPolynomials.Building.AugmentedFrame.CarryingGeometry
public import TernaryPeriodPolynomials.Building.OrientedChain.SimplexPermutation

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientTriangleLocalGeometry
open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness
open GoodAugmentedNormalForm AugmentedFrameComplex AugmentedBadFaces
open PrimitiveLineHeight IntegralFrameHeightReduction AmbientEdgeRetraction
open OrientedListChains

/-- The exact existential lifting property needed in degree two. -/
def Liftable (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector) (w : RationalLine)
    (c : Chain RationalLine) : Prop :=
  ∃ b : Chain RationalLine, b ∈ chains (lowLink F W w) 3 ∧
    boundary b = OrientedChainMap.map (retract F W) (boundary c)

theorem liftable_zero (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector) (w : RationalLine) :
    Liftable F W w 0 := ⟨0,Submodule.zero_mem _,by simp⟩

theorem liftable_smul (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector) (w : RationalLine)
    (q : ℚ) {c : Chain RationalLine} (h : Liftable F W w c) : Liftable F W w (q • c) := by
  obtain ⟨b,hb,he⟩ := h
  exact ⟨q • b,Submodule.smul_mem _ q hb,by simp only [map_smul,he]⟩

theorem liftable_add (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector) (w : RationalLine)
    {c d : Chain RationalLine} (hc : Liftable F W w c) (hd : Liftable F W w d) :
    Liftable F W w (c+d) := by
  obtain ⟨b,hb,he⟩ := hc
  obtain ⟨a,ha,hf⟩ := hd
  exact ⟨b+a,Submodule.add_mem _ hb ha,by simp only [map_add,he,hf]⟩

/-- Existential boundary lifting is independent of the chosen ordering. -/
theorem liftable_perm (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector) (w : RationalLine)
    {l m : List RationalLine} (hp : l.Perm m) (hm : Liftable F W w (simplex m)) :
    Liftable F W w (simplex l) := by
  obtain ⟨q,hq⟩ := OrientedSimplexPermutation.simplex_perm_smul hp
  rw [hq]
  exact liftable_smul F W w q hm

/-- Any primitive nonnegative representative computes the actual retraction span. -/
theorem retract_span_of_nonnegative (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hL : {L} ∈ link w)
    (v : IntegralVector) (hp : Primitive v)
    (hs : Submodule.span ℚ {rationalVector v} = L.val) (hv : 0 ≤ F v) :
    (retract F W L).val = Submodule.span ℚ {rationalVector (remainderVector F W v)} := by
  rw [retract_span F W w L hW hspan hL]
  exact remainder_span_independent F W L v hp hs hv

/-- The exact vector discrepancy in the reduced additive relation. -/
theorem remainderVector_sum (F : IntegralVector →ₗ[ℤ] ℤ) (W v u : IntegralVector) :
    remainderVector F W (v+u) = remainderVector F W v + remainderVector F W u -
      AugmentedHeightArithmetic.carry (F W) (F v) (F u) • W := by
  unfold remainderVector AugmentedHeightArithmetic.carry
  rw [map_add,sub_smul,sub_smul]
  abel

/-- Cyclically move the complementary direction to the final column. -/
def rotateChange : IntegralGL :=
  ⟨!![0,0,1;1,0,0;0,1,0],!![0,1,0;0,0,1;1,0,0],by decide +kernel,by decide +kernel⟩

theorem rotateChange_columns (g : IntegralGL) (j : Fin 3) :
    (g * rotateChange).val.col j = g.val.col ((![1,2,0] : Fin 3 → Fin 3) j) := by
  fin_cases j <;> ext i <;>
    simp [rotateChange,Matrix.col,Matrix.mul_apply,Fin.sum_univ_three]

/-- The rotated augmented sum is the sum of the original complementary columns. -/
theorem rotated_sum_span (g : IntegralGL) :
    (augmentedLine (g * rotateChange) 3).val =
      Submodule.span ℚ {rationalVector (g.val.col 1 + g.val.col 2)} := by
  change Submodule.span ℚ {rationalRepresentation (g * rotateChange) (template 3)} = _
  rw [← rationalVector_integralTemplate,← rationalVector_mulVec]
  have hv := AmbientDependentTriangles.core_vector_columns (g * rotateChange) 2
  change (g * rotateChange).val.mulVec (integralTemplate 3) =
    (g * rotateChange).val.col 0 + (g * rotateChange).val.col 1 at hv
  rw [hv,rotateChange_columns,rotateChange_columns]
  rfl

/-- The original basis columns are the first three literal carrying vectors. -/
theorem carrying_vector_column (g : IntegralGL) (j : Fin 3) :
    AugmentedCarryingGeometry.actualVector g j.castSucc.castSucc = g.val.col j := by
  fin_cases j <;> ext i <;>
    simp [AugmentedCarryingGeometry.actualVector,AugmentedCarryingGeometry.carryVector,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three]

/-- The old carrying lower-link API is contained in the actual unrestricted low link. -/
theorem carrying_lowerLink_le (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (g : IntegralGL) (hw : AugmentedCarryingGeometry.w g = w) :
    AugmentedCarryingGeometry.lowerLink F g (F W) ≤ lowLink F W w := by
  intro s hs
  refine ⟨⟨hs.1.1,?_⟩,?_⟩
  · have he := hs.1.2.2
    rw [hw] at he
    convert he using 1
    ext x
    simp
  · intro L hL
    refine ⟨?_,hs.2 L hL⟩
    intro he
    apply hs.1.2.1
    rw [hw,← he]
    exact hL

/-- Nonempty lists with an actual cone face and strict vertex bounds are low-link faces. -/
theorem list_mem_lowLink (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (l : List RationalLine) (hn : l ≠ [])
    (hf : (w :: l).toFinset ∈ ambient)
    (hv : ∀ L ∈ l, L ≠ w ∧ (height F L : ℤ) < F W) : l.toFinset ∈ lowLink F W w := by
  classical
  refine ⟨⟨(List.toFinset_nonempty_iff l).mpr hn,?_⟩,?_⟩
  · convert hf using 1
    ext x
    simp
  · intro L hL
    exact hv L (List.mem_toFinset.mp hL)

/-- A displayed low image triangle itself supplies the required boundary lift. -/
theorem liftable_of_image_face (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (l : List RationalLine) (hl : l.length = 3)
    (hf : (l.map (retract F W)).toFinset ∈ lowLink F W w) :
    Liftable F W w (simplex l) := by
  refine ⟨simplex (l.map (retract F W)),?_,?_⟩
  · have ha : Allowed (lowLink F W w) (l.map (retract F W)) := by
      right
      convert hf using 1
      ext x
      simp only [List.mem_toFinset]
    simpa only [List.length_map,hl] using simplex_mem_chains _ _ ha
  · rw [← OrientedChainMap.map_simplex,OrientedChainMap.boundary_map]

/-- An internally additive triangle with nonnegative sum generators has a low boundary lift. -/
theorem internal_sum_lift (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w A B C : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (hA : {A} ∈ link w) (hB : {B} ∈ link w) (hC : {C} ∈ link w)
    (a v u : IntegralVector) (hpa : Primitive a) (hpv : Primitive v) (hpu : Primitive u)
    (hsa : Submodule.span ℚ {rationalVector a} = A.val)
    (hsv : Submodule.span ℚ {rationalVector v} = B.val)
    (hsu : Submodule.span ℚ {rationalVector u} = C.val)
    (ha : a = v + u) (hv : 0 ≤ F v) (hu : 0 ≤ F u)
    (g : IntegralGL) (hg0 : g.val.col 0 = W) (hg1 : g.val.col 1 = v) (hg2 : g.val.col 2 = u) :
    Liftable F W w (simplex [A,B,C]) := by
  classical
  let h := reducedBasis F g
  have h0 : h.val.col 0 = W := (reducedBasis_col_zero F g).trans hg0
  have h1 : h.val.col 1 = remainderVector F W v := by
    change (reducedBasis F g).val.col 1 = _
    trans remainderVector F (g.val.col 0) (normalized F (g.val.col 1))
    · exact reducedBasis_col_remainder F g 0
    · rw [hg0,hg1,normalized_eq_self F v hv]
  have h2 : h.val.col 2 = remainderVector F W u := by
    change (reducedBasis F g).val.col 2 = _
    trans remainderVector F (g.val.col 0) (normalized F (g.val.col 2))
    · exact reducedBasis_col_remainder F g 1
    · rw [hg0,hg2,normalized_eq_self F u hu]
  have hRa := retract_span_of_nonnegative F W w A hW hspan hA a hpa hsa
    (by rw [ha,map_add]; omega)
  have hRb := retract_span_of_nonnegative F W w B hW hspan hB v hpv hsv hv
  have hRc := retract_span_of_nonnegative F W w C hW hspan hC u hpu hsu hu
  rcases AugmentedHeightArithmetic.carry_zero_or_one (F W) (F v) (F u) hN with hk | hk
  · have hw' : augmentedLine (h * rotateChange) 2 = w := by
      apply Subtype.ext
      change (augmentedLine (h * rotateChange) (2 : Fin 3).castSucc).val = _
      rw [columnLine_span,rotateChange_columns]
      change Submodule.span ℚ {rationalVector (h.val.col 0)} = _
      rw [h0]
      exact hspan
    have ha' : augmentedLine (h * rotateChange) 3 = retract F W A := by
      apply Subtype.ext
      rw [rotated_sum_span,h1,h2,hRa,ha,remainderVector_sum,hk,zero_smul,sub_zero]
    have hb' : augmentedLine (h * rotateChange) 0 = retract F W B := by
      apply Subtype.ext
      change (augmentedLine (h * rotateChange) (0 : Fin 3).castSucc).val = _
      rw [columnLine_span,rotateChange_columns]
      change Submodule.span ℚ {rationalVector (h.val.col 1)} = _
      rw [h1,hRb]
    have hc' : augmentedLine (h * rotateChange) 1 = retract F W C := by
      apply Subtype.ext
      change (augmentedLine (h * rotateChange) (1 : Fin 3).castSucc).val = _
      rw [columnLine_span,rotateChange_columns]
      change Submodule.span ℚ {rationalVector (h.val.col 2)} = _
      rw [h2,hRc]
    have hf : [w,retract F W A,retract F W B,retract F W C].toFinset ∈ ambient := by
      apply subset_augmentedFrame_mem (h * rotateChange) (by simp)
      intro K hK
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hK
      rcases hK with rfl | rfl | rfl | rfl
      · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,hw'⟩
      · exact Finset.mem_image.mpr ⟨3,Finset.mem_univ _,ha'⟩
      · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,hb'⟩
      · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,hc'⟩
    apply liftable_of_image_face F W w [A,B,C] rfl
    change [retract F W A,retract F W B,retract F W C].toFinset ∈ _
    apply list_mem_lowLink F W w _ (by simp) hf
    intro K hK
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hK
    rcases hK with rfl | rfl | rfl
    · exact ⟨((singleton_mem_link w _).mp (retract_mem_link F W w A hW hspan hA)).2,
        retract_height_lt F W w A hW hspan hN hA⟩
    · exact ⟨((singleton_mem_link w _).mp (retract_mem_link F W w B hW hspan hB)).2,
        retract_height_lt F W w B hW hspan hN hB⟩
    · exact ⟨((singleton_mem_link w _).mp (retract_mem_link F W w C hW hspan hC)).2,
        retract_height_lt F W w C hW hspan hN hC⟩
  · have he0 : AugmentedCarryingGeometry.actualVector h 0 = W :=
      (carrying_vector_column h 0).trans h0
    have he1 : AugmentedCarryingGeometry.actualVector h 1 = remainderVector F W v :=
      (carrying_vector_column h 1).trans h1
    have he2 : AugmentedCarryingGeometry.actualVector h 2 = remainderVector F W u :=
      (carrying_vector_column h 2).trans h2
    have he3 : AugmentedCarryingGeometry.actualVector h 3 = remainderVector F W a := by
      rw [AugmentedCarryingGeometry.actualVector_a,he0,he1,he2,ha,remainderVector_sum,hk,one_smul]
    have hw' : AugmentedCarryingGeometry.w h = w := by
      apply Subtype.ext
      rw [← AugmentedCarryingGeometry.actualVector_span,he0]
      exact hspan
    have ha' : AugmentedCarryingGeometry.a h = retract F W A := by
      apply Subtype.ext
      rw [← AugmentedCarryingGeometry.actualVector_span,he3,hRa]
    have hb' : AugmentedCarryingGeometry.b h = retract F W B := by
      apply Subtype.ext
      rw [← AugmentedCarryingGeometry.actualVector_span,he1,hRb]
    have hc' : AugmentedCarryingGeometry.c h = retract F W C := by
      apply Subtype.ext
      rw [← AugmentedCarryingGeometry.actualVector_span,he2,hRc]
    have hbval : F (AugmentedCarryingGeometry.actualVector h 1) = F v % F W := by
      rw [he1,remainderVector_value]
    have hcval : F (AugmentedCarryingGeometry.actualVector h 2) = F u % F W := by
      rw [he2,remainderVector_value]
    have hcarry : F W ≤ F (AugmentedCarryingGeometry.actualVector h 1) +
        F (AugmentedCarryingGeometry.actualVector h 2) := by
      rw [hbval,hcval]
      exact (AugmentedHeightArithmetic.carry_eq_one_iff (F W) (F v) (F u) hN).mp hk
    have hb0 : 0 ≤ F (AugmentedCarryingGeometry.actualVector h 1) := by
      rw [hbval]
      exact Int.emod_nonneg _ (ne_of_gt hN)
    have hbN : F (AugmentedCarryingGeometry.actualVector h 1) < F W := by
      rw [hbval]
      exact Int.emod_lt_of_pos _ hN
    have hc0 : 0 ≤ F (AugmentedCarryingGeometry.actualVector h 2) := by
      rw [hcval]
      exact Int.emod_nonneg _ (ne_of_gt hN)
    have hcN : F (AugmentedCarryingGeometry.actualVector h 2) < F W := by
      rw [hcval]
      exact Int.emod_lt_of_pos _ hN
    refine ⟨AugmentedCarryingGeometry.replacement h,?_,?_⟩
    · apply chains_mono (carrying_lowerLink_le F W w h hw') 3
      exact AugmentedCarryingGeometry.replacement_mem_lowerLink F h (F W) hN
        (congrArg F he0) hb0 hbN hc0 hcN hcarry
    · rw [AugmentedCarryingGeometry.boundary_replacement]
      rw [← OrientedChainMap.boundary_map,OrientedChainMap.map_simplex]
      simp only [List.map_cons,List.map_nil,ha',hb',hc']

/-- Membership of a listed actual link face gives singleton link membership. -/
theorem singleton_of_link_list (w : RationalLine) (l : List RationalLine)
    (hl : l.toFinset ∈ link w) (L : RationalLine) (hL : L ∈ l) : {L} ∈ link w := by
  classical
  apply ((link w).isRelLowerSet_faces hl).2
  · intro K hK
    have he : K = L := Finset.mem_singleton.mp hK
    subst K
    exact List.mem_toFinset.mpr hL
  · exact Finset.singleton_nonempty L

/-- The quotient of the complementary column agrees with the chosen actual line retraction. -/
theorem retract_complement_line (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (g : IntegralGL) (i : Fin 3) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val)
    (hw : augmentedLine g (AmbientDependentTriangles.coreIndex i) = w)
    (hK : {augmentedLine g 2} ∈ link w) :
    augmentedLine (AmbientDependentTriangles.reducedComplement F g W) 2 =
      retract F W (augmentedLine g 2) := by
  have hz := AmbientDependentTriangles.core_inverse_last_zero g i W hW
    (hspan.trans (congrArg Subtype.val hw).symm)
  have hs : Submodule.span ℚ {rationalVector (normalized F (g.val.col 2))} =
      (augmentedLine g 2).val :=
    (normalized_span F _).trans (columnLine_span g 2).symm
  have hr := retract_span_of_nonnegative F W w (augmentedLine g 2) hW hspan hK
    (normalized F (g.val.col 2)) (normalized_primitive F (column_primitive g 2)) hs
    (normalized_nonneg F _)
  apply Subtype.ext
  change (augmentedLine (AmbientDependentTriangles.reducedComplement F g W)
    (2 : Fin 3).castSucc).val = _
  rw [columnLine_span,AmbientDependentTriangles.reducedComplement_col_two F g W hz,hr]

/-- External additive triangles collapse or remain simplicial after complement reduction. -/
theorem external_triangle_lift (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (g : IntegralGL) (i j k : Fin 3)
    (hw : augmentedLine g (AmbientDependentTriangles.coreIndex i) = w)
    (hp : [w,augmentedLine g (AmbientDependentTriangles.coreIndex j),
      augmentedLine g (AmbientDependentTriangles.coreIndex k)].Perm
        (AmbientDependentTriangles.coreList g))
    (hn : [w,augmentedLine g (AmbientDependentTriangles.coreIndex j),
      augmentedLine g (AmbientDependentTriangles.coreIndex k)].Nodup)
    (hf : [augmentedLine g (AmbientDependentTriangles.coreIndex j),
      augmentedLine g (AmbientDependentTriangles.coreIndex k),augmentedLine g 2].toFinset ∈ link w) :
    Liftable F W w (simplex [augmentedLine g (AmbientDependentTriangles.coreIndex j),
      augmentedLine g (AmbientDependentTriangles.coreIndex k),augmentedLine g 2]) := by
  classical
  let B := augmentedLine g (AmbientDependentTriangles.coreIndex j)
  let C := augmentedLine g (AmbientDependentTriangles.coreIndex k)
  let K := augmentedLine g 2
  have hB : {B} ∈ link w := singleton_of_link_list w _ hf B (by simp [B])
  have hC : {C} ∈ link w := singleton_of_link_list w _ hf C (by simp [C])
  have hK : {K} ∈ link w := singleton_of_link_list w _ hf K (by simp [K])
  change Liftable F W w (simplex [B,C,K])
  rcases retract_additive_edge F W w B C hW hspan hN hB hC hn g hp with hl | he
  · let h := AmbientDependentTriangles.reducedComplement F g W
    have hw' : augmentedLine h (AmbientDependentTriangles.coreIndex i) = w :=
      (AmbientDependentTriangles.reducedComplement_core F g W i).trans hw
    have hb' : augmentedLine h (AmbientDependentTriangles.coreIndex j) = retract F W B := by
      rw [retract_eq_self F W B hl.1]
      exact AmbientDependentTriangles.reducedComplement_core F g W j
    have hc' : augmentedLine h (AmbientDependentTriangles.coreIndex k) = retract F W C := by
      rw [retract_eq_self F W C hl.2]
      exact AmbientDependentTriangles.reducedComplement_core F g W k
    have hk' : augmentedLine h 2 = retract F W K :=
      retract_complement_line F W w g i hW hspan hw hK
    have hcone : [w,retract F W B,retract F W C,retract F W K].toFinset ∈ ambient := by
      apply subset_augmentedFrame_mem h (by simp)
      intro L hL
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hL
      rcases hL with rfl | rfl | rfl | rfl
      · exact Finset.mem_image.mpr ⟨AmbientDependentTriangles.coreIndex i,Finset.mem_univ _,hw'⟩
      · exact Finset.mem_image.mpr ⟨AmbientDependentTriangles.coreIndex j,Finset.mem_univ _,hb'⟩
      · exact Finset.mem_image.mpr ⟨AmbientDependentTriangles.coreIndex k,Finset.mem_univ _,hc'⟩
      · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,hk'⟩
    apply liftable_of_image_face F W w [B,C,K] rfl
    change [retract F W B,retract F W C,retract F W K].toFinset ∈ _
    apply list_mem_lowLink F W w _ (by simp) hcone
    intro L hL
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
    rcases hL with rfl | rfl | rfl
    · exact ⟨((singleton_mem_link w _).mp (retract_mem_link F W w B hW hspan hB)).2,
        retract_height_lt F W w B hW hspan hN hB⟩
    · exact ⟨((singleton_mem_link w _).mp (retract_mem_link F W w C hW hspan hC)).2,
        retract_height_lt F W w C hW hspan hN hC⟩
    · exact ⟨((singleton_mem_link w _).mp (retract_mem_link F W w K hW hspan hK)).2,
        retract_height_lt F W w K hW hspan hN hK⟩
  · refine ⟨0,Submodule.zero_mem _,?_⟩
    rw [map_zero,← OrientedChainMap.boundary_map,OrientedChainMap.map_simplex]
    simp only [List.map_cons,List.map_nil,he,simplex_repeat_adjacent,map_zero]

end TernaryPoly.AmbientTriangleLocalGeometry
