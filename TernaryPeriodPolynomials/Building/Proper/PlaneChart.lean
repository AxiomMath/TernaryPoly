module

public import TernaryPeriodPolynomials.Building.Ambient.RelativeProjection

@[expose] public section

noncomputable section
namespace TernaryPoly.ProperPlaneChart
open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection AmbientRelativeProjection

/-- The literal integral plane spanned by the last two columns of the chosen frame. -/
def plane (g : IntegralGL) : Submodule ℚ Space := LinearMap.range (lift g)

/-- Membership means that the first inverse-frame coordinate vanishes. -/
theorem mem_plane_iff (g : IntegralGL) (v : Space) :
    v ∈ plane g ↔ rationalRepresentation g⁻¹ v 0 = 0 := by
  constructor
  · rintro ⟨q,rfl⟩
    change rationalRepresentation g⁻¹ (rationalRepresentation g ![0,q 0,q 1]) 0 = 0
    rw [representation_inverse]
    rfl
  · intro hv
    refine ⟨projection g v,?_⟩
    apply (rationalRepresentation g⁻¹).injective
    change rationalRepresentation g⁻¹ (rationalRepresentation g
      ![0,projection g v 0,projection g v 1]) = _
    rw [representation_inverse]
    funext i
    fin_cases i
    · exact hv.symm
    · rfl
    · rfl

theorem lift_projection (g : IntegralGL) {v : Space} (hv : v ∈ plane g) :
    lift g (projection g v) = v := by
  obtain ⟨q,rfl⟩ := hv
  rw [projection_lift]

theorem section_le_plane (g : IntegralGL) (Q : RankTwoAugmentedFrames.RationalLine2) :
    (sectionVertex g Q).val ≤ plane g := by
  rintro v ⟨q,_,rfl⟩
  exact ⟨q,rfl⟩

theorem base_not_le_plane (g : IntegralGL) : ¬(augmentedLine g 0).val ≤ plane g := by
  intro h
  have hv := h (Submodule.mem_span_singleton_self
    (rationalRepresentation g (template 0)))
  have hz := (mem_plane_iff g _).mp hv
  rw [representation_inverse] at hz
  exact one_ne_zero hz

theorem ne_base_of_le_plane (g : IntegralGL) (L : RationalLine) (hL : L.val ≤ plane g) :
    L ≠ augmentedLine g 0 := by
  intro he
  exact base_not_le_plane g (he ▸ hL)

/-- The actual quotient and section are inverse on every rational line in the plane. -/
theorem section_vertex (g : IntegralGL) (L : RationalLine) (hL : L.val ≤ plane g) :
    sectionVertex g (vertex g L) = L := by
  obtain ⟨v,_,_,hs⟩ := RationalLineBasis.rationalLine_primitive_generator L
  have hv : rationalVector v ∈ plane g := hL (hs ▸ Submodule.mem_span_singleton_self _)
  apply Subtype.ext
  rw [section_span g _ ((vertex_span g L (ne_base_of_le_plane g L hL) hs).symm),
    lift_projection g hv,hs]

theorem section_injective (g : IntegralGL) : Function.Injective (sectionVertex g) :=
  (show Function.LeftInverse (vertex g) (sectionVertex g) from vertex_section g).injective

theorem exists_section_iff (g : IntegralGL) (L : RationalLine) :
    (∃ Q, sectionVertex g Q = L) ↔ L.val ≤ plane g := by
  constructor
  · rintro ⟨Q,rfl⟩
    exact section_le_plane g Q
  · intro hL
    exact ⟨vertex g L,section_vertex g L hL⟩

/-- The chart is a literal equivalence onto rational lines contained in the integral plane. -/
def lineEquiv (g : IntegralGL) : RankTwoAugmentedFrames.RationalLine2 ≃
    {L : RationalLine // L.val ≤ plane g} where
  toFun Q := ⟨sectionVertex g Q,section_le_plane g Q⟩
  invFun L := vertex g L.val
  left_inv := vertex_section g
  right_inv L := Subtype.ext (section_vertex g L.val L.property)

/-- The plane has the expected literal rational span of the two integral column lines. -/
theorem plane_eq_sup (g : IntegralGL) :
    plane g = (augmentedLine g 1).val ⊔ (augmentedLine g 2).val := by
  apply le_antisymm
  · rintro v ⟨q,rfl⟩
    have he : lift g q = q 0 • rationalRepresentation g (template 1) +
        q 1 • rationalRepresentation g (template 2) := by
      change rationalRepresentation g ![0,q 0,q 1] = _
      rw [← map_smul,← map_smul,← map_add]
      congr 1
      funext i
      fin_cases i <;> simp [template]
    rw [he]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ ((show (augmentedLine g 1).val ≤ _ from le_sup_left) (Submodule.mem_span_singleton_self _)))
      (Submodule.smul_mem _ _ ((show (augmentedLine g 2).val ≤ _ from le_sup_right) (Submodule.mem_span_singleton_self _)))
  · apply sup_le
    · apply Submodule.span_le.mpr
      intro v hv
      rcases hv with rfl
      exact ⟨![1,0],rfl⟩
    · apply Submodule.span_le.mpr
      intro v hv
      rcases hv with rfl
      exact ⟨![0,1],rfl⟩

theorem plane_finrank_le (g : IntegralGL) : Module.finrank ℚ (plane g) ≤ 2 := by
  change Module.finrank ℚ (LinearMap.range (lift g)) ≤ 2
  calc
    Module.finrank ℚ (LinearMap.range (lift g)) ≤ Module.finrank ℚ RankTwoAugmentedFrames.Space :=
      LinearMap.finrank_range_le (lift g)
    _ = 2 := by simp [RankTwoAugmentedFrames.Space]

theorem plane_finrank (g : IntegralGL) : Module.finrank ℚ (plane g) = 2 := by
  have he := (LinearEquiv.ofInjective (lift g) (lift_injective g)).finrank_eq
  change Module.finrank ℚ RankTwoAugmentedFrames.Space = Module.finrank ℚ (plane g) at he
  rw [← he]
  simp [RankTwoAugmentedFrames.Space]

/-- Cyclically move the complementary column first. -/
theorem templateChange_two_column (h : IntegralGL) (j : Fin 2) :
    augmentedLine (h * templateChange 2) j.succ.castSucc = augmentedLine h j.castSucc.castSucc := by
  apply BadEdgeNormalForm.augmentedLine_mul_of_template
  rw [rationalRepresentation_apply]
  change ((templateChangeMatrix 2).map (Int.castRingHom ℚ)).mulVec _ = _
  fin_cases j <;> funext r <;> fin_cases r <;>
    simp [templateChangeMatrix,template,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

/-- Only planes supported by actual ambient edges require an integral chart. -/
theorem exists_plane_of_edge (L M : RationalLine) (hne : L ≠ M) (he : {L,M} ∈ ambient) :
    ∃ g : IntegralGL, plane g = L.val ⊔ M.val := by
  obtain ⟨h,hL,hM⟩ := BadEdgeNormalForm.ordered_ambient_edge L M hne he
  refine ⟨h * templateChange 2,?_⟩
  rw [plane_eq_sup,show augmentedLine (h * templateChange 2) 1 = augmentedLine h 0 from
    templateChange_two_column h 0,show augmentedLine (h * templateChange 2) 2 = augmentedLine h 1 from
    templateChange_two_column h 1,hL,hM]

end TernaryPoly.ProperPlaneChart
