module

public import TernaryPeriodPolynomials.Building.Ambient.RelativeProjection
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Coordinates

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeOrbitCompletion
open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection BadVertexFibers
open AmbientRelativeProjection RelativeStabilizerCoordinates

/-- The actual rational image of a subspace under an integral frame. -/
def mapSpace (g : IntegralGL) (L : RationalSubspace) : RationalSubspace :=
  L.map (rationalRepresentation g).toLinearMap

theorem mapSpace_one (L : RationalSubspace) : mapSpace 1 L = L := by simp [mapSpace]
theorem mapSpace_mul (g h : IntegralGL) (L : RationalSubspace) :
    mapSpace (g*h) L = mapSpace g (mapSpace h L) := by
  simp only [mapSpace,map_mul,LinearEquiv.coe_toLinearMap_mul,Module.End.mul_eq_comp,Submodule.map_comp]
theorem mapSpace_finrank (g : IntegralGL) (L : RationalSubspace) :
    Module.finrank ℚ (mapSpace g L) = Module.finrank ℚ L :=
  ((rationalRepresentation g).submoduleMap L).finrank_eq.symm

theorem L0_span : L0 = Submodule.span ℚ {template 0} := by
  apply le_antisymm
  · intro v hv
    obtain ⟨h1,h2⟩ := (mem_L0 v).mp hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v 0,?_⟩
    funext i
    fin_cases i <;> simp [template,h1,h2]
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl
    simp [template]

theorem P0_span : P0 = Submodule.span ℚ {template 0} ⊔ Submodule.span ℚ {template 1} := by
  apply le_antisymm
  · intro v hv
    have h2 := (mem_P0 v).mp hv
    have he : v = v 0 • template 0 + v 1 • template 1 := by
      funext i
      fin_cases i <;> simp [template,h2]
    rw [he]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ ((show Submodule.span ℚ {template 0} ≤ _ from le_sup_left) (Submodule.mem_span_singleton_self _)))
      (Submodule.smul_mem _ _ ((show Submodule.span ℚ {template 1} ≤ _ from le_sup_right) (Submodule.mem_span_singleton_self _)))
  · apply sup_le
    all_goals
      apply Submodule.span_le.mpr
      intro v hv
      rcases hv with rfl
      simp [template]

theorem mapSpace_L0 (g : IntegralGL) : mapSpace g L0 = (augmentedLine g 0).val := by
  rw [L0_span,mapSpace,Submodule.map_span,Set.image_singleton]
  rfl

theorem mapSpace_P0 (g : IntegralGL) :
    mapSpace g P0 = (augmentedLine g 0).val ⊔ (augmentedLine g 1).val := by
  rw [P0_span,mapSpace,Submodule.map_sup,Submodule.map_span,Submodule.map_span,
    Set.image_singleton,Set.image_singleton]
  rfl

/-- Removing the first frame coordinate changes a vector only by a vector in the first line. -/
theorem lift_projection_sub (g : IntegralGL) (x : Space) :
    lift g (projection g x) = x - (rationalRepresentation g⁻¹ x 0) • rationalRepresentation g (template 0) := by
  apply (rationalRepresentation g⁻¹).injective
  rw [map_sub,map_smul,representation_inverse]
  change rationalRepresentation g⁻¹ (rationalRepresentation g
    ![0,rationalRepresentation g⁻¹ x 1,rationalRepresentation g⁻¹ x 2]) = _
  rw [representation_inverse]
  funext i
  fin_cases i <;> simp [template]

/-- Every rational incident line-plane pair has an actual simultaneous integral basis. -/
theorem flag_completion (L P : RationalSubspace) (hL : Module.finrank ℚ L = 1)
    (hP : Module.finrank ℚ P = 2) (hle : L ≤ P) :
    ∃ g : IntegralGL, mapSpace g L0 = L ∧ mapSpace g P0 = P := by
  obtain ⟨g,hg⟩ := RationalLineBasis.rationalLine_eq_augmentedLine ⟨L,hL⟩
  have hgval : (augmentedLine g 0).val = L := congrArg Subtype.val hg
  have hn : ¬P ≤ L := by
    intro h
    have hd := Submodule.finrank_mono h
    rw [hP,hL] at hd
    omega
  obtain ⟨x,hx,hxL⟩ := Set.not_subset.mp hn
  have hproj : projection g x ≠ 0 := by
    intro h
    apply hxL
    rw [← hgval]
    exact (projection_eq_zero_iff g x).mp h
  obtain ⟨p,hp,_,hs⟩ := RankTwoAugmentedFrames.exists_primitive_same_span (projection g x) hproj
  have hbase : rationalRepresentation g (template 0) ∈ P :=
    hle (hgval ▸ Submodule.mem_span_singleton_self _)
  have hlift : lift g (projection g x) ∈ P := by
    rw [lift_projection_sub]
    exact P.sub_mem hx (P.smul_mem _ hbase)
  have hpP : lift g (RankTwoAugmentedFrames.rationalVector p) ∈ P := by
    have hm : RankTwoAugmentedFrames.rationalVector p ∈ Submodule.span ℚ {projection g x} := by
      rw [← hs]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp hm
    rw [← hq,map_smul]
    exact P.smul_mem q hlift
  refine ⟨g * completion p hp 0,?_,?_⟩
  · rw [mapSpace_L0,completion_line_zero,hgval]
  · apply Submodule.eq_of_le_of_finrank_eq
    · rw [mapSpace_P0,completion_line_zero,completion_line_one,hgval]
      apply sup_le hle
      apply Submodule.span_le.mpr
      intro v hv
      rcases hv with rfl
      exact hpP
    · rw [mapSpace_finrank,finrank_P0,hP]

/-- Every rational plane has an actual integral basis, without an ambient-edge hypothesis. -/
theorem plane_completion (P : RationalSubspace) (hP : Module.finrank ℚ P = 2) :
    ∃ g : IntegralGL, mapSpace g P0 = P := by
  have hn : P ≠ ⊥ := by intro h; rw [h,finrank_bot] at hP; omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  obtain ⟨g,_,hg⟩ := flag_completion (Submodule.span ℚ {v}) P (finrank_span_singleton hv0) hP
    (Submodule.span_le.mpr (by intro w hw; rcases hw with rfl; exact hv))
  exact ⟨g,hg⟩

end TernaryPoly.RelativeOrbitCompletion
