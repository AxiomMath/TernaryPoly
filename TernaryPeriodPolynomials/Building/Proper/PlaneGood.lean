module

public import TernaryPeriodPolynomials.Building.Proper.PlaneFaces
public import TernaryPeriodPolynomials.Building.RankTwo.GoodComplex
public import TernaryPeriodPolynomials.Building.Proper.PlaneComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.ProperPlaneGood
open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection BadVertexFibers
open AmbientRelativeProjection ProperPlaneChart ProperPlaneFaces

/-- The actual mod-three covector induced on the two integral plane coordinates. -/
def planeFunctional (g : IntegralGL) : RankTwoGoodComplex.Functional where
  toFun v := v 0 * AugmentedBadFaces.columnResidue g 1 + v 1 * AugmentedBadFaces.columnResidue g 2
  map_add' v w := by simp only [Pi.add_apply]; ring
  map_smul' q v := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

/-- Literal Good residue detection pulls back to the displayed rank-two covector. -/
theorem good_section_iff (g : IntegralGL) (Q : RankTwoAugmentedFrames.RationalLine2) :
    Good (sectionVertex g Q).val ↔ RankTwoGoodComplex.Good (planeFunctional g) Q := by
  obtain ⟨p,hp,rfl⟩ := quotientLine_exists_chart Q
  rw [section_quotientLine,chart_val,GoodAugmentedNormalForm.good_span_iff_residue
    (GoodAugmentedNormalForm.primitive_mulVec g (coordinateVector_primitive p hp 0)),
    chart_vector_residue,RankTwoGoodComplex.good_iff_primitive _ _ hp rfl]
  simp [planeFunctional,RankTwoGoodComplex.reduction]

/-- A single actual Good line in the plane makes the pulled-back covector nonzero. -/
theorem planeFunctional_ne_zero (g : IntegralGL) (L : RationalLine)
    (hL : L.val ≤ plane g) (hgood : Good L.val) : planeFunctional g ≠ 0 := by
  intro he
  have hg : RankTwoGoodComplex.Good (planeFunctional g) (vertex g L) := by
    apply (good_section_iff g _).mp
    rw [section_vertex g L hL]
    exact hgood
  rw [he] at hg
  exact hg rfl

/-- The actual full Good subcomplex contained in an integral plane. -/
abbrev goodPlane (g : IntegralGL) : PreAbstractSimplicialComplex RationalLine :=
  ProperPlaneComplex.planeComplex (plane g)

theorem goodPlane_le_planeComplex (g : IntegralGL) : goodPlane g ≤ planeComplex g :=
  fun _ hs => ⟨hs.1.1,hs.2⟩

theorem goodPlane_le_good (g : IntegralGL) : goodPlane g ≤ good := fun _ hs => hs.1

/-- The zero-coordinate section preserves exactly the actual Good plane faces. -/
theorem good_section_mapsFaces (g : IntegralGL) :
    OrientedChainMap.MapsFaces (sectionVertex g) (RankTwoGoodComplex.good (planeFunctional g))
      (goodPlane g) := by
  intro s hs
  have hp := ProperPlaneFaces.section_mapsFaces g s hs.1
  refine ⟨⟨hp.1,?_⟩,hp.2⟩
  intro L hL
  simp only [Finset.mem_image] at hL
  obtain ⟨Q,hQ,rfl⟩ := hL
  exact (good_section_iff g Q).mpr (hs.2 Q hQ)

/-- The actual quotient preserves Good faces supported inside the plane. -/
theorem good_projection_mapsFaces (g : IntegralGL) :
    OrientedChainMap.MapsFaces (vertex g) (goodPlane g)
      (RankTwoGoodComplex.good (planeFunctional g)) := by
  intro s hs
  refine ⟨ProperPlaneFaces.projection_mapsFaces g s ⟨hs.1.1,hs.2⟩,?_⟩
  intro Q hQ
  simp only [Finset.mem_image] at hQ
  obtain ⟨L,hL,rfl⟩ := hQ
  apply (good_section_iff g _).mp
  rw [section_vertex g L (hs.2 L hL)]
  exact hs.1.2 L hL

end TernaryPoly.ProperPlaneGood
