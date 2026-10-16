module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisKeep

@[expose] public section

noncomputable section
namespace TernaryPoly.EquivariantSingularMayerVietoris
open CategoryTheory FreeActionLinearization EquivariantSingularResolution EquivariantSingularSmall
open SphereOddDegree TopologicalSpace

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (U V : Opens E) (hU : InvariantSet G E (U : Set E)) (hV : InvariantSet G E (V : Set E))
  (hUV : U ⊔ V = ⊤)

/-- Routing a left-supported chain back to the left recovers the actual chain. -/
theorem left_routeLeft (n : ℕ) :
    (leftToCover G E U V hU hV hUV).f n ≫ routeLeft G E U V hU hV hUV n = 𝟙 _ := by
  ext c
  apply Subtype.ext
  exact congrArg (fun m => (m.hom c).val) (mvInclU_small_comp_routeU ℚ U V hUV n)

/-- The actual right-only route kills all left-supported chains. -/
theorem left_routeRight (n : ℕ) :
    (leftToCover G E U V hU hV hUV).f n ≫ routeRight G E U V hU hV hUV n = 0 := by
  ext c
  apply Subtype.ext
  exact congrArg (fun m => (m.hom c).val) (mvInclU_small_comp_routeV ℚ U V hUV n)

/-- Routing a right-supported chain to the left factors through actual intersection chains. -/
theorem right_routeLeft (n : ℕ) :
    (rightToCover G E U V hU hV hUV).f n ≫ routeLeft G E U V hU hV hUV n =
      projectRightToInter G E U V hU hV n ≫ (interToLeft G E U V hU hV).f n := by
  ext c
  apply Subtype.ext
  exact congrArg (fun m => (m.hom c).val) (mvInclV_small_comp_routeU ℚ U V hUV n)

/-- The actual right-supported chain splits into its intersection and right-only parts. -/
theorem right_inter_add_route (n : ℕ) :
    projectRightToInter G E U V hU hV n ≫ (interToRight G E U V hU hV).f n +
      (rightToCover G E U V hU hV hUV).f n ≫ routeRight G E U V hU hV hUV n = 𝟙 _ := by
  ext c
  apply Subtype.ext
  exact congrArg (fun m => (m.hom c).val) (projVtoUV_inclUV_V_add_inclV_routeV ℚ U V hUV n)

include hUV in
/-- The right-to-intersection projection recovers every actual intersection chain. -/
theorem inter_projectRight (n : ℕ) :
    (interToRight G E U V hU hV).f n ≫ projectRightToInter G E U V hU hV n = 𝟙 _ := by
  ext c
  apply Subtype.ext
  exact congrArg (fun m => (m.hom c).val) (mvInclUV_V_comp_projVtoUV ℚ U V hUV n)

/-- The two actual coordinate routes recover every small chain after inclusion. -/
theorem route_cover_identity (n : ℕ) :
    routeLeft G E U V hU hV hUV n ≫ (leftToCover G E U V hU hV hUV).f n +
      routeRight G E U V hU hV hUV n ≫ (rightToCover G E U V hU hV hUV).f n = 𝟙 _ := by
  ext c
  apply Subtype.ext
  exact keepHom_split_small ℚ U V hUV n c.val c.property

end TernaryPoly.EquivariantSingularMayerVietoris
