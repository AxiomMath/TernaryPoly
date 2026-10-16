module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Excision.Algebra
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisRestriction

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalExcision
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open EquivariantSingularSmall EquivariantSingularMayerVietoris

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (U V : Opens E) (hU : InvariantSet G E (U : Set E)) (hV : InvariantSet G E (V : Set E))
  (hUV : U ⊔ V = ⊤) (W : Rep.{0} ℚ G)

/-- The actual signed Mayer–Vietoris sequence remains short exact for arbitrary coefficients. -/
theorem coefficientSquare_shortExact :
    (ShortComplex.mk
      (biprod.lift ((coefficients G W).map (interToLeft G E U V hU hV))
        (-((coefficients G W).map (interToRight G E U V hU hV))))
      (biprod.desc ((coefficients G W).map (leftToCover G E U V hU hV hUV))
        ((coefficients G W).map (rightToCover G E U V hU hV hUV)))
      (by rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
          inclusion_square]; simp)).ShortExact := by
  exact ShortComplex.shortExact_of_iso
    (mapSquareIso (coefficients G W) (interToLeft G E U V hU hV) (interToRight G E U V hU hV)
      (leftToCover G E U V hU hV hUV) (rightToCover G E U V hU hV hUV)
      (inclusion_square G E U V hU hV hUV).symm)
    (map_degreewise_split_shortExact ((Rep.coinvariantsTensor ℚ G).obj W)
      (chainShortComplex G E U V hU hV hUV) (evaluatedSplitting G E U V hU hV hUV))

/-- The supported coefficient quotient maps to the small-chain quotient by the actual square. -/
def supportedSmallMap :
    cokernel ((coefficients G W).map (interToRight G E U V hU hV)) ⟶
      cokernel ((coefficients G W).map (leftToCover G E U V hU hV hUV)) :=
  cokernel.map _ _ ((coefficients G W).map (interToLeft G E U V hU hV))
    ((coefficients G W).map (rightToCover G E U V hU hV hUV))
    (by rw [← Functor.map_comp, ← Functor.map_comp, inclusion_square])

/-- This literal square induces an isomorphism after tensoring with any coefficient representation. -/
instance supportedSmallMap_isIso : IsIso (supportedSmallMap G E U V hU hV hUV W) :=
  RelativeExcisionAlgebra.cokernel_map_isIso_of_shortExact _ _ _ _
    (by rw [← Functor.map_comp, ← Functor.map_comp, inclusion_square])
    (coefficientSquare_shortExact G E U V hU hV hUV W)

/-- The actual left-to-small inclusion remains monic by its equivariant degreewise retraction. -/
instance coefficientLeftToSmall_mono :
    Mono ((coefficients G W).map (leftToCover G E U V hU hV hUV)) := by
  apply mono_of_mono_f
  intro n
  let F := (Rep.coinvariantsTensor ℚ G).obj W
  change Mono (F.map ((leftToCover G E U V hU hV hUV).f n))
  apply mono_of_mono_fac (g := F.map ((leftToCover G E U V hU hV hUV).f n))
    (f := F.map (routeLeft G E U V hU hV hUV n)) (h := 𝟙 _)
  rw [← F.map_comp, left_routeLeft, F.map_id]

/-- The full coefficient inclusion square commutes literally. -/
theorem smallToFull_square :
    (coefficients G W).map (leftToCover G E U V hU hV hUV) ≫
      (coefficients G W).map (smallInclusion G E (SphereOddDegree.twoSetCover U V hUV)
        (twoSetCover_invariant G E U V hU hV hUV)) =
    𝟙 _ ≫ (coefficients G W).map (subordinateInclusion G E (U : Set E) hU) := by
  rw [Category.id_comp, ← Functor.map_comp]
  exact congrArg ((coefficients G W).map) (subordinateToSmall_inclusion G E _ _ _ _ _)

/-- The literal small-to-full relative coefficient map. -/
def smallRelativeMap :
    cokernel ((coefficients G W).map (leftToCover G E U V hU hV hUV)) ⟶
      cokernel ((coefficients G W).map (subordinateInclusion G E (U : Set E) hU)) :=
  cokernel.map _ _ (𝟙 _) ((coefficients G W).map
    (smallInclusion G E (SphereOddDegree.twoSetCover U V hUV)
      (twoSetCover_invariant G E U V hU hV hUV))) (smallToFull_square G E U V hU hV hUV W)

/-- Actual small-to-full relative excision follows from the genuine coefficient homotopy equivalence. -/
theorem smallRelativeMap_quasiIso [IsCancelSMul G E]
    [Mono ((coefficients G W).map (subordinateInclusion G E (U : Set E) hU))] :
    QuasiIso (smallRelativeMap G E U V hU hV hUV W) := by
  have := smallCoefficientInclusion_quasiIso G E W (SphereOddDegree.twoSetCover U V hUV)
    (twoSetCover_invariant G E U V hU hV hUV)
  exact @RelativeExcisionAlgebra.cokernel_map_quasiIso _ _ _ _
    ((coefficients G W).map (leftToCover G E U V hU hV hUV))
    ((coefficients G W).map (subordinateInclusion G E (U : Set E) hU))
    inferInstance inferInstance (𝟙 _)
    ((coefficients G W).map (smallInclusion G E (SphereOddDegree.twoSetCover U V hUV)
      (twoSetCover_invariant G E U V hU hV hUV)))
    (smallToFull_square G E U V hU hV hUV W) inferInstance this

end TernaryPoly.SingularLocalExcision
