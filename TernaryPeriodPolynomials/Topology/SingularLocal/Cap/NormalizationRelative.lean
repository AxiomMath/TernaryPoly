module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.NormalizationGeometry
public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.ZeroClasses
public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Cochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCapNormalization
open CategoryTheory Limits
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SingularLocalConstant SingularLocalCap SingularCoverNaturality
open SphereOddDegree.AffineBarycentricSubdivision

variable {E B X : TopCat.{0}}
  (p : E ⟶ B) (F : E ⟶ X) (f : B ⟶ X) (hsquare : F ≫ 𝟙 X = p ≫ f)
  (hp : IsQuotientCoveringMap p Unit)
  (hF : ∀ (g : Unit) (x : E), F (g • x) = g • F x) (V : ModuleCat.{0} ℚ)

/-- A genuine relative cochain's V-valued evaluation vanishes on the actual subspace-chain image. -/
theorem evaluation_subspace_zero (a : ℕ)
    (φ : (relativeLocalCochains p (𝟙 X) F f hsquare hp (identityCover X) hF (constantRep V)).X a)
    (c : singularChainGroup ℚ B a) :
    evaluation X V a ((kernel.ι (localPullback p (𝟙 X) F f hsquare hp (identityCover X) hF
      (constantRep V))).f a φ) ((scalarSpaceMap f).f a c) = 0 := by
  erw [← top_cap_evaluation]
  have h := relativeCochain_cap_subspace_zero p (𝟙 X) F f hsquare hp (identityCover X) hF
    (constantRep V) a 0 φ c
  exact (congrArg (coefficientSum X V 0) h).trans (map_zero _)

/-- Literal V-valued evaluation descends through the actual relative scalar cokernel. -/
def relativeEvaluation (a : ℕ) :
    (relativeLocalCochains p (𝟙 X) F f hsquare hp (identityCover X) hF (constantRep V)).X a →ₗ[ℚ]
      (relativeScalarChains f).X a →ₗ[ℚ] V :=
  RelativeAlgebra.descendBilinear (scalarSpaceMap f) a _ V
    ((cochainHomEquiv X V a).toLinearMap.comp
      ((kernel.ι (localPullback p (𝟙 X) F f hsquare hp (identityCover X) hF (constantRep V))).f a).hom)
    (evaluation_subspace_zero p F f hsquare hp hF V a)

/-- The relative evaluation keeps its literal formula on every actual ambient scalar representative. -/
theorem relativeEvaluation_projection (a : ℕ)
    (φ : (relativeLocalCochains p (𝟙 X) F f hsquare hp (identityCover X) hF (constantRep V)).X a)
    (c : singularChainGroup ℚ X a) :
    relativeEvaluation p F f hsquare hp hF V a φ ((cokernel.π (scalarSpaceMap f)).f a c) =
      evaluation X V a ((kernel.ι (localPullback p (𝟙 X) F f hsquare hp (identityCover X) hF
        (constantRep V))).f a φ) c :=
  RelativeAlgebra.descend_projection (scalarSpaceMap f) a _ _
    (evaluation_subspace_zero p F f hsquare hp hF V a φ) c

/-- The augmentation of the existing relative-cochain cap is the independent relative evaluation. -/
theorem relativeCap_coefficientSum (a : ℕ)
    (φ : (relativeLocalCochains p (𝟙 X) F f hsquare hp (identityCover X) hF (constantRep V)).X a)
    (c : (relativeScalarChains f).X a) :
    coefficientSum X V 0 (relativeCochainCap p (𝟙 X) F f hsquare hp (identityCover X) hF
      (constantRep V) a 0 φ c) = relativeEvaluation p F f hsquare hp hF V a φ c := by
  obtain ⟨z,rfl⟩ := RelativeAlgebra.projection_surjective (scalarSpaceMap f) a c
  erw [relativeCochainCap_projection]
  erw [top_cap_evaluation, relativeEvaluation_projection]

/-- On actual relative homology classes, the existing geometric cap followed by the
literal H0 augmentation equals relative evaluation on their genuine cycle representatives. -/
theorem relativeCapHomology_evaluation (a : ℕ)
    (φ : Homology.Cycles ((relativeLocalCochains p (𝟙 X) F f hsquare hp (identityCover X) hF
      (constantRep V)).sc' (a-1) a (a+1)))
    (c : Homology.Cycles ((relativeScalarChains f).sc' (a+1) a (a-1))) :
    augmentation X V (relativeCochainCapHomology p (𝟙 X) F f hsquare hp (identityCover X) hF
      (constantRep V) a 0 (Descent.cochainClass _ a φ) (Descent.chainClass _ a c)) =
      relativeEvaluation p F f hsquare hp hF V a φ.val c.val := by
  have h := relativeCochainCapHomology_representatives p (𝟙 X) F f hsquare hp (identityCover X) hF
    (constantRep V) a 0 φ c
  exact (congrArg (augmentation X V) h).trans
    ((augmentation_chainClass X V _).trans (relativeCap_coefficientSum p F f hsquare hp hF V a φ.val c.val))

end TernaryPoly.SingularLocalCapNormalization
