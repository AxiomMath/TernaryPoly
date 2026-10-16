module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Coordinates

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalConstant
open CategoryTheory Limits
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SphereOddDegree.AffineBarycentricSubdivision
variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- Evaluation identifies the actual geometric constant cochains with V-valued Hom
cochains on the genuine rational singular chain group, for arbitrary V. -/
def cochainHomEquiv (n : ℕ) :
    VertexCochain (𝟙 X) (identityCover X) (constantRep V) n ≃ₗ[ℚ]
      (singularChainGroup ℚ X n →ₗ[ℚ] V) where
  toFun := evaluation X V n
  invFun f σ := (fiberEquiv X V (atVertex σ)).symm (f (chainGenerator ℚ X n σ))
  left_inv φ := by
    funext σ
    exact (congrArg (fiberEquiv X V (atVertex σ)).symm
      (evaluation_generator X V n φ σ)).trans ((fiberEquiv X V (atVertex σ)).symm_apply_apply _)
  right_inv f := by
    apply SingularLocalCap.scalarChain_ext
    intro σ
    rw [evaluation_generator, LinearEquiv.apply_symm_apply]
  map_add' φ ψ := by
    apply SingularLocalCap.scalarChain_ext
    intro σ
    rw [LinearMap.add_apply, evaluation_generator, evaluation_generator, evaluation_generator]
    exact map_add _ _ _
  map_smul' r φ := by
    apply SingularLocalCap.scalarChain_ext
    intro σ
    rw [LinearMap.smul_apply, evaluation_generator, evaluation_generator]
    exact map_smul _ r _

end TernaryPoly.SingularLocalConstant
