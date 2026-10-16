module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Cochains

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalConstant
open CategoryTheory Limits
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SphereOddDegree.AffineBarycentricSubdivision
variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- The canonical coefficient value of the geometric cochain differential is the ordinary
alternating sum of the cochain values on the same singular faces. -/
theorem differential_value (n : ℕ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) n)
    (σ : SingularSimplex X (n+1)) :
    fiberEquiv X V (atVertex σ) (differential (𝟙 X) (identityCover X) (constantRep V) n φ σ) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        fiberEquiv X V (atVertex (pullSimplex (simplexCoface n i) σ))
          (φ (pullSimplex (simplexCoface n i) σ)) := by
  refine (congrArg (fiberEquiv X V (atVertex σ))
    (differential_apply (𝟙 X) (identityCover X) (constantRep V) n φ σ)).trans ?_
  refine (map_sum (fiberEquiv X V (atVertex σ)) _ _).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  exact (map_zsmul (fiberEquiv X V (atVertex σ)) _ _).trans
    (congrArg (fun v => (-1 : ℤ)^i.val • v) (fiberEquiv_transport X V _ _))

/-- The actual local cochain differential becomes precomposition with the actual rational
singular boundary under the V-valued Hom comparison. -/
theorem evaluation_differential (n : ℕ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) n) :
    evaluation X V (n+1) (differential (𝟙 X) (identityCover X) (constantRep V) n φ) =
      (evaluation X V n φ).comp (singularBoundary ℚ X n).hom := by
  apply SingularLocalCap.scalarChain_ext
  intro σ
  erw [evaluation_generator, differential_value, LinearMap.comp_apply,
    SingularLocalCap.scalarBoundary_generator, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, evaluation_generator]
  rfl

end TernaryPoly.SingularLocalConstant
