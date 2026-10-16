module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Coordinates

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCapNormalization
open CategoryTheory Limits
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SingularLocalConstant SingularLocalCap
open SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision

variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- Canonical fiber evaluation removes exactly the two actual cap transport paths,
leaving evaluation on the literal front face. -/
theorem capCoefficient_value (a b : ℕ) (σ : SingularSimplex X (a+b))
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a) :
    fiberEquiv X V (atVertex (backSimplex X a b σ))
        (capCoefficient (𝟙 X) (identityCover X) (constantRep V) a b σ φ) =
      fiberEquiv X V (atVertex (frontSimplex X a b σ)) (φ (frontSimplex X a b σ)) := by
  exact (fiberEquiv_transport X V (simplexPullPath (backMap a b) σ).symm
    (coefficientTransportLinear (𝟙 X) (identityCover X) (simplexPullPath (frontMap a b) σ)
      (φ (frontSimplex X a b σ)))).trans
    (fiberEquiv_transport X V (simplexPullPath (frontMap a b) σ) _)

/-- The finite coefficient sum of the actual geometric simplex cap is front-face evaluation. -/
theorem capSimplex_value (a b : ℕ) (σ : SingularSimplex X (a+b))
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a) :
    coefficientSum X V b (capSimplex (𝟙 X) (identityCover X) (constantRep V) a b σ φ) =
      fiberEquiv X V (atVertex (frontSimplex X a b σ)) (φ (frontSimplex X a b σ)) := by
  exact (coefficientSum_single X V b (backSimplex X a b σ)
    (capCoefficient (𝟙 X) (identityCover X) (constantRep V) a b σ φ)).trans
      (capCoefficient_value X V a b σ φ)

/-- With zero-dimensional back face the front singular simplex is exactly the original simplex. -/
theorem frontSimplex_top (a : ℕ) (σ : SingularSimplex X a) : frontSimplex X a 0 σ = σ := by
  have h : frontFace a 0 = 𝟙 (SimplexCategory.mk a) := by
    ext i
    rfl
  change (TopCat.toSSet.obj X).map (frontFace a 0).op σ = σ
  rw [h, op_id]
  exact congrArg (fun f => f σ) ((TopCat.toSSet.obj X).map_id _)

/-- On a simplex, augmentation of the ACTUAL top-degree geometric cap is literal
V-valued cochain evaluation, with no rank or dimension argument. -/
theorem top_cap_generator (a : ℕ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a) (σ : SingularSimplex X a) :
    coefficientSum X V 0 (cap (𝟙 X) (identityCover X) (constantRep V) a 0 φ
      (chainGenerator ℚ X a σ)) = evaluation X V a φ (chainGenerator ℚ X a σ) := by
  erw [cap_generator]
  rw [capSimplex_value, frontSimplex_top, evaluation_generator]

/-- On every actual finite rational singular chain, augmentation of the existing
geometric top cap equals literal V-valued cochain evaluation. -/
theorem top_cap_evaluation (a : ℕ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a)
    (c : singularChainGroup ℚ X a) :
    coefficientSum X V 0 (cap (𝟙 X) (identityCover X) (constantRep V) a 0 φ c) =
      evaluation X V a φ c := by
  have h : (coefficientSum X V 0).comp (cap (𝟙 X) (identityCover X) (constantRep V) a 0 φ) =
      evaluation X V a φ := by
    apply scalarChain_ext
    exact top_cap_generator X V a φ
  exact LinearMap.congr_fun h c

end TernaryPoly.SingularLocalCapNormalization
