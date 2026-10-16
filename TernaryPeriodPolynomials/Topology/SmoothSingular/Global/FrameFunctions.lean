module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FrameSimplices

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory TopologicalSpace Set
open FreeActionLinearization CoveringSingularOrbits
open scoped Simplicial
variable {G : Type} [Group G] {X Y : TopCat.{0}}
  [MulAction G X] [ContinuousConstSMul G X] (T : SingularFrame G X Y) (V : Rep ℝ G) (n : ℕ)

/-- Restrict actual equivariant simplex functions to the actual chosen lifting sheet. -/
def frameFunctionRestriction : equivariantFunctions G X V n →ₗ[ℝ] (SingularSimplex Y n → V) where
  toFun c σ := c (projection T.lift n σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extend actual simplex values by the representation of the genuine sheet label. -/
def frameFunctionExtension : (SingularSimplex Y n → V) →ₗ[ℝ] equivariantFunctions G X V n where
  toFun c := ⟨fun σ => V.ρ (simplexLabel T n σ) (c (projection T.base n σ)), by
    intro g σ
    dsimp only
    rw [simplexLabel_smul, frameProjection_smul, map_mul]
    rfl⟩
  map_add' c d := by
    apply Subtype.ext
    funext σ
    exact map_add _ _ _
  map_smul' a c := by
    apply Subtype.ext
    funext σ
    exact map_smul _ _ _

/-- Actual frame extension recovers each equivariant simplex function. -/
theorem frameFunctionExtension_restriction (c : equivariantFunctions G X V n) :
    frameFunctionExtension T V n (frameFunctionRestriction T V n c) = c := by
  apply Subtype.ext
  funext σ
  change V.ρ (simplexLabel T n σ) (c (projection T.lift n (projection T.base n σ))) = c σ
  rw [← c.property, simplex_frame_reconstruction]

/-- Actual frame restriction recovers each ordinary simplex function. -/
theorem frameFunctionRestriction_extension (c : SingularSimplex Y n → V) :
    frameFunctionRestriction T V n (frameFunctionExtension T V n c) = c := by
  funext σ
  change V.ρ (simplexLabel T n (projection T.lift n σ))
    (c (projection T.base n (projection T.lift n σ))) = c σ
  rw [simplexLabel_lift, frameProjection_lift, map_one]
  rfl

/-- The genuine covering frame identifies actual equivariant simplex functions with ordinary
coefficient-valued simplex functions; all inverse formulas use the actual deck action. -/
def frameFunctionEquiv : equivariantFunctions G X V n ≃ₗ[ℝ] (SingularSimplex Y n → V) where
  __ := frameFunctionRestriction T V n
  invFun := frameFunctionExtension T V n
  left_inv := frameFunctionExtension_restriction T V n
  right_inv := frameFunctionRestriction_extension T V n

end TernaryPoly.SmoothSingularGlobal
