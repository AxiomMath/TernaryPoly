module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ChartsProduct
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryCharts
open SymmetricSpaceFlagCoordinates
open scoped Manifold

/-- Identify the product model with Mathlib's standard Euclidean half-space, with height first. -/
def productHalfSpaceHomeomorph : ProductModel ≃ₜ EuclideanHalfSpace 5 where
  toFun p := ⟨WithLp.toLp 2 ![p.2.val,p.1 0,p.1 1,p.1 2,p.1 3],p.2.property⟩
  invFun p := (![p.val 1,p.val 2,p.val 3,p.val 4],⟨p.val 0,p.property⟩)
  left_inv p := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 5 => ℝ)).comp (by fun_prop)
  continuous_invFun := by fun_prop

@[simp] theorem productHalfSpace_height (p : ProductModel) :
    (productHalfSpaceHomeomorph p).val 0=p.2.val := rfl

/-- The actual flag corner has the standard five-dimensional manifold-with-boundary model. -/
def cornerHalfSpaceHomeomorph : Corner ≃ₜ EuclideanHalfSpace 5 :=
  cornerProductHomeomorph.trans productHalfSpaceHomeomorph

@[simp] theorem cornerHalfSpace_height (p : Corner) :
    (cornerHalfSpaceHomeomorph p).val 0=min p.2.1.val p.2.2.val := rfl

@[simp] theorem cornerHalfSpace_positive (p : Corner) :
    0<(cornerHalfSpaceHomeomorph p).val 0 ↔ p∈cornerInterior :=
  cornerProduct_positive p

@[simp] theorem cornerHalfSpace_zero (p : Corner) :
    (cornerHalfSpaceHomeomorph p).val 0=0 ↔ p.2.1.val=0 ∨ p.2.2.val=0 :=
  cornerProduct_zero p

end TernaryPoly.SymmetricSpaceBoundaryCharts
