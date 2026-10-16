module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalHomologyCoefficients

/-- Over ℚ, a linear map annihilating the kernel of f factors through f, with arbitrary
target module; extension from the range uses vector-space complements, not finite dimension. -/
theorem factor_of_ker_le {A B V : ModuleCat.{0} ℚ} (f : A →ₗ[ℚ] B) (φ : A →ₗ[ℚ] V)
    (h : LinearMap.ker f ≤ LinearMap.ker φ) : ∃ ψ : B →ₗ[ℚ] V, ψ.comp f = φ := by
  let r : LinearMap.range f →ₗ[ℚ] V :=
    ((LinearMap.ker f).liftQ φ h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ,hψ⟩ := LinearMap.exists_extend r
  refine ⟨ψ, ?_⟩
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hψ (⟨f x,⟨x,rfl⟩⟩ : LinearMap.range f)
  change ψ (f x) = r ⟨f x,⟨x,rfl⟩⟩ at hx
  refine hx.trans ?_
  change (LinearMap.ker f).liftQ φ h (f.quotKerEquivRange.symm ⟨f x,⟨x,rfl⟩⟩) = φ x
  erw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

end TernaryPoly.RationalHomologyCoefficients
