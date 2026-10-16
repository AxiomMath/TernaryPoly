module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
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
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Coordinate volume densities of positive real bilinear forms. -/
noncomputable section
namespace TernaryPoly.BilinearVolumeDensity

open Matrix LinearMap
open LinearMap (BilinForm)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The density in the standard coordinate basis. -/
def density (B : BilinForm ℝ (ι → ℝ)) : ℝ := Real.sqrt B.toMatrix'.det

/-- Positivity of a bilinear form gives positivity of its coordinate Gram matrix. -/
theorem gram_posDef (B : BilinForm ℝ (ι → ℝ))
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v, v ≠ 0 → 0 < B v v) :
    B.toMatrix'.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    simpa only [BilinForm.toMatrix'_apply] using hs (Pi.single j 1) (Pi.single i 1)
  · intro v hv
    simpa only [star_trivial, ← Matrix.toBilin'_apply', Matrix.toBilin'_toMatrix'] using hp v hv

/-- Strict positivity of the coordinate density. -/
theorem density_pos (B : BilinForm ℝ (ι → ℝ))
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v, v ≠ 0 → 0 < B v v) :
    0 < density B := Real.sqrt_pos.mpr (gram_posDef B hs hp).det_pos

/-- Pullback multiplies density by the absolute determinant of the linear map. -/
theorem density_comp (B : BilinForm ℝ (ι → ℝ))
    (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    density (B.comp L L) = |L.det| * density B := by
  unfold density
  rw [BilinForm.toMatrix'_comp, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, LinearMap.det_toMatrix']
  rw [show L.det * B.toMatrix'.det * L.det = (L.det * L.det) * B.toMatrix'.det by ring]
  rw [Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self_eq_abs]

end TernaryPoly.BilinearVolumeDensity
