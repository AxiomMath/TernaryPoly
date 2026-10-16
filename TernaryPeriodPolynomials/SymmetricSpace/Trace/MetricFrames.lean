module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricPositive
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

@[expose] public section


/-! Every actual positive form has an invertible Euclidean frame. -/
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix
open scoped MatrixOrder

/-- A positive definite real matrix is g g-transpose for an actual invertible g. -/
theorem exists_positive_frame (S : Mat) (hS : S.PosDef) :
    ∃ g : Matˣ, S = (g : Mat) * star (g : Mat) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hS.posSemidef.nonneg
  have hdetS : S.det ≠ 0 := isUnit_iff_ne_zero.mp ((S.isUnit_iff_isUnit_det).mp hS.isUnit)
  have hdetB : B.det ≠ 0 := by
    intro h
    apply hdetS
    rw [hB, det_mul, h, mul_zero]
  have hu : IsUnit B := (B.isUnit_iff_isUnit_det).mpr (isUnit_iff_ne_zero.mpr hdetB)
  obtain ⟨b, rfl⟩ := hu
  refine ⟨star b, ?_⟩
  simpa using hB

end TernaryPoly.SymmetricSpaceTraceMetric
