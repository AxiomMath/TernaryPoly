module

public import TernaryPeriodPolynomials.SymmetricSpace.PositiveAction
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceCornerDegeneration
open Matrix SymmetricSpacePositive

/-- Positive semidefinite matrices have strictly positive trace as soon as they are nonzero. -/
theorem psd_trace_pos {M : Mat} (hM : M.PosSemidef) (hne : M≠0) : 0<M.trace := by
  have ht : M.trace≠0 := fun h => hne (hM.trace_eq_zero_iff.mp h)
  exact lt_of_le_of_ne hM.trace_nonneg (Ne.symm ht)

theorem normalize_psd {M : Mat} (hM : M.PosSemidef) (hne : M≠0) :
    (SymmetricSpacePositive.normalize M).PosSemidef :=
  hM.smul (inv_nonneg.mpr (psd_trace_pos hM hne).le)

theorem normalize_trace {M : Mat} (ht : M.trace≠0) :
    (SymmetricSpacePositive.normalize M).trace=1 := by
  rw [SymmetricSpacePositive.normalize,Matrix.trace_smul,smul_eq_mul,inv_mul_cancel₀ ht]

theorem normalize_ne_zero {M : Mat} (ht : M.trace≠0) :
    SymmetricSpacePositive.normalize M≠0 := by
  intro h
  have he := normalize_trace ht
  rw [h,Matrix.trace_zero] at he
  exact zero_ne_one he

theorem rank_normalize {M : Mat} (ht : M.trace≠0) :
    (SymmetricSpacePositive.normalize M).rank=M.rank :=
  Matrix.rank_smul_of_mem_nonZeroDivisors M (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero ht))

theorem conjugate_psd (g : RealGL) {M : Mat} (hM : M.PosSemidef) :
    (conjugate g M).PosSemidef :=
  g.isUnit.posSemidef_star_right_conjugate_iff.mpr hM

theorem conjugate_ne_zero (g : RealGL) {M : Mat} (hne : M≠0) : conjugate g M≠0 := by
  intro h
  apply hne
  calc
    M=conjugate g⁻¹ (conjugate g M) := by rw [←conjugate_mul,inv_mul_cancel,conjugate_one]
    _=0 := by rw [h]; simp [conjugate]

theorem conjugate_trace_pos (g : RealGL) {M : Mat} (hM : M.PosSemidef) (hne : M≠0) :
    0<(conjugate g M).trace := psd_trace_pos (conjugate_psd g hM) (conjugate_ne_zero g hne)

theorem rank_conjugate (g : RealGL) (M : Mat) : (conjugate g M).rank=M.rank := by
  unfold conjugate
  rw [Matrix.rank_mul_eq_left_of_isUnit_det (star g.val) (g.val*M)
    (Matrix.isUnit_iff_isUnit_det _ |>.mp g.isUnit.star)]
  exact Matrix.rank_mul_eq_right_of_isUnit_det g.val M (Matrix.isUnits_det_units g)

theorem rank_normalized_conjugate (g : RealGL) {M : Mat} (hM : M.PosSemidef) (hne : M≠0) :
    (SymmetricSpacePositive.normalize (conjugate g M)).rank=M.rank := by
  rw [rank_normalize (ne_of_gt (conjugate_trace_pos g hM hne)),rank_conjugate]

/-- Normalized congruence is continuous on any continuously parameterized nonzero PSD family. -/
theorem continuous_normalized_conjugate {X : Type*} [TopologicalSpace X]
    (g : RealGL) {f : X → Mat} (hf : Continuous f)
    (hpsd : ∀ x, (f x).PosSemidef) (hne : ∀ x, f x≠0) :
    Continuous (fun x => SymmetricSpacePositive.normalize (conjugate g (f x))) := by
  have hc : Continuous (fun x => conjugate g (f x)) :=
    (continuous_const.mul hf).mul continuous_const
  exact (hc.matrix_trace.inv₀ (fun x => ne_of_gt (conjugate_trace_pos g (hpsd x) (hne x)))).smul hc

end TernaryPoly.SymmetricSpaceCornerDegeneration
