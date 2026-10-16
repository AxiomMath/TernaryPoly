module

public import Mathlib.NumberTheory.ModularForms.LFunction
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Tactic
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.SpecificLimits.RCLike
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Perm.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.MvPowerSeries.LexOrder
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Order.ExtrClosure
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.WithTopology

@[expose] public section

noncomputable section
open Complex Filter Asymptotics
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

namespace TernaryPoly.BinaryCuspPeriod

/-- The actual space of full-level holomorphic cusp forms of weight `d + 2`. -/
abbrev Forms (d : ℕ) := CuspForm 𝒮ℒ ((d : ℤ) + 2)

/-- Fourier coefficients in the width-one expansion at infinity. -/
def coefficients {d : ℕ} (f : Forms d) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n

/-- The actual imaginary-axis Mellin integral, with Mathlib's normalization. -/
def moment {d : ℕ} (f : Forms d) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => f (ofComplex (I * t))) s

theorem weight_pos (d : ℕ) : (0 : ℤ) < (d : ℤ) + 2 := by omega

/-- The imaginary-axis Mellin integral is convergent at every complex argument. -/
theorem moment_convergent {d : ℕ} (f : Forms d) (s : ℂ) :
    MellinConvergent (fun t : ℝ => f (ofComplex (I * t))) s :=
  ((CuspForm.isStrongFEPair (weight_pos d) f).hasMellin s).1

/-- Hecke's coefficient bound, specialized to the actual full-level cusp form. -/
theorem coefficient_growth {d : ℕ} (f : Forms d) :
    coefficients f =O[atTop] (fun n : ℕ => (n : ℝ) ^ (((d : ℝ) + 2) / 2)) := by
  change (fun n => (qExpansion 1 f).coeff n) =O[atTop] _
  simpa [Subgroup.strictWidthInfty_SL2Z] using
    CuspFormClass.qExpansion_isBigO f

/-- The outer critical value lies in the absolute-convergence half-plane when `d > 4`. -/
theorem lseries_summable {d : ℕ} (hd : 4 < d) (f : Forms d) :
    LSeriesSummable (coefficients f) (d : ℂ) := by
  apply LSeriesSummable_of_isBigO_rpow (x := ((d : ℝ) + 2) / 2 + 1)
  · simp only [natCast_re]
    have : (4 : ℝ) < d := by exact_mod_cast hd
    linarith
  · simpa using coefficient_growth f

/-- Absolute convergence, in the norm-summability form consumed by Euler products. -/
theorem norm_terms_summable {d : ℕ} (hd : 4 < d) (f : Forms d) :
    Summable (fun n => ‖LSeries.term (coefficients f) (d : ℂ) n‖) :=
  (summable_norm_iff).mpr (lseries_summable hd f)

/-- At the outer critical point, Mathlib's analytic continuation is the actual Dirichlet sum. -/
theorem lseries_eq_L {d : ℕ} (hd : 4 < d) (f : Forms d) :
    LSeries (coefficients f) (d : ℂ) = ModularForm.L (weight_pos d) f (d : ℂ) := by
  have hs : (((d : ℤ) + 2 : ℤ) : ℝ) / 2 + 1 < (d : ℂ).re := by
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat, natCast_re]
    have : (4 : ℝ) < d := by exact_mod_cast hd
    linarith
  have h := CuspForm.hasSum_L (weight_pos d) f hs
  rw [Subgroup.strictWidthInfty_SL2Z] at h
  simp only [ofReal_one, one_cpow, one_mul] at h
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  simpa only [LSeries, LSeries.term_of_ne_zero' hd0, coefficients] using h.tsum_eq

/-- Exact Mellin normalization, retaining the usual complex Gamma function. -/
theorem moment_nat_eq {d : ℕ} (hd : 0 < d) (f : Forms d) :
    moment f (d : ℂ) = Gamma (d : ℂ) / (2 * (Real.pi : ℂ)) ^ d *
      ModularForm.L (weight_pos d) f (d : ℂ) := by
  have hg : Gamma (d : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa only [natCast_re] using (show (0 : ℝ) < d by exact_mod_cast hd))
  have hp : (2 * (Real.pi : ℂ)) ^ d ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [ModularForm.L, CuspForm.Λ_eq_mellin]
  change moment f (d : ℂ) = Gamma (d : ℂ) / (2 * (Real.pi : ℂ)) ^ d *
    (moment f (d : ℂ) * (2 / Gammaℂ (d : ℂ)))
  rw [Gammaℂ_def, cpow_neg, cpow_natCast]
  field_simp

end TernaryPoly.BinaryCuspPeriod
