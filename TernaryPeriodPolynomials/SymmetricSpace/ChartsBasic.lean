module

public import TernaryPeriodPolynomials.SymmetricSpace.Positive
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section


open Matrix
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace TernaryPoly.SymmetricSpaceCharts
open SymmetricSpacePositive

abbrev Coordinates := Fin 5 → ℝ

/-- The five independent entries in the fixed convention (00,01,02,11,12). -/
def extract (S : Mat) : Coordinates := ![S 0 0,S 0 1,S 0 2,S 1 1,S 1 2]

/-- Symmetry and trace one determine the missing entries, including S22=1-S00-S11. -/
def reconstruct (x : Coordinates) : Mat :=
  !![x 0,x 1,x 2;x 1,x 3,x 4;x 2,x 4,1-x 0-x 3]

theorem reconstruct_isSymm (x : Coordinates) : (reconstruct x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem reconstruct_isHermitian (x : Coordinates) : (reconstruct x).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (reconstruct_isSymm x)

@[simp] theorem reconstruct_trace (x : Coordinates) : (reconstruct x).trace=1 := by
  simp [reconstruct,Matrix.trace,Fin.sum_univ_succ]

@[simp] theorem extract_reconstruct (x : Coordinates) : extract (reconstruct x)=x := by
  ext i
  fin_cases i <;> rfl

/-- The exact five coordinates recover every symmetric matrix of trace one. -/
theorem reconstruct_extract (S : Mat) (hS : S.IsSymm) (ht : S.trace=1) :
    reconstruct (extract S)=S := by
  have hsum : S 0 0+S 1 1+S 2 2=1 := by
    simpa [Matrix.trace,Fin.sum_univ_succ,add_assoc] using ht
  ext i j
  fin_cases i <;> fin_cases j
  all_goals try (first | rfl | exact hS.apply _ _)
  change 1-S 0 0-S 1 1=S 2 2
  linarith

theorem contDiff_extract : ContDiff ℝ ∞ extract := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply_apply ℝ ℝ 0 0
  · exact contDiff_apply_apply ℝ ℝ 0 1
  · exact contDiff_apply_apply ℝ ℝ 0 2
  · exact contDiff_apply_apply ℝ ℝ 1 1
  · exact contDiff_apply_apply ℝ ℝ 1 2

theorem contDiff_reconstruct : ContDiff ℝ ∞ reconstruct := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact contDiff_apply ℝ ℝ 0
  · exact contDiff_apply ℝ ℝ 1
  · exact contDiff_apply ℝ ℝ 2
  · exact contDiff_apply ℝ ℝ 1
  · exact contDiff_apply ℝ ℝ 3
  · exact contDiff_apply ℝ ℝ 4
  · exact contDiff_apply ℝ ℝ 2
  · exact contDiff_apply ℝ ℝ 4
  · exact (contDiff_const.sub (contDiff_apply ℝ ℝ 0)).sub (contDiff_apply ℝ ℝ 3)

theorem continuous_extract : Continuous extract := contDiff_extract.continuous

theorem continuous_reconstruct : Continuous reconstruct := contDiff_reconstruct.continuous

/-- The explicit coordinate image of the positive-definite trace-one space. -/
def positiveCoordinates : Set Coordinates := {x | (reconstruct x).PosDef}

abbrev PositiveCoordinates := positiveCoordinates

theorem reconstruct_mem (x : Coordinates) (hx : x∈positiveCoordinates) :
    reconstruct x∈traceOnePositive := ⟨hx,reconstruct_trace x⟩

theorem extract_mem (S : Space) : extract S.val∈positiveCoordinates := by
  change (reconstruct (extract S.val)).PosDef
  rw [reconstruct_extract S.val (Matrix.isHermitian_iff_isSymm.mp S.property.1.isHermitian)
    S.property.2]
  exact S.property.1

end TernaryPoly.SymmetricSpaceCharts
