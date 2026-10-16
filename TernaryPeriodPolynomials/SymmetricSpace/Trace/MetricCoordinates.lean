module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricDefinite
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricBilinear
public import TernaryPeriodPolynomials.SymmetricSpace.ChartsBasic

@[expose] public section


/-! The invariant metric in the exact five coordinates of the arithmetic space. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix SymmetricSpaceCharts

/-- The actual derivative of the trace-one reconstruction map. -/
def tangentMatrix (v : Coordinates) : Mat :=
  !![v 0,v 1,v 2;v 1,v 3,v 4;v 2,v 4,-v 0-v 3]

@[simp] theorem tangentMatrix_add (v w : Coordinates) :
    tangentMatrix (v + w) = tangentMatrix v + tangentMatrix w := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [tangentMatrix]
  all_goals ring

@[simp] theorem tangentMatrix_smul (c : ℝ) (v : Coordinates) :
    tangentMatrix (c • v) = c • tangentMatrix v := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [tangentMatrix]
  all_goals ring

@[simp] theorem extract_tangentMatrix (v : Coordinates) : extract (tangentMatrix v) = v := by
  ext i
  fin_cases i <;> rfl

theorem tangentMatrix_injective : Function.Injective tangentMatrix :=
  Function.LeftInverse.injective extract_tangentMatrix

theorem tangentMatrix_isHermitian (v : Coordinates) : (tangentMatrix v).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem tangentMatrix_trace (v : Coordinates) : (tangentMatrix v).trace = 0 := by
  simp [tangentMatrix, Matrix.trace, Fin.sum_univ_succ]

@[simp] theorem tangentMatrix_zero : tangentMatrix 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tangentMatrix]

/-- The genuine coordinate tangent pairing, before introducing any bundle norms. -/
def coordinatePair (x v w : Coordinates) : ℝ :=
  tangentPair (reconstruct x) (tangentMatrix v) (tangentMatrix w)

theorem coordinatePair_comm (x v w : Coordinates) : coordinatePair x v w = coordinatePair x w v :=
  tangentPair_comm _ _ _

theorem coordinatePair_pos (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) (hv : v ≠ 0) : 0 < coordinatePair x v v := by
  apply tangentPair_self_pos _ _ hx (reconstruct_trace x)
    (tangentMatrix_isHermitian v) (tangentMatrix_trace v)
  intro h
  apply hv
  apply tangentMatrix_injective
  simpa using h

/-- The exact positive coordinate bilinear form. -/
def coordinateBilin (x : Coordinates) : Coordinates →ₗ[ℝ] Coordinates →ₗ[ℝ] ℝ where
  toFun v :=
    { toFun := coordinatePair x v
      map_add' := fun w z => by simp [coordinatePair, tangentPair_add_right]
      map_smul' := fun c w => by simp [coordinatePair, tangentPair_smul_right] }
  map_add' v w := by
    apply LinearMap.ext
    intro z
    change coordinatePair x (v + w) z = coordinatePair x v z + coordinatePair x w z
    simp [coordinatePair, tangentPair_add_left]
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    change coordinatePair x (c • v) w = c * coordinatePair x v w
    simp [coordinatePair, tangentPair_smul_left]

@[simp] theorem coordinateBilin_apply (x v w : Coordinates) : coordinateBilin x v w = coordinatePair x v w := rfl

end TernaryPoly.SymmetricSpaceTraceMetric
