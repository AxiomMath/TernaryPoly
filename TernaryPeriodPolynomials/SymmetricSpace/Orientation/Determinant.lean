module

public import TernaryPeriodPolynomials.SymmetricSpace.Orientation.Transvections

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceOrientation
open Matrix

/-- The actual symmetric-square matrix has determinant det(g)^4, even for singular g. -/
theorem coordinateMatrix_det (g : Mat3) : (coordinateMatrix g).det = g.det^4 := by
  apply Matrix.diagonal_transvection_induction
    (fun h : Mat3 => (coordinateMatrix h).det = h.det^4) g
  · intro d _
    exact coordinateMatrix_det_diagonal d
  · intro t
    rw [coordinateMatrix_det_transvection,t.det,one_pow]
  · intro h k hh hk
    rw [coordinateMatrix_mul,Matrix.det_mul,hh,hk,Matrix.det_mul,mul_pow]

/-- Determinant of the actual linear action in the explicit six-coordinate basis. -/
theorem coordinateAction_det (g : Mat3) : LinearMap.det (coordinateAction g) = g.det^4 := by
  rw [←LinearMap.det_toMatrix',←coordinateMatrix_eq_toMatrix,coordinateMatrix_det]

/-- Coordinate-free determinant of actual congruence on the symmetric-matrix subspace. -/
theorem congruence_det (g : Mat3) : LinearMap.det (congruence g) = g.det^4 := by
  calc
    _ = LinearMap.det (coordinateAction g) :=
      (LinearMap.det_conj (congruence g) coordinatesEquiv).symm
    _ = g.det^4 := coordinateAction_det g

/-- The actual real symmetric 3x3 matrix space has dimension six. -/
theorem symmetric_finrank : Module.finrank ℝ Symmetric = 6 := by
  have h := coordinatesEquiv.finrank_eq
  simpa only [Module.finrank_fin_fun] using h

end TernaryPoly.SymmetricSpaceOrientation
