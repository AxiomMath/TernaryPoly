module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.Operator
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.Linear

@[expose] public section


/-! Actual parallel coefficient and insertion rules for the symmetric tensor contraction. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy SymmetricSpaceCharts
open SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

theorem covariantFormDerivative_symmetricPart (n k : ℕ) (w : Coordinates → FormValue n k)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates)
    (hw : DifferentiableAt ℝ w x) :
    covariantFormDerivative n k (fun y => coefficientFormMap (symmetricPart n y v) k (w y)) x u =
      coefficientFormMap (symmetricPart n x v) k (covariantFormDerivative n k w x u) +
        coefficientFormMap (symmetricPart n x (tangentConnection x u v)) k (w x) := by
  have hL := (((contDiffOn_symmetricPart n v x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  rw [covariantFormDerivative_coefficientFormMap n k _ w x u hL hw,
    coefficientOperatorDerivative_symmetricPart n x hx u v]

theorem differentiableAt_insertion (n k : ℕ) (w : Coordinates → FormValue n (k + 1))
    (x v : Coordinates) (hw : DifferentiableAt ℝ w x) :
    DifferentiableAt ℝ (fun y => insertion n k v (w y)) x := by
  have hL : HasFDerivAt (insertion n k v) (insertion n k v) (w x) := (insertion n k v).hasFDerivAt
  exact (HasFDerivAt.comp (𝕜 := ℝ) (E := Coordinates) (F := FormValue n (k + 1)) (G := FormValue n k)
    (f := w) (g := insertion n k v) x hL hw.hasFDerivAt).differentiableAt

theorem covariantFormDerivative_contractionBilinear (n k : ℕ) (w : Coordinates → FormValue n (k + 1))
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v z : Coordinates)
    (hw : DifferentiableAt ℝ w x) :
    covariantFormDerivative n k (fun y => contractionBilinear n k y (w y) v z) x u =
      contractionBilinear n k x (covariantFormDerivative n (k + 1) w x u) v z +
        contractionBilinear n k x (w x) (tangentConnection x u v) z +
        contractionBilinear n k x (w x) v (tangentConnection x u z) := by
  change covariantFormDerivative n k
    (fun y => coefficientFormMap (symmetricPart n y v) k (insertion n k z (w y))) x u = _
  rw [covariantFormDerivative_symmetricPart n k _ x hx u v
    (differentiableAt_insertion n k w x z hw), covariantFormDerivative_insertion n k w x u z hw,
    map_add]
  exact add_right_comm
    (contractionBilinear n k x (covariantFormDerivative n (k + 1) w x u) v z)
    (contractionBilinear n k x (w x) v (tangentConnection x u z))
    (contractionBilinear n k x (w x) (tangentConnection x u v) z)

end TernaryPoly.PolynomialFormConnection
