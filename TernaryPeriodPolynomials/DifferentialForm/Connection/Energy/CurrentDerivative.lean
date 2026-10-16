module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.Covector
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence.MetricDual

@[expose] public section


/-! The actual energy covector has the derivative required by inverse-metric divergence. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy SymmetricSpaceCharts
open SmoothCoveringDeRham
open scoped ContDiff Matrix.Norms.Elementwise

def energyCovectorCoordinates (n k : ℕ) (w : Coordinates → FormValue n k) (x : Coordinates) : Coordinates :=
  fun i => energyCovector n k x (w x) (Pi.single i 1)

theorem contDiffOn_energyCovectorCoordinates (n k : ℕ) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) :
    ContDiffOn ℝ ∞ (energyCovectorCoordinates n k w) positiveCoordinates := by
  apply contDiffOn_pi.mpr
  intro i
  exact contDiffOn_formPairing_functions n k (fun _ h => h) hw
    ((contDiffOn_coefficientFormMap n k (contDiffOn_symmetricPart n (Pi.single i 1))).clm_apply hw)

theorem covector_tangentConnection (L : Coordinates →L[ℝ] ℝ) (x u : Coordinates) (j : Fin 5) :
    L (tangentConnection x u (Pi.single j 1)) =
      ∑ r, tangentConnectionMatrix x u r j * L (Pi.single r 1) := by
  rw [congrFun (tangentConnection_matrixAction x u) j]
  simp only [matrixAction, map_sum, map_smul, smul_eq_mul, Matrix.transpose_apply]

theorem fderiv_energyCovectorCoordinates (n k : ℕ) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) (j : Fin 5) :
    fderiv ℝ (energyCovectorCoordinates n k w) x u j =
      2 * formPairing n k x (w x)
        (coefficientFormMap (symmetricPart n x (Pi.single j 1)) k (covariantFormDerivative n k w x u)) +
      ∑ r, tangentConnectionMatrix x u r j * energyCovectorCoordinates n k w x r := by
  have hwa := ((hw x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have h := hasDerivAt_energyCovector_connection n k w x hx u (Pi.single j 1) hwa
  rw [covector_tangentConnection] at h
  have hd := (((contDiffOn_energyCovectorCoordinates n k hw x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  have hl := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_coordinateLine x u)
    (by simp only [zero_smul, add_zero])
  have he := hasDerivAt_pi.mp hl j
  exact he.unique h

end TernaryPoly.PolynomialFormConnection
