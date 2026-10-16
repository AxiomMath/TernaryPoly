module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentDerivative
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Anticommutator

@[expose] public section


/-! Exact pointwise divergence of the genuine symmetric-connection energy current. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy SymmetricSpaceCharts
open SmoothCoveringDeRham
open scoped ContDiff Matrix.Norms.Elementwise

theorem energyCurrent_eq_metricDualCovector (n k : ℕ) (w : Coordinates → FormValue n k) :
    energyCurrent n k w = metricDualCovector (energyCovectorCoordinates n k w) := rfl

theorem inverseGram_entry_symm (x : Coordinates) (hx : x ∈ positiveCoordinates) (i j : Fin 5) :
    inverseGram x i j = inverseGram x j i := by
  have h := Matrix.isHermitian_iff_isSymm.mp (inverseGram_posDef x hx).isHermitian
  exact congrFun (congrFun h.symm i) j

theorem formPairing_symmetricDirectionalTrace (n k : ℕ) (w : Coordinates → FormValue n k)
    (x : Coordinates) :
    formPairing n k x (w x) (symmetricDirectionalTrace n k w x) =
      ∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j * formPairing n k x (w x)
        (coefficientFormMap (symmetricPart n x (Pi.single i 1)) k (covariantFormDerivative n k w x (Pi.single j 1))) := by
  change formContinuousBilin n k x (w x) _ = _
  simp only [symmetricDirectionalTrace, PolynomialFormCoordinates.clm_map_sum,
    PolynomialFormCoordinates.clm_map_smul, smul_eq_mul, formContinuousBilin_apply]

theorem weightedDivergence_energyCurrent (n k : ℕ) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    weightedDivergence (energyCurrent n k w) x =
      2 * formPairing n k x (w x) (symmetricDirectionalTrace n k w x) := by
  have hd := (((contDiffOn_energyCovectorCoordinates n k hw x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  rw [energyCurrent_eq_metricDualCovector]
  rw [weightedDivergence_metricDualCovector _ x hx hd
    (fun i j => 2 * formPairing n k x (w x)
      (coefficientFormMap (symmetricPart n x (Pi.single j 1)) k (covariantFormDerivative n k w x (Pi.single i 1))))
    (fun i j => fderiv_energyCovectorCoordinates n k hw x hx (Pi.single i 1) j)]
  rw [formPairing_symmetricDirectionalTrace, Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [inverseGram_entry_symm x hx j i]
  ring

/-- The actual anticommutator provides a scalar expression suitable for quotient descent. -/
theorem weightedDivergence_energyCurrent_two (n : ℕ) {w : Coordinates → FormValue n 2}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    weightedDivergence (energyCurrent n 2 w) x =
      2 * formPairing n 2 x (w x)
        (symmetricContraction n 2 x (covariantExterior n 2 w x) +
          covariantExterior n 1 (fun y => symmetricContraction n 1 y (w y)) x) := by
  rw [weightedDivergence_energyCurrent n 2 hw x hx,
    covariant_contraction_anticommutator_two n w x hx
      (((hw x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))]

end TernaryPoly.PolynomialFormConnection
