module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.MetricData
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Regularity

@[expose] public section


/-! The literal metric-volume divergence and the symmetric-connection energy current. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialCoefficientBundle PolynomialFormMetric
open PolynomialFormGeometricEnergy SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
open SmoothCoveringDeRham
open scoped ContDiff Matrix.Norms.Elementwise

/-- Genuine coordinate weighted divergence for the Riemannian density. -/
def weightedDivergence (V : Coordinates → Coordinates) (x : Coordinates) : ℝ :=
  (coordinateDensity x)⁻¹ * ∑ i : Fin 5,
    fderiv ℝ (fun y => coordinateDensity y * V y i) x (Pi.single i 1)

/-- Literal tangent covariance under the actual arithmetic deck action. -/
def IsDeckVectorField (V : Coordinates → Coordinates) : Prop :=
  ∀ (g : DeckGroup) (x : Coordinates), x ∈ positiveCoordinates →
    V (deckMap g x) = fderiv ℝ (deckMap g) x (V x)

/-- The actual metric dual of the one-form pairing a section against its symmetric connection. -/
def energyCurrent (n k : ℕ) (w : Coordinates → FormValue n k) (x : Coordinates) : Coordinates :=
  fun i => ∑ j : Fin 5, (inverseGram x i j) * formPairing n k
    x (w x) (coefficientFormMap (symmetricPart n x (Pi.single j 1)) k (w x))

@[simp] theorem energyCurrent_of_eq_zero (n k : ℕ) (w : Coordinates → FormValue n k)
    (x : Coordinates) (hw : w x = 0) : energyCurrent n k w x = 0 := by
  funext i
  simp only [energyCurrent, hw, formPairing_zero_left, mul_zero, Finset.sum_const_zero, Pi.zero_apply]

theorem contDiffOn_energyCurrent (n k : ℕ) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) :
    ContDiffOn ℝ ∞ (energyCurrent n k w) positiveCoordinates := by
  apply contDiffOn_pi.mpr
  intro i
  apply ContDiffOn.sum
  intro j _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp contDiffOn_inverseGram i) j).mul
    (contDiffOn_formPairing_functions n k (fun _ h => h) hw
      ((contDiffOn_coefficientFormMap n k (contDiffOn_symmetricPart n (Pi.single j 1))).clm_apply hw))

end TernaryPoly.PolynomialFormConnection
