module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.MetricSections
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.ParallelRules
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence

@[expose] public section


/-! The genuine symmetric-connection current covector and its covariant derivative. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy SymmetricSpaceCharts
open SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

theorem formPairing_symmetricPart_selfAdjoint (n k : ℕ) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (u : Coordinates) (a b : FormValue n k) :
    formPairing n k x (coefficientFormMap (symmetricPart n x u) k a) b =
      formPairing n k x a (coefficientFormMap (symmetricPart n x u) k b) := by
  simp only [formPairing_formula]
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  congr 1
  exact symmetricPart_selfAdjoint n x hx u _ _

/-- The true scalar covector whose inverse-metric dual is the energy current. -/
def energyCovector (n k : ℕ) (x : Coordinates) (a : FormValue n k) : Coordinates →L[ℝ] ℝ :=
  (formContinuousBilin n k x a).comp (symmetricFormDerivative n k x a)

@[simp] theorem energyCovector_apply (n k : ℕ) (x v : Coordinates) (a : FormValue n k) :
    energyCovector n k x a v =
      formPairing n k x a (coefficientFormMap (symmetricPart n x v) k a) := rfl

theorem differentiableAt_symmetricFormSection (n k : ℕ) (w : Coordinates → FormValue n k)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (v : Coordinates)
    (hw : DifferentiableAt ℝ w x) :
    DifferentiableAt ℝ (fun y => coefficientFormMap (symmetricPart n y v) k (w y)) x := by
  have hL := (((contDiffOn_coefficientFormMap n k (contDiffOn_symmetricPart n v) x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  convert! DifferentiableAt.clm_apply (𝕜 := ℝ) (E := Coordinates) (G := FormValue n k) (H := FormValue n k)
    (c := fun y => coefficientFormMap (symmetricPart n y v) k) (u := w) (x := x)
    (by convert! hL using 1) (by convert! hw using 1) using 1

theorem hasDerivAt_energyCovector_connection (n k : ℕ) (w : Coordinates → FormValue n k)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates)
    (hw : DifferentiableAt ℝ w x) :
    HasDerivAt (fun t : ℝ => energyCovector n k (x + t • u) (w (x + t • u)) v)
      (2 * formPairing n k x (w x)
        (coefficientFormMap (symmetricPart n x v) k (covariantFormDerivative n k w x u)) +
          energyCovector n k x (w x) (tangentConnection x u v)) 0 := by
  have h := hasDerivAt_formPairing_connection n k x hx u w
    (fun y => coefficientFormMap (symmetricPart n y v) k (w y)) hw
    (differentiableAt_symmetricFormSection n k w x hx v hw)
  rw [covariantFormDerivative_symmetricPart n k w x hx u v hw] at h
  rw [formPairing_symm n k x hx (covariantFormDerivative n k w x u),
    formPairing_symmetricPart_selfAdjoint n k x hx v] at h
  convert! h using 1
  change 2 * formPairing n k x (w x)
      (coefficientFormMap (symmetricPart n x v) k (covariantFormDerivative n k w x u)) +
      formPairing n k x (w x) (coefficientFormMap (symmetricPart n x (tangentConnection x u v)) k (w x)) = _
  rw [formPairing_add_right]
  ring

end TernaryPoly.PolynomialFormConnection
