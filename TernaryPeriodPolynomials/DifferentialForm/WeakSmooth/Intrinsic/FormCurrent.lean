module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.CurrentCoordinates
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.Current

@[expose] public section


/-! Exact intrinsic local currents and their actual form-valued compact-test coordinate currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialFormCoordinates PolynomialFormHilbert SymmetricSpaceCharts SymmetricSpacePositive
  SymmetricSpaceCovering SmoothCoveringDeRham

/-- The actual form-valued chart current of an intrinsic quotient current. -/
def intrinsicChartFormCurrent (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (T : IntrinsicCurrent n k (chartOpen S Ω)) : FormWeak n k Ω :=
  formWeakOfCoordinates n k Ω (intrinsicCurrentCoordinates n k S Ω hΩ T)

/-- The actual intrinsic quotient current obtained from an actual form-valued chart current. -/
def intrinsicCurrentOfForm (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (W : FormWeak n k Ω) : IntrinsicCurrent n k (chartOpen S Ω) :=
  intrinsicCurrentOfCoordinates n k S Ω (formWeakCoordinates n k Ω W)

/-- Passing from actual form currents to intrinsic currents and back recovers the original. -/
theorem intrinsicChartFormCurrent_ofForm (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (W : FormWeak n k Ω) :
    intrinsicChartFormCurrent n k S Ω hΩ (intrinsicCurrentOfForm n k S Ω W) = W :=
  (congrArg (formWeakOfCoordinates n k Ω)
    (intrinsicCurrentCoordinates_ofCoordinates n k S Ω hΩ (formWeakCoordinates n k Ω W))).trans
      (formWeakOfCoordinates_coordinates n k Ω W)

/-- Passing from actual intrinsic currents to form currents and back recovers the original. -/
theorem intrinsicCurrentOfForm_chartFormCurrent (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (T : IntrinsicCurrent n k (chartOpen S Ω)) :
    intrinsicCurrentOfForm n k S Ω (intrinsicChartFormCurrent n k S Ω hΩ T) = T :=
  (congrArg (intrinsicCurrentOfCoordinates n k S Ω)
    (formWeakCoordinates_ofCoordinates n k Ω (intrinsicCurrentCoordinates n k S Ω hΩ T))).trans
      (intrinsicCurrentOfCoordinates_coordinates n k S Ω hΩ T)

/-- The genuine intrinsic chart-current correspondence preserves zero. -/
theorem intrinsicChartFormCurrent_zero (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target) :
    intrinsicChartFormCurrent n k S Ω hΩ 0 = 0 := by
  apply LinearMap.ext
  intro φ
  change (coordinates n k).symm (fun _ => 0) = 0
  exact map_zero (coordinates n k).symm

/-- The intrinsic Hilbert current has exactly the constructed actual Hilbert form
current in every genuine chart. -/
theorem intrinsicChartFormCurrent_hilbert (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (u : Hilbert n k) :
    intrinsicChartFormCurrent n k S Ω hΩ (intrinsicHilbertCurrent n k (chartOpen S Ω) u) =
      chartHilbertFormCurrent n k S Ω hΩ u := rfl

end TernaryPoly.PolynomialFormWeakSmooth
