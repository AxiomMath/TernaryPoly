module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.FormCurrent
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.CoordinateDifferential
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.Differential

@[expose] public section

/-! Genuine intrinsic local current differentiation equals the actual form-current differential. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialFormCoordinates SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
  SmoothCoveringDeRham

/-- The actual intrinsic/chart form-current correspondence intertwines the actual intrinsic
support-local differential and the genuine exterior-symbol weak differential. -/
theorem intrinsicChartFormCurrent_differential (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (T : IntrinsicCurrent n k (chartOpen S Ω)) :
    formWeakExterior n k Ω (intrinsicChartFormCurrent n k S Ω hΩ T) =
      intrinsicChartFormCurrent n (k+1) S Ω hΩ (intrinsicCurrentDifferential n k (chartOpen S Ω) T) := by
  apply (Function.LeftInverse.injective (formWeakOfCoordinates_coordinates n (k+1) Ω))
  funext j
  have hu : formWeakCoordinates n k Ω (intrinsicChartFormCurrent n k S Ω hΩ T) =
      intrinsicCurrentCoordinates n k S Ω hΩ T := formWeakCoordinates_ofCoordinates n k Ω _
  have hz : formWeakCoordinates n (k+1) Ω
      (intrinsicChartFormCurrent n (k+1) S Ω hΩ (intrinsicCurrentDifferential n k (chartOpen S Ω) T)) =
      intrinsicCurrentCoordinates n (k+1) S Ω hΩ (intrinsicCurrentDifferential n k (chartOpen S Ω) T) :=
    formWeakCoordinates_ofCoordinates n (k+1) Ω _
  exact (formWeakCoordinates_exterior n k Ω _ j).trans
    ((congrArg (fun w : Index n k → ScalarWeak Ω =>
      ∑ i : Index n k, ∑ d : Fin 5, symbolMatrix n k d j i •
        scalarWeakDerivative Ω (Pi.single d 1) (w i)) hu).trans
      ((intrinsicCurrentCoordinates_differential n k S Ω hΩ j T).symm.trans
        (congrFun hz j).symm))

/-- Actual closed intrinsic currents have actual closed form-valued chart currents. -/
theorem intrinsicChartFormCurrent_closed (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (T : IntrinsicCurrent n k (chartOpen S Ω))
    (hT : intrinsicCurrentDifferential n k (chartOpen S Ω) T = 0) :
    formWeakExterior n k Ω (intrinsicChartFormCurrent n k S Ω hΩ T) = 0 :=
  (intrinsicChartFormCurrent_differential n k S Ω hΩ T).trans
    ((congrArg (intrinsicChartFormCurrent n (k+1) S Ω hΩ) hT).trans
      (intrinsicChartFormCurrent_zero n (k+1) S Ω hΩ))

/-- Reconstructing an intrinsic current commutes with its genuine exterior differential. -/
theorem intrinsicCurrentOfForm_differential (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (W : FormWeak n k Ω) :
    intrinsicCurrentDifferential n k (chartOpen S Ω) (intrinsicCurrentOfForm n k S Ω W) =
      intrinsicCurrentOfForm n (k+1) S Ω (formWeakExterior n k Ω W) := by
  apply (Function.LeftInverse.injective (intrinsicCurrentOfForm_chartFormCurrent n (k+1) S Ω hΩ))
  exact (intrinsicChartFormCurrent_differential n k S Ω hΩ _).symm.trans
    ((congrArg (formWeakExterior n k Ω) (intrinsicChartFormCurrent_ofForm n k S Ω hΩ W)).trans
      (intrinsicChartFormCurrent_ofForm n (k+1) S Ω hΩ _).symm)

end TernaryPoly.PolynomialFormWeakSmooth
