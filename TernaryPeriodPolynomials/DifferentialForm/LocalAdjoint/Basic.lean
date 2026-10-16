module

public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Gram
public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Differential
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalRegularity
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.OperatorSupport

@[expose] public section


/-! The genuine local formal adjoint of the polynomial-coefficient exterior derivative. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceRiemannian CompactCoordinateIntegration
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise

/-- The literal weighted transpose-divergence in the actual form bases. -/
def localAdjoint (n k : ℕ) (w : Coordinates → FormValue n (k + 1)) (x : Coordinates) : FormValue n k :=
  (coordinates n k).symm (fun i => weightedMatrixAdjoint (weightedGram n k)
    (weightedGram n (k + 1)) (fun d : Fin 5 => Pi.single d 1) (differentialCoefficients n k)
    (fun _ _ _ _ => 0) (components n (k + 1) w) i x)

@[simp] theorem components_localAdjoint (n k : ℕ) (w : Coordinates → FormValue n (k + 1)) :
    components n k (localAdjoint n k w) = weightedMatrixAdjoint (weightedGram n k)
      (weightedGram n (k + 1)) (fun d : Fin 5 => Pi.single d 1) (differentialCoefficients n k)
      (fun _ _ _ _ => 0) (components n (k + 1) w) := by
  funext i x
  change ((coordinates n k) ((coordinates n k).symm _)) i = _
  rw [(coordinates n k).apply_symm_apply]

/-- Scalar coordinates of genuine smooth forms are smooth. -/
theorem contDiffOn_components (n k : ℕ) {w : Coordinates → FormValue n k}
    {U : Set Coordinates} (hw : ContDiffOn ℝ ∞ w U) (i : Index n k) :
    ContDiffOn ℝ ∞ (components n k w i) U := by
  have hc : ContDiff ℝ ∞ (coordinates n k) :=
    ContinuousLinearEquiv.contDiff (𝕜 := ℝ) (E := FormValue n k) (F := Index n k → ℝ)
      (coordinates n k)
  have ht := ContDiff.comp_contDiffOn (𝕜 := ℝ) (E := Coordinates) (F := FormValue n k)
    (G := Index n k → ℝ) hc hw
  exact contDiffOn_pi.mp ht i

/-- Scalar coordinates create no additional support. -/
theorem tsupport_components (n k : ℕ) (w : Coordinates → FormValue n k) (i : Index n k) :
    tsupport (components n k w i) ⊆ tsupport w := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  simp only [components, hx, ContinuousLinearEquiv.map_zero, Pi.zero_apply]

/-- The actual local adjoint is smooth on the genuine positive coordinate domain. -/
theorem contDiffOn_localAdjoint (n k : ℕ) {w : Coordinates → FormValue n (k + 1)}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) :
    ContDiffOn ℝ ∞ (localAdjoint n k w) positiveCoordinates := by
  change ContDiffOn ℝ ∞ ((coordinates n k).symm ∘ _) positiveCoordinates
  apply ContDiff.comp_contDiffOn (𝕜 := ℝ) (E := Coordinates) (F := Index n k → ℝ)
    (G := FormValue n k) (coordinates n k).symm.contDiff
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_weightedMatrixAdjoint isOpen_positiveCoordinates
  · intro i l
    exact contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram_inverse n k) i) l
  · intro j l
    exact contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram n (k + 1)) j) l
  · intros; exact contDiffOn_const
  · intros; exact contDiffOn_const
  · intro j
    exact contDiffOn_components n (k + 1) hw j

end TernaryPoly.PolynomialFormCoordinates
