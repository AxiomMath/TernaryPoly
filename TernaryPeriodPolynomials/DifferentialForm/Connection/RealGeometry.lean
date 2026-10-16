module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tangent.Sections

@[expose] public section


/-! Actual real congruence transport with determinant-square one. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

theorem conjugate_det_of_sq_one (g : RealGL) (hg : g.val.det ^ 2 = 1) (S : Mat) :
    (conjugate g S).det = S.det := by
  simp only [conjugate, Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, star_trivial]
  calc g.val.det * S.det * g.val.det = g.val.det ^ 2 * S.det := by ring
    _ = S.det := by rw [hg, one_mul]

theorem determinantNormalize_real_conjugate (g : RealGL) (hg : g.val.det ^ 2 = 1) (S : Mat) :
    determinantNormalize (conjugate g S) = conjugate g (determinantNormalize S) := by
  rw [determinantNormalize, conjugate_det_of_sq_one g hg, determinantNormalize, conjugate_smul]

theorem coordinateForm_real (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    coordinateForm (coordinateAction g x) = conjugate g (coordinateForm x) := by
  rw [coordinateForm, reconstruct_coordinateAction g x hx]
  change determinantNormalize ((conjugate g (reconstruct x)).trace⁻¹ • conjugate g (reconstruct x)) = _
  rw [determinantNormalize_smul _ (inv_pos.mpr (conjugate_positive g _ hx).trace_pos)
    _ (conjugate_positive g _ hx)]
  exact determinantNormalize_real_conjugate g hg (reconstruct x)

theorem formDerivative_real (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (v : Coordinates) :
    formDerivative (coordinateAction g x) (fderiv ℝ (coordinateAction g) x v) =
      conjugate g (formDerivative x v) := by
  have hF := (((contDiffOn_coordinateAction g x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  have hQ := coordinateForm_differentiable (coordinateAction g x) (coordinateAction_mem g x hx)
  have hl := hQ.hasFDerivAt.comp x hF.hasFDerivAt
  have hr := (congruenceCLM g).hasFDerivAt.comp x (coordinateForm_differentiable x hx).hasFDerivAt
  have hL : HasFDerivAt (fun y => conjugate g (coordinateForm y))
      ((fderiv ℝ coordinateForm (coordinateAction g x)).comp (fderiv ℝ (coordinateAction g) x)) x := by
    apply hl.congr_of_eventuallyEq
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    exact (coordinateForm_real g hg y hy).symm
  have he := congrArg (fun L => L v) (hL.unique hr)
  convert! he using 1

theorem logarithmicForm_real (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (v : Coordinates) :
    logarithmicForm (coordinateAction g x) (fderiv ℝ (coordinateAction g) x v) =
      g.val * logarithmicForm x v * g.val⁻¹ := by
  rw [logarithmicForm, formDerivative_real g hg x hx v, coordinateForm_real g hg x hx]
  obtain ⟨S, hS⟩ := (coordinateForm_positive x hx).isUnit
  have h := right_inverse_congruence_tangent g S (formDerivative x v)
  simpa only [conjugate, Units.val_mul, Units.coe_star, Matrix.coe_units_inv, logarithmicForm, ← hS] using h

/-- Literal coefficient action by inverse substitution. -/
def realCoefficientMap (n : ℕ) (g : RealGL) : Coefficients n →L[ℝ] Coefficients n :=
  (coefficientSubstitution n g.val⁻¹).toContinuousLinearMap

theorem symmetricPart_real (n : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (v : Coordinates) (p : Coefficients n) :
    symmetricPart n (coordinateAction g x) (fderiv ℝ (coordinateAction g) x v) (realCoefficientMap n g p) =
      realCoefficientMap n g (symmetricPart n x v p) := by
  change symmetricPart n (coordinateAction g x) (fderiv ℝ (coordinateAction g) x v)
    (coefficientSubstitution n g.val⁻¹ p) = coefficientSubstitution n g.val⁻¹ (symmetricPart n x v p)
  simp only [symmetricPart, _root_.smul_apply, infinitesimalCLM_apply, map_smul]
  rw [logarithmicForm_real g hg x hx v, coefficientInfinitesimal_conjugation n g.val (logarithmicForm x v) g.isUnit]

end TernaryPoly.PolynomialFormConnection
