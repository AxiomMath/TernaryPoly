module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Flat.FrameProfile
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.Transport
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.AnalyticFamilies

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart

def completion (frame : Rectangular ℝ) : PlaneMatrix :=
  fun row => ![frame row 0, frame row 1, exterior frame row]

theorem completion_columns (frame : Rectangular ℝ) : columns (completion frame) = frame := by
  ext row column
  fin_cases column <;> rfl

theorem completion_det (frame : Rectangular ℝ) :
    (completion frame).det = ∑ row, (exterior frame row) ^ 2 := by
  rw [det_eq_exterior, completion_columns]
  apply Finset.sum_congr rfl
  intro row _
  change exterior frame row * exterior frame row = _
  exact (pow_two _).symm

theorem completion_det_pos (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    0 < (completion frame).det := by
  rw [completion_det]
  apply Finset.sum_pos' (fun row _ => sq_nonneg _)
  obtain ⟨row, nonzero⟩ : ∃ row, exterior frame row ≠ 0 := by
    by_contra h
    push Not at h
    exact fullRank (funext h)
  exact ⟨row, Finset.mem_univ row, sq_pos_of_ne_zero nonzero⟩

theorem completion_contDiff : ContDiff ℝ ⊤ completion := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  fin_cases row <;> fin_cases column <;>
    simp [completion, exterior, crossProduct] <;> fun_prop

theorem exterior_continuous : Continuous (exterior (ring := ℝ)) := by
  apply continuous_pi
  intro row
  fin_cases row <;> simp [exterior, crossProduct] <;> fun_prop

theorem fullRank_isOpen : IsOpen {frame : Rectangular ℝ | FullRank frame} :=
  isOpen_ne.preimage exterior_continuous

def point (frame : Rectangular ℝ) : RealGL3 := (invertibleMatrix (completion frame))⁻¹

theorem point_inverse_val (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    (point frame)⁻¹.val = completion frame := by
  rw [point, inv_inv, invertibleMatrix_val _ (completion_det_pos frame fullRank).ne']

theorem point_frame (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    (point frame)⁻¹.val * RectangularKernel.standard = frame := by
  rw [point_inverse_val frame fullRank, RectangularKernel.standard, mul_standard, completion_columns]

def inverseMatrix (frame : Rectangular ℝ) : PlaneMatrix := (completion frame)⁻¹

theorem inverseMatrix_det_ne_zero (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    (inverseMatrix frame).det ≠ 0 := by
  rw [inverseMatrix, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero (completion_det_pos frame fullRank).ne'

theorem point_eq (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    point frame = invertibleMatrix (inverseMatrix frame) := by
  apply Units.ext
  rw [invertibleMatrix_val _ (inverseMatrix_det_ne_zero frame fullRank)]
  change (invertibleMatrix (completion frame))⁻¹.val = (completion frame)⁻¹
  rw [Matrix.GeneralLinearGroup.coe_inv, invertibleMatrix_val _ (completion_det_pos frame fullRank).ne']

theorem determinant_contDiff : ContDiff ℝ ⊤ (fun frame : Rectangular ℝ => (completion frame).det) := by
  have determinant : ContDiff ℝ ⊤ (fun matrix : PlaneMatrix => matrix.det) := by
    simp only [Matrix.det_fin_three]
    fun_prop
  exact determinant.comp completion_contDiff

theorem adjugate_contDiff : ContDiff ℝ ⊤ (fun frame : Rectangular ℝ => (completion frame).adjugate) := by
  have adjugate : ContDiff ℝ ⊤ (fun matrix : PlaneMatrix => matrix.adjugate) := by
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    fin_cases row <;> fin_cases column <;> simp [Matrix.adjugate_fin_three] <;> fun_prop
  exact adjugate.comp completion_contDiff

theorem inverseMatrix_contDiffOn : ContDiffOn ℝ ⊤ inverseMatrix {frame : Rectangular ℝ | FullRank frame} := by
  change ContDiffOn ℝ ⊤ (fun frame : Rectangular ℝ => (completion frame)⁻¹) _
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact (determinant_contDiff.contDiffOn.inv (fun frame fullRank => (completion_det_pos frame fullRank).ne')).smul
    adjugate_contDiff.contDiffOn

theorem inverseMatrix_contDiffAt (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    ContDiffAt ℝ ⊤ inverseMatrix frame :=
  inverseMatrix_contDiffOn.contDiffAt (fullRank_isOpen.mem_nhds fullRank)

def adelicFrame (finitePoint : FiniteGL) (frame : Rectangular ℝ) : Rectangular Adeles :=
  fun row column => (frame row column,
    (finitePoint⁻¹.val * (RectangularKernel.standard : Rectangular FiniteAdeles)) row column)

theorem adelicFrame_eq (finitePoint : FiniteGL) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    adelicFrame finitePoint frame = FrameProfile.frame (atFinite finitePoint * atInfinity (point frame)) := by
  have realEquality := point_frame frame fullRank
  unfold adelicFrame FrameProfile.frame
  rw [_root_.mul_inv_rev, Units.val_mul]
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · have equality := congrArg (fun value : Rectangular ℝ => value row column) realEquality.symm
    fin_cases column <;>
      simpa [atFinite, atInfinity, combineGL, pairMatrix, Matrix.mul_apply, Fin.sum_univ_three,
        RectangularKernel.standard, columns, Matrix.one_apply] using equality
  · fin_cases row <;>
      simp [atFinite, atInfinity, combineGL, pairMatrix, Matrix.mul_apply, Fin.sum_univ_three,
        RectangularKernel.standard, columns, Matrix.one_apply]

theorem profile_eq {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (finitePoint : FiniteGL) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    FrameProfile.profile induced (adelicFrame finitePoint frame) =
      FrameProfile.normalized induced (atFinite finitePoint * atInfinity (point frame)) := by
  rw [adelicFrame_eq finitePoint frame fullRank, FrameProfile.profile_frame]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart
