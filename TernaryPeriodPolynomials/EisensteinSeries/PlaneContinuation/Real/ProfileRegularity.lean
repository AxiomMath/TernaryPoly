module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.FrameChart

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealProfileRegularity

theorem point_det (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    (GeneralLinearGroup.det (point frame)).val = (RealFrameChart.completion frame).det⁻¹ := by
  rw [point, map_inv, Units.val_inv_eq_inv_val]
  change (invertibleMatrix (RealFrameChart.completion frame)).val.det⁻¹ = _
  rw [invertibleMatrix_val _ (completion_det_pos frame fullRank).ne']

theorem outer_point {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    outerCharacter data parameter (GeneralLinearGroup.det (atInfinity (point frame))) =
      Complex.exp ((2 * inductionExponent .plane parameter) * (Real.log (RealFrameChart.completion frame).det : ℂ)) := by
  have positive : 0 < (GeneralLinearGroup.det (point frame)).val := by
    rw [point_det frame fullRank]
    exact inv_pos.mpr (completion_det_pos frame fullRank)
  change data.chi.toMonoidHom (GeneralLinearGroup.det (atInfinity (point frame))) *
    normPower (GeneralLinearGroup.det (atInfinity (point frame))) (-2 * inductionExponent .plane parameter) = _
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.det_atInfinity, data.chi.positiveReal _ positive, one_mul, normPower, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_real]
  rw [point_det frame fullRank, abs_of_pos (inv_pos.mpr (completion_det_pos frame fullRank)), Real.log_inv, Complex.ofReal_neg]
  congr 1
  ring

def coefficient {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (finitePoint : FiniteGL)
    (frame : Rectangular ℝ) : ℂ :=
  (outerCharacter data parameter (GeneralLinearGroup.det (atFinite finitePoint)))⁻¹ *
    Complex.exp ((-2 * inductionExponent .plane parameter) * (Real.log (RealFrameChart.completion frame).det : ℂ))

theorem coefficient_eq {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (finitePoint : FiniteGL)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    coefficient data parameter finitePoint frame =
      (outerCharacter data parameter (GeneralLinearGroup.det (atFinite finitePoint * atInfinity (point frame))))⁻¹ := by
  rw [map_mul, map_mul, outer_point data parameter frame fullRank, mul_inv]
  unfold coefficient
  rw [← Complex.exp_neg]
  congr 2
  ring

theorem coefficient_contDiffOn {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (finitePoint : FiniteGL) :
    ContDiffOn ℝ ⊤ (coefficient data parameter finitePoint) {frame : Rectangular ℝ | FullRank frame} := by
  have logarithm := RealFrameChart.determinant_contDiff.contDiffOn.log
    (fun frame (fullRank : FullRank frame) => (completion_det_pos frame fullRank).ne')
  exact contDiffOn_const.mul (Complex.contDiff_exp.comp_contDiffOn
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn logarithm)))

def cuspModel {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : FiniteGL) (frame : Rectangular ℝ) : data.cusp.H :=
  (planeCuspVector induced (atFinite finitePoint * atInfinity (invertibleMatrix (inverseMatrix frame)))).val

theorem cuspModel_contDiffOn {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : FiniteGL) :
    ContDiffOn ℝ ⊤ (cuspModel induced finitePoint) {frame : Rectangular ℝ | FullRank frame} := by
  have smoothVector := planeCuspVector_smooth induced (atFinite finitePoint)
  have smoothMap : ContDiffOn ℝ ⊤ (fun frame : Rectangular ℝ => fun _ : Fin 1 => inverseMatrix frame)
      {frame : Rectangular ℝ | FullRank frame} :=
    contDiffOn_pi.mpr (fun _ => inverseMatrix_contDiffOn)
  have mapped : Set.MapsTo (fun frame : Rectangular ℝ => fun _ : Fin 1 => inverseMatrix frame)
      {frame : Rectangular ℝ | FullRank frame} {matrices : Fin 1 → PlaneMatrix | ∀ i, (matrices i).det ≠ 0} :=
    fun frame fullRank _ => inverseMatrix_det_ne_zero frame fullRank
  have result := smoothVector.comp smoothMap mapped
  exact result

def model {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : FiniteGL) (frame : Rectangular ℝ) : data.cusp.H :=
  coefficient data parameter finitePoint frame • cuspModel induced finitePoint frame

theorem profile_eq_model {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : FiniteGL) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    (profile induced (adelicFrame finitePoint frame)).val = model induced finitePoint frame := by
  rw [RealFrameChart.profile_eq induced finitePoint frame fullRank]
  change _ = coefficient data parameter finitePoint frame • cuspModel induced finitePoint frame
  rw [coefficient_eq data parameter finitePoint frame fullRank, cuspModel, ← point_eq frame fullRank]
  rfl

theorem profile_contDiffOn {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : FiniteGL) :
    ContDiffOn ℝ ⊤ (fun frame : Rectangular ℝ => (profile induced (adelicFrame finitePoint frame)).val)
      {frame : Rectangular ℝ | FullRank frame} := by
  apply ((coefficient_contDiffOn data parameter finitePoint).smul (cuspModel_contDiffOn induced finitePoint)).congr
  intro frame fullRank
  exact profile_eq_model induced finitePoint frame fullRank

theorem profile_contDiffAt {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : FiniteGL) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    ContDiffAt ℝ ⊤ (fun frame : Rectangular ℝ => (profile induced (adelicFrame finitePoint frame)).val) frame :=
  (profile_contDiffOn induced finitePoint).contDiffAt (fullRank_isOpen.mem_nhds fullRank)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealProfileRegularity
