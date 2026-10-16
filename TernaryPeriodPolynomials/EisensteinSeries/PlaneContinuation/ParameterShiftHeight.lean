module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.InducedRecovery

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight TernaryPeriodPolynomials.PlaneEisensteinContinuation.HeightProperties TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open scoped Classical Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ParameterShiftHeight

def row : PlaneMatrix →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun matrix := WithLp.toLp 2 (fun column => matrix 2 column)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem row_nonzero (point : RealGL3) : row point.val ≠ 0 := by
  intro equality
  apply FlagRows.lastRow_ne_zero point
  funext column
  exact congrArg (fun value : EuclideanSpace ℝ (Fin 3) => value column) equality

def realModel (matrix : PlaneMatrix) : ℝ := Real.log matrix.det / 3 - Real.log ‖row matrix‖

theorem realModel_analyticAt (point : RealGL3) : AnalyticAt ℝ realModel point.val := by
  let boundedRow : PlaneMatrix →L[ℝ] EuclideanSpace ℝ (Fin 3) := ⟨row, row.continuous_of_finiteDimensional⟩
  have rowSmooth : ContDiffAt ℝ ⊤ (fun matrix : PlaneMatrix => ‖row matrix‖) point.val :=
    boundedRow.contDiff.contDiffAt.norm ℝ (row_nonzero point)
  have determinant : ContDiff ℝ ⊤ (fun matrix : PlaneMatrix => matrix.det) := by
    simp only [Matrix.det_fin_three]
    fun_prop
  exact ((determinant.contDiffAt.log (GeneralLinearGroup.det_ne_zero point)).div_const 3 |>.sub
    (rowSmooth.log (norm_ne_zero_iff.mpr (row_nonzero point)))).analyticAt

theorem realModel_eq (point : RealGL3) : realModel point.val = height (atInfinity point) := by
  rw [AdelicHeight.height_atInfinity, Real.log_abs]
  rfl

theorem realHeight_analyticAt (point : RealGL3) :
    AnalyticAt ℝ (fun matrix : PlaneMatrix => (height (atInfinity (invertibleMatrix matrix)) : ℂ)) point.val := by
  have model := (Complex.ofRealCLM.analyticAt _).comp (realModel_analyticAt point)
  apply model.congr
  have nearby : ∀ᶠ matrix : PlaneMatrix in nhds point.val, matrix.det ≠ 0 := by
    change {matrix : PlaneMatrix | matrix.det ≠ 0} ∈ nhds point.val
    exact (isOpen_ne.preimage continuous_id.matrix_det).mem_nhds (GeneralLinearGroup.det_ne_zero point)
  filter_upwards [nearby] with matrix membership
  dsimp only [Function.comp_apply, Complex.ofRealCLM_apply]
  rw [← realModel_eq, OrbitSmooth.invertibleMatrix_val matrix membership]

theorem height_split (point : AdelicGL) (realPoint : RealGL3) :
    height (point * atInfinity realPoint) = height (atInfinity (realGroup point * realPoint)) + height (atFinite (finiteGroup point)) := by
  have product : point * atInfinity realPoint = atInfinity (realGroup point * realPoint) * atFinite (finiteGroup point) := by
    calc
      point * atInfinity realPoint = (atInfinity (realGroup point) * atFinite (finiteGroup point)) * atInfinity realPoint :=
        congrArg (fun g : AdelicGL => g * atInfinity realPoint) (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adelicGL_eq_mul point)
      _ = _ := by rw [mul_assoc, atFinite_atInfinity_commute, ← mul_assoc, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul]
  rw [product, AdelicHeight.height_real_finite]

theorem height_smooth (point : AdelicGL) :
    Smooth (fun matrices : Fin 1 → RealGL3 => (height (point * atInfinity (matrices 0)) : ℂ)) := by
  simp only [height_split, Complex.ofReal_add]
  exact (BoundedSmoothRealization.smooth_of_analytic (fun realPoint => (height (atInfinity realPoint) : ℂ))
    realHeight_analyticAt (realGroup point)).add contDiffOn_const

def coefficient (difference : ℂ) (point : AdelicGL) : ℂ := Complex.exp (difference * (height point : ℂ))

theorem coefficient_smooth (difference : ℂ) (point : AdelicGL) :
    Smooth (fun matrices : Fin 1 → RealGL3 => coefficient difference (point * atInfinity (matrices 0))) :=
  Complex.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul (height_smooth point))

theorem coefficient_nonzero (difference : ℂ) (point : AdelicGL) : coefficient difference point ≠ 0 := Complex.exp_ne_zero _

theorem coefficient_compact (difference : ℂ) (point compact : AdelicGL) (membership : inMaximalCompact compact) :
    coefficient difference (point * compact) = coefficient difference point := by
  rw [coefficient, height_mul_compact point compact membership]
  rfl

theorem height_levi (point : AdelicGL) (binary : BinaryAdelicGL) (scalar : Adelesˣ) :
    height (planeLevi binary scalar * point) =
      (Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) - 2 * Real.log (adeleNorm scalar : ℝ)) / 3 + height point := by
  let parabolic : planeParabolic Adeles := ⟨planeLevi binary scalar, by constructor <;> rfl⟩
  have corner : planeCornerUnit parabolic = scalar := by apply Units.ext; rfl
  have equality := height_plane_mul parabolic point
  rw [planeHeightLog_eq_det_corner, corner] at equality
  change height (planeLevi binary scalar * point) =
    Real.log (adeleNorm (GeneralLinearGroup.det (planeLevi binary scalar)) : ℝ) / 3 - Real.log (adeleNorm scalar : ℝ) + height point at equality
  rw [det_planeLevi, log_adeleNorm_mul] at equality
  rw [equality]
  ring

theorem coefficient_levi (difference : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) (scalar : Adelesˣ) :
    coefficient difference (planeLevi binary scalar * point) =
      normPower (GeneralLinearGroup.det binary) (difference / 3) * normPower scalar (-2 * difference / 3) * coefficient difference point := by
  simp only [coefficient, height_levi, normPower, ← Complex.exp_add, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  ring

theorem coefficient_unipotent (difference : ℂ) (point : AdelicGL) (first second : Adeles) :
    coefficient difference (planeUnipotent first second * point) = coefficient difference point := by
  let parabolic : planeParabolic Adeles := ⟨planeUnipotent first second, by constructor <;> rfl⟩
  have corner : planeCornerUnit parabolic = 1 := by apply Units.ext; rfl
  have equality := height_plane_mul parabolic point
  rw [planeHeightLog_eq_det_corner, corner] at equality
  change height (planeUnipotent first second * point) =
    Real.log (adeleNorm (GeneralLinearGroup.det (planeUnipotent first second)) : ℝ) / 3 - Real.log (adeleNorm 1 : ℝ) + height point at equality
  simp only [det_planeUnipotent, map_one, NNReal.coe_one, Real.log_one, zero_div, sub_self, zero_add] at equality
  rw [coefficient, equality]
  rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ParameterShiftHeight
