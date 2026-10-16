module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.SiegelCover
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelMeasurability

theorem unit_continuous : Continuous (fun argument : UpperHalfPlane => unit argument argument.im_pos) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column
    · exact UpperHalfPlane.continuous_im
    · exact UpperHalfPlane.continuous_re
    · exact continuous_const
    · exact continuous_const
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column
    · exact UpperHalfPlane.continuous_im.inv₀ (fun argument => argument.im_pos.ne')
    · exact UpperHalfPlane.continuous_re.neg.div UpperHalfPlane.continuous_im (fun argument => argument.im_pos.ne')
    · exact continuous_const
    · exact continuous_const

def strip : Set UpperHalfPlane := {argument | 1 ≤ argument.im ∧ |argument.re| ≤ 1}

theorem strip_closed : IsClosed strip :=
  (isClosed_le continuous_const UpperHalfPlane.continuous_im).inter
    (isClosed_le UpperHalfPlane.continuous_re.abs continuous_const)

instance strip_sigmaCompact : SigmaCompactSpace strip := strip_closed.sigmaCompactSpace

instance integral_compact : CompactSpace IntegralBinaryGL := by
  let _ : CompactSpace (Matrix (Fin 2) (Fin 2) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → IntegralAdeles))
  infer_instance

def scale (logarithm : ℝ) : ℝˣ := Units.mk0 (Real.exp logarithm) (Real.exp_ne_zero logarithm)

theorem scale_continuous : Continuous scale := by
  apply Units.continuous_iff.mpr
  exact ⟨Real.continuous_exp, Real.continuous_exp.inv₀ (fun logarithm => Real.exp_ne_zero logarithm)⟩

theorem scalar_continuous : Continuous (GeneralLinearGroup.scalar (Fin 2) (R := ℝ)) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    by_cases equality : row = column
    · simpa only [Function.comp_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, ite_eq_left equality] using
        (Units.continuous_val : Continuous (fun value : ℝˣ => value.val))
    · simpa only [Function.comp_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, ite_eq_right equality] using
        (continuous_const : Continuous (fun _ : ℝˣ => (0 : ℝ)))
  · have equality : (fun value : ℝˣ => (GeneralLinearGroup.scalar (Fin 2) value)⁻¹.val) =
        fun value => (GeneralLinearGroup.scalar (Fin 2) value⁻¹).val := by funext value; rw [map_inv]
    rw [equality]
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    by_cases equality : row = column
    · simpa only [Function.comp_apply, id_eq, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, ite_eq_left equality] using
        ((Units.continuous_iff.mp (continuous_id : Continuous (fun value : ℝˣ => value))).2)
    · simpa only [Function.comp_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, ite_eq_right equality] using
        (continuous_const : Continuous (fun _ : ℝˣ => (0 : ℝ)))

abbrev Parameter := IntegralBinaryGL × ℝ × strip × Circle

theorem atFinite_continuous : Continuous (atFinite (m := 2)) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun value : BinaryFiniteGL => fun row column => ((1 : Matrix (Fin 2) (Fin 2) ℝ) row column, value.val row column))
    exact continuous_pi (fun row => continuous_pi (fun column => continuous_const.prodMk
      ((continuous_apply column).comp ((continuous_apply row).comp (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) FiniteAdeles))))))
  · change Continuous (fun value : BinaryFiniteGL => fun row column => ((1 : Matrix (Fin 2) (Fin 2) ℝ) row column, value⁻¹.val row column))
    exact continuous_pi (fun row => continuous_pi (fun column => continuous_const.prodMk
      ((continuous_apply column).comp ((continuous_apply row).comp
        ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) FiniteAdeles)).comp
          (continuous_inv : Continuous (fun value : BinaryFiniteGL => value⁻¹)))))))

def parameterize (parameter : Parameter) : BinaryAdelicGL :=
  AdelicSiegelCover.chart parameter.1 (scale parameter.2.1) parameter.2.2.1.val
    (RealSiegelSet.rightFactor parameter.2.2.2)

theorem parameterize_continuous : Continuous parameterize := by
  unfold parameterize AdelicSiegelCover.chart
  exact (atFinite_continuous.comp (integralMap_continuous.comp continuous_fst)).mul
    (StageTranslation.atInfinity_continuous.comp
      ((scalar_continuous.comp (scale_continuous.comp (continuous_fst.comp continuous_snd))).mul
        ((unit_continuous.comp (continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))).mul
          (RealSiegelSet.rightFactor_continuous.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))))))

theorem range_eq_region : Set.range parameterize = AdelicSiegelCover.region := by
  ext point
  constructor
  · rintro ⟨parameter, rfl⟩
    exact ⟨parameter.1, scale parameter.2.1, Real.exp_pos _, parameter.2.2.1.val, parameter.2.2.1.property.1,
      parameter.2.2.1.property.2, RealSiegelSet.rightFactor parameter.2.2.2, ⟨parameter.2.2.2, rfl⟩, rfl⟩
  · rintro ⟨integral, scalar, positive, argument, height, horizontal, right, ⟨rotation, rfl⟩, rfl⟩
    refine ⟨(integral, Real.log scalar.val, ⟨argument, height, horizontal⟩, rotation), ?_⟩
    have scaleEquality : scale (Real.log scalar.val) = scalar := by
      apply Units.ext
      exact Real.exp_log positive
    change AdelicSiegelCover.chart integral (scale (Real.log scalar.val)) argument _ = _
    rw [scaleEquality]

theorem region_sigmaCompact : IsSigmaCompact AdelicSiegelCover.region := by
  rw [← range_eq_region]
  exact isSigmaCompact_range parameterize_continuous

theorem region_measurable : MeasurableSet AdelicSiegelCover.region := by
  obtain ⟨compacts, compact, equality⟩ := region_sigmaCompact
  rw [← equality]
  exact MeasurableSet.iUnion (fun index => (compact index).measurableSet)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelMeasurability
