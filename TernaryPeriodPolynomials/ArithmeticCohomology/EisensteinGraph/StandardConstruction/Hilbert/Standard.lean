module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.Height

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertStandard

def integrand {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (coordinates : Adeles × Adeles) : data.cusp.H :=
  (CuspLift.vector data .plane parameter function induced
    (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument)).val

theorem integrand_continuous {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) : Continuous (integrand data parameter function induced argument) :=
  (CuspLift.continuous data .plane parameter function induced).comp
    ((continuous_const.mul InducedContinuity.lineUnipotent_continuous).mul continuous_const)

theorem normSummand_integrals_ne_top {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    (∑' flag : Flags .plane, ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
      ENNReal.ofReal (HilbertHeight.normSummand data parameter function induced
        (lineUnipotent coordinates.1 coordinates.2 * argument) flag) ∂radicalMeasure) ≠ ⊤ := by
  obtain ⟨majorant, nonnegative, summable, dominates⟩ :=
    HilbertHeight.domain_majorant data parameter function induced halfPlane argument
  apply ne_top_of_le_ne_top
    (show ENNReal.ofReal (∑' flag, majorant flag) ≠ ⊤ from ENNReal.ofReal_ne_top)
  rw [ENNReal.ofReal_tsum_of_nonneg nonnegative summable]
  apply ENNReal.tsum_le_tsum
  intro flag
  calc
    _ ≤ ∫⁻ _coordinates in additiveDomain ×ˢ additiveDomain,
        ENNReal.ofReal (majorant flag) ∂radicalMeasure := by
      apply setLIntegral_mono measurable_const
      intro coordinates membership
      exact ENNReal.ofReal_le_ofReal (dominates coordinates membership flag)
    _ = ENNReal.ofReal (majorant flag) := by simp

theorem integrand_integrable {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    Integrable (integrand data parameter function induced argument) radicalMeasure := by
  refine ⟨(integrand_continuous data parameter function induced argument).aestronglyMeasurable, ?_⟩
  change (∫⁻ coordinates, ‖integrand data parameter function induced argument coordinates‖ₑ
    ∂radicalMeasure) < ⊤
  rw [FundamentalDomain.radicalDomain_fundamental.lintegral_eq_tsum''
    (fun coordinates => ‖integrand data parameter function induced argument coordinates‖ₑ)]
  have bound := ENNReal.tsum_comp_le_tsum_of_injective BruhatCells.openFlag_injective
    (fun flag => ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
      ENNReal.ofReal (HilbertHeight.normSummand data parameter function induced
        (lineUnipotent coordinates.1 coordinates.2 * argument) flag) ∂radicalMeasure)
  simp only [HilbertHeight.normSummand_open_shift, ofReal_norm] at bound
  exact lt_of_le_of_lt bound (lt_top_iff_ne_top.mpr
    (normSummand_integrals_ne_top data parameter function induced halfPlane argument))

def value {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) : data.cusp.H :=
  ∫ coordinates, integrand data parameter function induced argument coordinates ∂radicalMeasure

theorem value_finite_invariant {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (level : finiteLevel) (argument : AdelicGL) :
    value data parameter function induced (argument * atFinite level.val) =
      value data parameter function induced argument := by
  unfold value integrand
  apply integral_congr_ae
  filter_upwards [] with coordinates
  rw [← mul_assoc, CuspLift.finite_invariant]

theorem value_radical_invariant {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (first second : Adeles) (argument : AdelicGL) :
    value data parameter function induced (lineUnipotent first second * argument) =
      value data parameter function induced argument := by
  have equality : integrand data parameter function induced (lineUnipotent first second * argument) =
      fun coordinates => integrand data parameter function induced argument (coordinates + (first, second)) := by
    funext coordinates
    unfold integrand
    rw [mul_assoc (weyl⁻¹ : AdelicGL), ← mul_assoc (lineUnipotent _ _), ← lineUnipotent_add]
    simp only [Prod.fst_add, Prod.snd_add, mul_assoc]
  unfold value
  rw [equality]
  exact integral_add_right_eq_self _ (first, second)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertStandard
