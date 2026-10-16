module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.HeightMajorant
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ConstantTerm

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ScalarSummability

theorem norm_integrals_ne_top (function : Flags .plane → Adeles × Adeles → ℂ)
    (majorant : Flags .plane → ℝ) (nonnegative : ∀ flag, 0 ≤ majorant flag)
    (summable : Summable majorant)
    (bounded : ∀ coordinates ∈ additiveDomain ×ˢ additiveDomain, ∀ flag,
      ‖function flag coordinates‖ ≤ majorant flag) :
    (∑' flag : Flags .plane, ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
      ‖function flag coordinates‖ₑ ∂radicalMeasure) ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (show ENNReal.ofReal (∑' flag, majorant flag) ≠ ⊤ from ENNReal.ofReal_ne_top)
  rw [ENNReal.ofReal_tsum_of_nonneg nonnegative summable]
  apply ENNReal.tsum_le_tsum
  intro flag
  calc
    (∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
        ‖function flag coordinates‖ₑ ∂radicalMeasure) ≤
      ∫⁻ _coordinates in additiveDomain ×ˢ additiveDomain,
        ENNReal.ofReal (majorant flag) ∂radicalMeasure := by
      apply setLIntegral_mono measurable_const
      intro coordinates membership
      rw [← enorm_norm, Real.enorm_eq_ofReal (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (bounded coordinates membership flag)
    _ = ENNReal.ofReal (majorant flag) := by simp

theorem eisenstein_norm_integrals_ne_top {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compact, inMaximalCompact compact → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact) binary‖ ≤ bound)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    (∑' flag : Flags .plane, ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
      ‖eisensteinSummand extension parameter
        (lineUnipotent coordinates.1 coordinates.2 * argument) flag‖ₑ ∂radicalMeasure) ≠ ⊤ := by
  obtain ⟨majorant, nonnegative, summable, dominates⟩ :=
    HeightMajorant.scalar_domain_majorant data extension flat bound bounded parameter halfPlane argument
  exact norm_integrals_ne_top _ majorant nonnegative summable dominates

theorem standard_integrable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compact, inMaximalCompact compact → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact) binary‖ ≤ bound)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    Integrable (standardIntegrand extension parameter argument) radicalMeasure :=
  ConstantTerm.standard_integrable_of_norm_sum data extension parameter (flat.1 parameter) argument
    (eisenstein_norm_integrals_ne_top data extension flat bound bounded parameter halfPlane argument)

theorem eisenstein_constantTerm {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compact, inMaximalCompact compact → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact) binary‖ ≤ bound)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) (eisenstein : AdelicGL → ℂ)
    (sums : ∀ value, HasSum (eisensteinSummand extension parameter value) (eisenstein value)) :
    (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      eisenstein (lineUnipotent coordinates.1 coordinates.2 * argument) ∂radicalMeasure) =
      ∫ coordinates, standardIntegrand extension parameter argument coordinates ∂radicalMeasure :=
  ConstantTerm.eisenstein_constantTerm_of_norm_sum data extension parameter (flat.1 parameter)
    argument eisenstein sums
    (eisenstein_norm_integrals_ne_top data extension flat bound bounded parameter halfPlane argument)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ScalarSummability
