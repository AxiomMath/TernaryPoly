module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ClosedCellIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Unfolding
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedContinuity
public import Mathlib.Data.Rat.Encodable

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ConstantTerm

instance rationalGLCountable : Countable RationalGL3 := by
  let : Countable (Matrix (Fin 3) (Fin 3) ℚ) :=
    inferInstanceAs (Countable (Fin 3 → Fin 3 → ℚ))
  exact Units.val_injective.countable

instance rationalFlagsCountable (side : Side) : Countable (Flags side) :=
  QuotientGroup.mk_surjective.countable

theorem standard_integrable_of_eisenstein_norm_sum {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL)
    (summandsIntegrable : ∀ flag : Flags .plane,
      IntegrableOn (fun coordinates : Adeles × Adeles =>
        eisensteinSummand extension parameter
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag)
        (additiveDomain ×ˢ additiveDomain) radicalMeasure)
    (summableNorms : (∑' flag : Flags .plane,
      ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
        ‖eisensteinSummand extension parameter
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag‖ₑ ∂radicalMeasure) ≠ ⊤) :
    Integrable (standardIntegrand extension parameter argument) radicalMeasure := by
  apply Unfolding.radical_integrable_of_norm_sum
  · intro rational
    simpa only [FundamentalDomain.rationalPair,
      BruhatSums.eisensteinSummand_open_shift data extension parameter induced] using
      summandsIntegrable (BruhatCells.openFlag rational)
  · have bound := ENNReal.tsum_comp_le_tsum_of_injective BruhatCells.openFlag_injective
      (fun flag => ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
        ‖eisensteinSummand extension parameter
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag‖ₑ ∂radicalMeasure)
    simp only [BruhatSums.eisensteinSummand_open_shift data extension parameter induced] at bound
    exact ne_top_of_le_ne_top summableNorms bound

theorem standard_integrable_of_measurable_norm_sum {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL)
    (measurable : AEStronglyMeasurable (standardIntegrand extension parameter argument)
      radicalMeasure)
    (summableNorms : (∑' flag : Flags .plane,
      ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
        ‖eisensteinSummand extension parameter
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag‖ₑ ∂radicalMeasure) ≠ ⊤) :
    Integrable (standardIntegrand extension parameter argument) radicalMeasure := by
  refine ⟨measurable, ?_⟩
  change (∫⁻ coordinates, ‖standardIntegrand extension parameter argument coordinates‖ₑ
    ∂radicalMeasure) < ⊤
  rw [FundamentalDomain.radicalDomain_fundamental.lintegral_eq_tsum''
    (fun coordinates => ‖standardIntegrand extension parameter argument coordinates‖ₑ)]
  have bound := ENNReal.tsum_comp_le_tsum_of_injective BruhatCells.openFlag_injective
    (fun flag => ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
      ‖eisensteinSummand extension parameter
        (lineUnipotent coordinates.1 coordinates.2 * argument) flag‖ₑ ∂radicalMeasure)
  simp only [BruhatSums.eisensteinSummand_open_shift data extension parameter induced] at bound
  exact lt_of_le_of_lt bound (lt_top_iff_ne_top.mpr summableNorms)

theorem summands_integrable_of_standard {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL)
    (integrable : Integrable (standardIntegrand extension parameter argument) radicalMeasure)
    (flag : Flags .plane) :
    IntegrableOn (fun coordinates : Adeles × Adeles =>
      eisensteinSummand extension parameter
        (lineUnipotent coordinates.1 coordinates.2 * argument) flag)
      (additiveDomain ×ˢ additiveDomain) radicalMeasure := by
  by_cases isOpen : flag ∈ Set.range BruhatCells.openFlag
  · obtain ⟨rational, rfl⟩ := isOpen
    simp_rw [BruhatSums.eisensteinSummand_open_shift data extension parameter induced]
    exact (integrable.comp_add_left _).integrableOn
  · exact ClosedCellIntegral.closedFlag_integrable data extension parameter induced
      argument ⟨flag, isOpen⟩

theorem eisenstein_constantTerm {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (eisenstein : AdelicGL → ℂ)
    (sums : ∀ value, HasSum (eisensteinSummand extension parameter value) (eisenstein value))
    (summandsIntegrable : ∀ flag : Flags .plane,
      IntegrableOn (fun coordinates : Adeles × Adeles =>
        eisensteinSummand extension parameter
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag)
        (additiveDomain ×ˢ additiveDomain) radicalMeasure)
    (summableNorms : (∑' flag : Flags .plane,
      ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
        ‖eisensteinSummand extension parameter
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag‖ₑ ∂radicalMeasure) ≠ ⊤) :
    (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      eisenstein (lineUnipotent coordinates.1 coordinates.2 * argument) ∂radicalMeasure) =
      ∫ coordinates, standardIntegrand extension parameter argument coordinates ∂radicalMeasure := by
  have standardIntegrable := standard_integrable_of_eisenstein_norm_sum data extension parameter
    induced argument summandsIntegrable summableNorms
  have summation : ∀ coordinates : Adeles × Adeles,
      eisenstein (lineUnipotent coordinates.1 coordinates.2 * argument) =
        ∑' flag, eisensteinSummand extension parameter
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag := by
    intro coordinates
    exact (sums _).tsum_eq.symm
  simp_rw [summation]
  rw [integral_tsum (fun flag => (summandsIntegrable flag).aestronglyMeasurable) summableNorms]
  have support : Function.support (fun flag : Flags .plane =>
      ∫ coordinates in additiveDomain ×ˢ additiveDomain,
        eisensteinSummand extension parameter
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag ∂radicalMeasure) ⊆
        Set.range BruhatCells.openFlag := by
    intro flag membership
    by_contra closed
    exact membership (ClosedCellIntegral.closedFlag_integral data extension parameter induced
      argument ⟨flag, closed⟩)
  rw [← BruhatCells.openFlag_injective.tsum_eq support]
  simp_rw [BruhatSums.eisensteinSummand_open_shift data extension parameter induced]
  exact (FundamentalDomain.radicalDomain_fundamental.integral_eq_tsum''
    (standardIntegrand extension parameter argument) standardIntegrable).symm

theorem eisenstein_constantTerm_of_norm_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (eisenstein : AdelicGL → ℂ)
    (sums : ∀ value, HasSum (eisensteinSummand extension parameter value) (eisenstein value))
    (measurable : AEStronglyMeasurable (standardIntegrand extension parameter argument)
      radicalMeasure)
    (summableNorms : (∑' flag : Flags .plane,
      ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
        ‖eisensteinSummand extension parameter
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag‖ₑ ∂radicalMeasure) ≠ ⊤) :
    (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      eisenstein (lineUnipotent coordinates.1 coordinates.2 * argument) ∂radicalMeasure) =
      ∫ coordinates, standardIntegrand extension parameter argument coordinates ∂radicalMeasure := by
  have integrable := standard_integrable_of_measurable_norm_sum data extension parameter
    induced argument measurable summableNorms
  exact eisenstein_constantTerm data extension parameter induced argument eisenstein sums
    (summands_integrable_of_standard data extension parameter induced argument integrable)
    summableNorms

theorem standard_integrable_of_norm_sum {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL)
    (summableNorms : (∑' flag : Flags .plane,
      ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
        ‖eisensteinSummand extension parameter
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag‖ₑ ∂radicalMeasure) ≠ ⊤) :
    Integrable (standardIntegrand extension parameter argument) radicalMeasure :=
  standard_integrable_of_measurable_norm_sum data extension parameter induced argument
    (InducedContinuity.standardIntegrand_aestronglyMeasurable data extension parameter induced argument)
    summableNorms

theorem eisenstein_constantTerm_of_norm_sum {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (eisenstein : AdelicGL → ℂ)
    (sums : ∀ value, HasSum (eisensteinSummand extension parameter value) (eisenstein value))
    (summableNorms : (∑' flag : Flags .plane,
      ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
        ‖eisensteinSummand extension parameter
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag‖ₑ ∂radicalMeasure) ≠ ⊤) :
    (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      eisenstein (lineUnipotent coordinates.1 coordinates.2 * argument) ∂radicalMeasure) =
      ∫ coordinates, standardIntegrand extension parameter argument coordinates ∂radicalMeasure :=
  eisenstein_constantTerm data extension parameter induced argument eisenstein sums
    (InducedContinuity.eisensteinSummand_integrableOn data extension parameter induced argument)
    summableNorms

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ConstantTerm
