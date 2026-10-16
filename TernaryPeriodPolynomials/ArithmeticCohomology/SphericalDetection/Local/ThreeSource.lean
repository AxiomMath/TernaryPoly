module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Local.ThreeLevelEmbedding
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Local.Detection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem generalLinearGroup_map_entry_congr {source target : Type*} [CommRing source] [CommRing target]
    (hom : source →+* target) (first second : GeneralLinearGroup (Fin 3) source)
    (equal : GeneralLinearGroup.map hom first = GeneralLinearGroup.map hom second) (row column : Fin 3) :
    hom (first.val row column) = hom (second.val row column) :=
  congrArg (fun matrix => matrix.val row column) equal

theorem finiteGL_eq_of_three_and_away (first second : FiniteGL)
    (three : GeneralLinearGroup.map finiteThree first = GeneralLinearGroup.map finiteThree second)
    (away : ∀ place, place ≠ placeThree → GeneralLinearGroup.map (finiteEvaluation place) first =
      GeneralLinearGroup.map (finiteEvaluation place) second) : first = second := by
  apply Units.ext
  funext row column
  apply finiteAdeles_eq_of_three_and_away
  · exact generalLinearGroup_map_entry_congr finiteThree first second three row column
  · intro place distinct
    exact generalLinearGroup_map_entry_congr (finiteEvaluation place) first second
      (away place distinct) row column

theorem realGroup_atThree (matrix : LocalThreeGL) : realGroup (atThree matrix) = 1 :=
  realGroup_atFinite (finiteAtThree matrix)

theorem finiteGroup_atThree (matrix : LocalThreeGL) : finiteGroup (atThree matrix) = finiteAtThree matrix :=
  finiteGroup_atFinite (finiteAtThree matrix)

theorem atThree_commute (matrix : LocalThreeGL) (base : AdelicGL)
    (base_three : adelicThreeGroup base = 1) : Commute (atThree matrix) base := by
  apply adelicGL_ext
  · rw [map_mul, map_mul, realGroup_atThree, one_mul, mul_one]
  · apply finiteGL_eq_of_three_and_away
    · change adelicThreeGroup (atThree matrix * base) = adelicThreeGroup (base * atThree matrix)
      rw [map_mul, map_mul, atThree_three, base_three, mul_one, one_mul]
    · intro place away
      rw [map_mul finiteGroup, map_mul finiteGroup, finiteGroup_atThree, map_mul, map_mul,
        finiteAtThree_away matrix place away, one_mul, mul_one]

/-- A literal local section obtained by varying only the component at three of the source. -/
def sourceLocalThreeSection {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (supported : BadPlaneSource source) (vertices : Fin 3 → RealGL3)
    (base : AdelicGL) (base_three : adelicThreeGroup base = 1) (monomial : Fin 3 →₀ ℕ) :
    localBadPlaneSections :=
  ⟨fun matrix => (source vertices (atThree matrix * base)).val.coeff monomial, by
    constructor
    · intro matrix outside
      dsimp only
      have source_zero := badPlaneSource_local_support data source cocycle supported vertices
        (atThree matrix * base) (by
          simpa only [map_mul, atThree_three, base_three, mul_one] using outside)
      rw [source_zero]
      rfl
    · intro matrix compact level
      dsimp only
      have reorder : atThree (matrix * compact) * base =
          (atThree matrix * base) * atThree compact := by
        rw [map_mul, mul_assoc, (atThree_commute compact base base_three).eq, ← mul_assoc]
      rw [reorder]
      exact (cocycle.1 vertices monomial).2.1
        ⟨finiteAtThree compact, finiteAtThree_level compact level⟩ (atThree matrix * base)⟩

/-- The supplied local entry applies to the actual adelic source coefficients. -/
theorem sourceLocalThree_integral {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (supported : BadPlaneSource source)
    (vertices : Fin 3 → RealGL3) (base : AdelicGL) (base_three : adelicThreeGroup base = 1)
    (monomial : Fin 3 →₀ ℕ) (measure : Measure ℚ_[3]) (haar : measure.IsAddHaarMeasure)
    (normalized : measure {value | ‖value‖ ≤ 1} = 1) :
    Integrable (fun parameter : ℚ_[3] × ℚ_[3] => (source vertices (atThree (weyl⁻¹ * lineUnipotent parameter.1 parameter.2 * localGoodLine) * base)).val.coeff monomial)
      (measure.prod measure) ∧
    (∫ parameter : ℚ_[3] × ℚ_[3], (source vertices (atThree (weyl⁻¹ * lineUnipotent parameter.1 parameter.2 * localGoodLine) * base)).val.coeff monomial
      ∂(measure.prod measure)) = (1 / 9 : ℂ) * (source vertices base).val.coeff monomial := by
  let section_value := sourceLocalThreeSection data source cocycle supported vertices base base_three monomial
  have result := local_entry measure haar normalized section_value.val section_value.property.1 section_value.property.2
  constructor
  · exact result.1
  · simpa only [section_value, localBadPlaneIntegrand, sourceLocalThreeSection, map_one, one_mul] using result.2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
