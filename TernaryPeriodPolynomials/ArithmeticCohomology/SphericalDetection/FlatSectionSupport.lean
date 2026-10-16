module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PlaneParabolicDecomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Local.ThreeSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.Comparison

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def LocalThreePlaneSupport (function : AdelicGL → ℂ) : Prop :=
  ∀ argument, (¬ ∃ parabolic : planeParabolic ℚ_[3], ∃ compact : LocalThreeGL,
    InLocalThreeLevel compact ∧ adelicThreeGroup argument = parabolic.val * compact) → function argument = 0

theorem generalLinearGroup_map_plane {source target : Type*} [CommRing source] [CommRing target]
    (hom : source →+* target) (matrix : planeParabolic source) :
    GeneralLinearGroup.map hom matrix.val ∈ planeParabolic target := by
  constructor
  · rw [GeneralLinearGroup.map_apply, matrix.property.1, map_zero]
  · rw [GeneralLinearGroup.map_apply, matrix.property.2, map_zero]

theorem adelicThreeGroup_plane (matrix : planeParabolic Adeles) :
    adelicThreeGroup matrix.val ∈ planeParabolic ℚ_[3] :=
  generalLinearGroup_map_plane finiteThree
    ⟨finiteGroup matrix.val, generalLinearGroup_map_plane (RingHom.snd ℝ FiniteAdeles) matrix⟩

theorem outside_localThreePlane_of_left_parabolic (parabolic : planeParabolic Adeles) (argument : AdelicGL)
    (outside : ¬ ∃ local_parabolic : planeParabolic ℚ_[3], ∃ compact : LocalThreeGL,
      InLocalThreeLevel compact ∧ adelicThreeGroup (parabolic.val * argument) = local_parabolic.val * compact) :
    ¬ ∃ local_parabolic : planeParabolic ℚ_[3], ∃ compact : LocalThreeGL,
      InLocalThreeLevel compact ∧ adelicThreeGroup argument = local_parabolic.val * compact := by
  rintro ⟨local_parabolic, compact, level, equality⟩
  apply outside
  refine ⟨⟨adelicThreeGroup parabolic.val, adelicThreeGroup_plane parabolic⟩ * local_parabolic,
    compact, level, ?_⟩
  rw [map_mul, equality, ← mul_assoc]
  rfl

/-- Literal support at three persists in the entire flat family. -/
theorem flatSection_localThree_support {degree : ℕ} (data : InducingData degree)
    (flat : ℂ → AdelicGL → ℂ) (flat_section : IsFlatSection data flat)
    (endpoint_support : LocalThreePlaneSupport (flat cohomologicalPoint)) (parameter : ℂ) :
    LocalThreePlaneSupport (flat parameter) := by
  intro argument outside
  obtain ⟨first, second, scalar, block, compact, compact_member, factorization⟩ :=
    adelicGL_exists_induction_coordinates argument
  let left_parabolic : planeParabolic Adeles :=
    ⟨planeUnipotent first second * planeLevi 1 scalar,
      (planeParabolic Adeles).mul_mem ⟨rfl, rfl⟩ (planeLevi_mem 1 scalar)⟩
  have outside_block : ¬ ∃ local_parabolic : planeParabolic ℚ_[3], ∃ local_compact : LocalThreeGL,
      InLocalThreeLevel local_compact ∧
      adelicThreeGroup (planeLevi block 1 * compact) = local_parabolic.val * local_compact := by
    apply outside_localThreePlane_of_left_parabolic left_parabolic
    change ¬ ∃ local_parabolic : planeParabolic ℚ_[3], ∃ local_compact : LocalThreeGL,
      InLocalThreeLevel local_compact ∧
      adelicThreeGroup ((planeUnipotent first second * planeLevi 1 scalar) *
        (planeLevi block 1 * compact)) = local_parabolic.val * local_compact
    rw [mul_assoc, ← factorization]
    exact outside
  have endpoint_zero := endpoint_support _ outside_block
  have flat_identity := flat_section.2.2 parameter block compact compact_member
  rw [endpoint_zero, mul_zero] at flat_identity
  have flat_zero : flat parameter (planeLevi block 1 * compact) = 0 :=
    (mul_eq_zero.mp flat_identity).resolve_left (normPower_ne_zero _ _)
  rw [factorization, (flat_section.1 parameter).2.2.2.1,
    (flat_section.1 parameter).2.2.2.2.1, flat_zero, mul_zero]

theorem sourceCoefficient_localThree_support {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (supported : BadPlaneSource source) (vertices : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ) :
    LocalThreePlaneSupport (fun argument => (source vertices argument).val.coeff monomial) := by
  intro argument outside
  dsimp only
  rw [badPlaneSource_local_support data source cocycle supported vertices argument outside]
  rfl

def inducedLocalThreeSection {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (support : LocalThreePlaneSupport function) (base : AdelicGL) (base_three : adelicThreeGroup base = 1) :
    localBadPlaneSections :=
  ⟨fun matrix => function (atThree matrix * base), by
    constructor
    · intro matrix outside
      apply support
      simpa only [map_mul, atThree_three, base_three, mul_one] using outside
    · intro matrix compact level
      dsimp only
      have reorder : atThree (matrix * compact) * base =
          (atThree matrix * base) * atThree compact := by
        rw [map_mul, mul_assoc, (atThree_commute compact base base_three).eq, ← mul_assoc]
      rw [reorder]
      exact induced.2.1 ⟨finiteAtThree compact, finiteAtThree_level compact level⟩ (atThree matrix * base)⟩

/-- The local factor is exactly one ninth for every parameter of the actual flat section. -/
theorem flatSectionLocalThree_integral {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (flat : ℂ → AdelicGL → ℂ) (flat_section : IsFlatSection data flat)
    (endpoint_support : LocalThreePlaneSupport (flat cohomologicalPoint)) (parameter : ℂ)
    (base : AdelicGL) (base_three : adelicThreeGroup base = 1)
    (measure : Measure ℚ_[3]) (haar : measure.IsAddHaarMeasure)
    (normalized : measure {value | ‖value‖ ≤ 1} = 1) :
    Integrable (fun value : ℚ_[3] × ℚ_[3] =>
      flat parameter (atThree (weyl⁻¹ * lineUnipotent value.1 value.2 * localGoodLine) * base))
      (measure.prod measure) ∧
    (∫ value : ℚ_[3] × ℚ_[3],
      flat parameter (atThree (weyl⁻¹ * lineUnipotent value.1 value.2 * localGoodLine) * base)
      ∂(measure.prod measure)) = (1 / 9 : ℂ) * flat parameter base := by
  let section_value := inducedLocalThreeSection data parameter (flat parameter)
    (flat_section.1 parameter) (flatSection_localThree_support data flat flat_section endpoint_support parameter)
    base base_three
  have result := local_entry measure haar normalized section_value.val section_value.property.1 section_value.property.2
  constructor
  · exact result.1
  · simpa only [section_value, localBadPlaneIntegrand, inducedLocalThreeSection, map_one, one_mul] using result.2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
