module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.ThreeCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def standardAwayThreeIntegrand (flat : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (base : AdelicGL) (away : AdelesAwayThree × AdelesAwayThree) : ℂ :=
  flat parameter (standardAwayThreeArgument away base)

local instance standardThreeFactorHaar : normalizedLocalThreeMeasure.IsAddHaarMeasure :=
  normalizedLocalThreeMeasure_haar

theorem standardIntegrand_three_integral {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (flat : ℂ → AdelicGL → ℂ) (flat_section : IsFlatSection data flat)
    (endpoint_support : LocalThreePlaneSupport (flat cohomologicalPoint)) (parameter : ℂ)
    (base : AdelicGL) (base_three : adelicThreeGroup base = 1)
    (away : AdelesAwayThree × AdelesAwayThree) :
    (∫ localParameter, standardIntegrand flat parameter (atThree localGoodLine * base)
      (radicalThreeJoin (localParameter, away))
      ∂(normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)) =
      (1 / 9 : ℂ) * standardAwayThreeIntegrand flat parameter base away := by
  simp only [standardIntegrand, standardThreeCoordinates]
  exact (flatSectionLocalThree_integral local_entry data flat flat_section endpoint_support parameter
    (standardAwayThreeArgument away base) (standardAwayThreeArgument_three away base base_three)
    normalizedLocalThreeMeasure normalizedLocalThreeMeasure_haar normalizedLocalThreeMeasure_normalized).2

/-- Fubini extracts the literal one-ninth entry from the genuine convergent adelic standard integral. -/
theorem standardIntegral_three_factor {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (flat : ℂ → AdelicGL → ℂ) (flat_section : IsFlatSection data flat)
    (endpoint_support : LocalThreePlaneSupport (flat cohomologicalPoint)) (parameter : ℂ)
    (base : AdelicGL) (base_three : adelicThreeGroup base = 1)
    (integrable : Integrable (standardIntegrand flat parameter (atThree localGoodLine * base)) radicalMeasure) :
    Integrable (standardAwayThreeIntegrand flat parameter base) radicalAwayThreeMeasure ∧
    (∫ radical, standardIntegrand flat parameter (atThree localGoodLine * base) radical ∂radicalMeasure) =
      (1 / 9 : ℂ) * ∫ away, standardAwayThreeIntegrand flat parameter base away ∂radicalAwayThreeMeasure := by
  have inner : (fun away => ∫ localParameter,
      standardIntegrand flat parameter (atThree localGoodLine * base)
        (radicalThreeJoin (localParameter, away))
        ∂(normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)) =
      (fun away => (1 / 9 : ℂ) * standardAwayThreeIntegrand flat parameter base away) := by
    funext away
    exact standardIntegrand_three_integral local_entry data flat flat_section endpoint_support parameter
      base base_three away
  constructor
  · have lifted := radicalThreeJoin_measurePreserving.integrable_comp_of_integrable integrable
    have integrated := lifted.integral_prod_right
    change Integrable (fun away => ∫ localParameter,
      standardIntegrand flat parameter (atThree localGoodLine * base)
        (radicalThreeJoin (localParameter, away))
        ∂(normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)) radicalAwayThreeMeasure at integrated
    rw [inner] at integrated
    exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (by norm_num : (1 / 9 : ℂ) ≠ 0)) _).mp integrated
  · rw [radicalIntegral_three_fubini _ integrable, inner, integral_const_mul]

/-- The supplied standard continuation agrees in a half-plane with the complementary integral. -/
theorem standardContinuation_three_factor {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (flat standard : ℂ → AdelicGL → ℂ)
    (flat_section : IsFlatSection data flat)
    (endpoint_support : LocalThreePlaneSupport (flat cohomologicalPoint))
    (continuation : IsStandardContinuation flat standard) :
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      ∀ base : AdelicGL, adelicThreeGroup base = 1 →
      Integrable (standardAwayThreeIntegrand flat parameter base) radicalAwayThreeMeasure ∧
      standard parameter (atThree localGoodLine * base) =
        (1 / 9 : ℂ) * ∫ away, standardAwayThreeIntegrand flat parameter base away ∂radicalAwayThreeMeasure := by
  obtain ⟨threshold, converges⟩ := continuation.2
  refine ⟨threshold, ?_⟩
  intro parameter right base base_three
  obtain ⟨integrable, value⟩ := converges parameter right (atThree localGoodLine * base)
  rw [value]
  exact standardIntegral_three_factor local_entry data flat flat_section endpoint_support
    parameter base base_three integrable

/-- An independently identified complementary continuation gives the same factor at a regular point. -/
theorem standardContinuation_three_eq_at {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (flat standard : ℂ → AdelicGL → ℂ)
    (flat_section : IsFlatSection data flat)
    (endpoint_support : LocalThreePlaneSupport (flat cohomologicalPoint))
    (continuation : IsStandardContinuation flat standard)
    (base : AdelicGL) (base_three : adelicThreeGroup base = 1)
    (complement : ℂ → ℂ) (complement_meromorphic : ∀ parameter, MeromorphicAt complement parameter)
    (complement_integral : ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      complement parameter = ∫ away, standardAwayThreeIntegrand flat parameter base away ∂radicalAwayThreeMeasure)
    (endpoint : ℂ)
    (standard_analytic : AnalyticAt ℂ (fun parameter => standard parameter (atThree localGoodLine * base)) endpoint)
    (complement_analytic : AnalyticAt ℂ complement endpoint) :
    standard endpoint (atThree localGoodLine * base) = (1 / 9 : ℂ) * complement endpoint := by
  obtain ⟨standard_threshold, standard_formula⟩ :=
    standardContinuation_three_factor local_entry data flat standard flat_section endpoint_support continuation
  obtain ⟨complement_threshold, complement_formula⟩ := complement_integral
  apply meromorphic_eq_at_of_halfPlane (second := fun parameter => (1 / 9 : ℂ) * complement parameter)
    (continuation.1 (atThree localGoodLine * base))
    (fun parameter => analyticAt_const.meromorphicAt.mul (complement_meromorphic parameter))
    (max standard_threshold complement_threshold) _ endpoint standard_analytic
    (analyticAt_const.mul complement_analytic)
  intro parameter beyond
  rw [(standard_formula parameter (lt_of_le_of_lt (le_max_left _ _) beyond) base base_three).2,
    complement_formula parameter (lt_of_le_of_lt (le_max_right _ _) beyond)]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
