module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.ThreeFactor

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineAwayThree : AdelicGL :=
  atThree localGoodLine⁻¹ * rationalGroup rationalGoodLine

theorem goodLineAwayThree_three : adelicThreeGroup goodLineAwayThree = 1 := by
  rw [goodLineAwayThree, map_mul, atThree_three, adelicThreeGroup_rational,
    rationalGoodLine_at_three, inv_mul_cancel]

theorem goodLineAwayThree_reassemble :
    atThree localGoodLine * goodLineAwayThree = rationalGroup rationalGoodLine := by
  rw [goodLineAwayThree, map_inv, mul_inv_cancel_left]

def localBinarySwapIntegral : LocalThreeIntegralGL :=
  ⟨!![0,1,0;1,0,0;0,0,1], !![0,1,0;1,0,0;0,0,1], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem localStandardAtZero_level : InLocalThreeLevel (weyl⁻¹ * localGoodLine) := by
  refine ⟨localBinarySwapIntegral, ?_, ?_⟩
  · funext column
    fin_cases column <;>
      simp [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
        GeneralLinearGroup.map_apply, localBinarySwapIntegral]
  · apply Units.ext
    funext row column
    fin_cases row <;> fin_cases column <;>
      simp [GeneralLinearGroup.map_apply, localBinarySwapIntegral,
        weyl, localGoodLine, Matrix.mul_apply, Fin.sum_univ_three]

def standardGoodLineAwayIntegrand (flat : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (away : AdelesAwayThree × AdelesAwayThree) : ℂ :=
  flat parameter (weyl⁻¹ *
    lineUnipotent (adeleAwayThreeScalar away.1) (adeleAwayThreeScalar away.2) *
      rationalGroup rationalGoodLine)

theorem standardAwayThreeIntegrand_goodLine {degree : ℕ}
    (data : InducingData degree) (flat : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (flat parameter))
    (away : AdelesAwayThree × AdelesAwayThree) :
    standardAwayThreeIntegrand flat parameter goodLineAwayThree away =
      standardGoodLineAwayIntegrand flat parameter away := by
  have zero_coordinates : radicalThreeJoin ((0, 0), away) =
      (adeleAwayThreeScalar away.1, adeleAwayThreeScalar away.2) := by
    rw [radicalThreeJoin_apply, finiteAtThreeScalar_zero, zero_add, zero_add]
    rfl
  have coordinate := standardThreeCoordinates (0, 0) away goodLineAwayThree
  rw [zero_coordinates, goodLineAwayThree_reassemble] at coordinate
  dsimp only at coordinate
  rw [show lineUnipotent (0 : ℚ_[3]) 0 = 1 from (lineUnipotentHom ℚ_[3]).map_one, mul_one] at coordinate
  have commute := atThree_commute (weyl⁻¹ * localGoodLine)
    (standardAwayThreeArgument away goodLineAwayThree)
    (standardAwayThreeArgument_three away goodLineAwayThree goodLineAwayThree_three)
  rw [commute.eq] at coordinate
  change flat parameter (standardAwayThreeArgument away goodLineAwayThree) =
    flat parameter (weyl⁻¹ * lineUnipotent (adeleAwayThreeScalar away.1)
      (adeleAwayThreeScalar away.2) * rationalGroup rationalGoodLine)
  rw [coordinate]
  exact (induced.2.1
    ⟨finiteAtThree (weyl⁻¹ * localGoodLine), finiteAtThree_level _ localStandardAtZero_level⟩
    (standardAwayThreeArgument away goodLineAwayThree)).symm

/-- The rational good-line restriction has a literal complementary standard integral. -/
theorem standardContinuation_goodLine_factor {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (flat standard : ℂ → AdelicGL → ℂ)
    (flat_section : IsFlatSection data flat)
    (endpoint_support : LocalThreePlaneSupport (flat cohomologicalPoint))
    (continuation : IsStandardContinuation flat standard) :
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      Integrable (standardGoodLineAwayIntegrand flat parameter) radicalAwayThreeMeasure ∧
      standard parameter (rationalGroup rationalGoodLine) =
        (1 / 9 : ℂ) * ∫ away, standardGoodLineAwayIntegrand flat parameter away ∂radicalAwayThreeMeasure := by
  obtain ⟨threshold, formula⟩ :=
    standardContinuation_three_factor local_entry data flat standard flat_section endpoint_support continuation
  refine ⟨threshold, ?_⟩
  intro parameter beyond
  have result := formula parameter beyond goodLineAwayThree goodLineAwayThree_three
  rw [goodLineAwayThree_reassemble] at result
  have integrands : standardAwayThreeIntegrand flat parameter goodLineAwayThree =
      standardGoodLineAwayIntegrand flat parameter := by
    funext away
    exact standardAwayThreeIntegrand_goodLine data flat parameter (flat_section.1 parameter) away
  rwa [integrands] at result

end TernaryPeriodPolynomials.SphericalDetection.Helpers
