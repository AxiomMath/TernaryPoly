module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.BadOrbits

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem eq_of_good_vanishing_standardBadLine {degree : ℕ}
    {first second : StratumH2 degree trivialCharacter .line}
    (firstGood : VanishesOnGood degree trivialCharacter .line first)
    (secondGood : VanishesOnGood degree trivialCharacter .line second)
    (standardEqual :
      fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
          standardBadLine first =
        fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
          standardBadLine second) :
    first = second := by
  apply fixedPointH2_jointly_injective rationalLevel
    (rationalCoefficientComponent degree trivialCharacter)
  intro flag
  by_cases good : GoodFlag .line flag
  · exact (vanishesOnGood_fixedPointH2 firstGood flag good).trans
      (vanishesOnGood_fixedPointH2 secondGood flag good).symm
  · obtain ⟨element, transported⟩ := badLine_is_standardBadLine_orbit flag good
    have firstTransport := stabilizerTransportH2_fixedPointH2 rationalLevel
      (rationalCoefficientComponent degree trivialCharacter) element standardBadLine flag
      transported first
    have secondTransport := stabilizerTransportH2_fixedPointH2 rationalLevel
      (rationalCoefficientComponent degree trivialCharacter) element standardBadLine flag
      transported second
    rw [← firstTransport, ← secondTransport, standardEqual]

theorem mem_automorphicLineSpan_iff_matching_standardBadLine (degree : ℕ)
    (coordinate : StratumH2 degree trivialCharacter .line)
    (good : VanishesOnGood degree trivialCharacter .line coordinate) :
    coordinate ∈ automorphicLineSpan degree ↔
      ∃ coefficients : realizedLineClasses degree →₀ ℂ,
        VanishesOnGood degree trivialCharacter .line
            (coefficients.sum (fun image scalar => scalar • image.val)) ∧
          fixedPointH2 rationalLevel
              (rationalCoefficientComponent degree trivialCharacter) standardBadLine
              coordinate =
            fixedPointH2 rationalLevel
              (rationalCoefficientComponent degree trivialCharacter) standardBadLine
              (coefficients.sum (fun image scalar => scalar • image.val)) := by
  constructor
  · intro membership
    obtain ⟨coefficients, sameClass⟩ :=
      (mem_automorphicLineSpan_iff_finite_sources degree coordinate).mp membership
    refine ⟨coefficients, ?_, ?_⟩
    · rw [sameClass]
      exact good
    · exact congrArg (fixedPointH2 rationalLevel
        (rationalCoefficientComponent degree trivialCharacter) standardBadLine)
        sameClass.symm
  · rintro ⟨coefficients, sourceGood, sameRestriction⟩
    apply (mem_automorphicLineSpan_iff_finite_sources degree coordinate).mpr
    exact ⟨coefficients,
      (eq_of_good_vanishing_standardBadLine good sourceGood sameRestriction).symm⟩

theorem innerBadLine_standardRestriction_injective (degree : ℕ) :
    Function.Injective (fun coordinate : innerBadLineClasses degree =>
      fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
        standardBadLine coordinate.val) := by
  intro first second sameRestriction
  apply Subtype.ext
  exact eq_of_good_vanishing_standardBadLine
    ((mem_innerBadLineClasses_iff degree first.val).mp first.property).1
    ((mem_innerBadLineClasses_iff degree second.val).mp second.property).1
    sameRestriction

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
