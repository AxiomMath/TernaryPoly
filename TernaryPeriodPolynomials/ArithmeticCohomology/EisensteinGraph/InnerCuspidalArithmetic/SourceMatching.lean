module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.AutomorphicSpan

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem mem_automorphicLineSpan_iff_matching_stabilizers (degree : ℕ)
    (coordinate : StratumH2 degree trivialCharacter .line) :
    coordinate ∈ automorphicLineSpan degree ↔
      ∃ coefficients : realizedLineClasses degree →₀ ℂ,
        ∀ flag : Flags .line,
          fixedPointH2 rationalLevel
              (rationalCoefficientComponent degree trivialCharacter) flag coordinate =
            fixedPointH2 rationalLevel
              (rationalCoefficientComponent degree trivialCharacter) flag
              (coefficients.sum (fun image scalar => scalar • image.val)) := by
  rw [mem_automorphicLineSpan_iff_finite_sources]
  constructor
  · rintro ⟨coefficients, sameClass⟩
    refine ⟨coefficients, ?_⟩
    intro flag
    exact congrArg (fixedPointH2 rationalLevel
      (rationalCoefficientComponent degree trivialCharacter) flag) sameClass.symm
  · rintro ⟨coefficients, sameRestrictions⟩
    refine ⟨coefficients, ?_⟩
    apply fixedPointH2_jointly_injective rationalLevel
      (rationalCoefficientComponent degree trivialCharacter)
    intro flag
    exact (sameRestrictions flag).symm

theorem mem_automorphicLineSpan_of_matching_bad_stabilizers {degree : ℕ}
    {coordinate : StratumH2 degree trivialCharacter .line}
    (good : VanishesOnGood degree trivialCharacter .line coordinate)
    (coefficients : realizedLineClasses degree →₀ ℂ)
    (sourceGood : VanishesOnGood degree trivialCharacter .line
      (coefficients.sum (fun image scalar => scalar • image.val)))
    (badRestrictions : ∀ flag : Flags .line, ¬ GoodFlag .line flag →
      fixedPointH2 rationalLevel
          (rationalCoefficientComponent degree trivialCharacter) flag coordinate =
        fixedPointH2 rationalLevel
          (rationalCoefficientComponent degree trivialCharacter) flag
          (coefficients.sum (fun image scalar => scalar • image.val))) :
    coordinate ∈ automorphicLineSpan degree := by
  apply (mem_automorphicLineSpan_iff_matching_stabilizers degree coordinate).mpr
  refine ⟨coefficients, ?_⟩
  intro flag
  by_cases goodFlag : GoodFlag .line flag
  · exact (vanishesOnGood_fixedPointH2 good flag goodFlag).trans
      (vanishesOnGood_fixedPointH2 sourceGood flag goodFlag).symm
  · exact badRestrictions flag goodFlag

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
