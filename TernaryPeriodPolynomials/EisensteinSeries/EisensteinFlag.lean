module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.FlagReduction
public import TernaryPeriodPolynomials.EisensteinSeries.Class.FlagCusp

@[expose] public section


/-!
# Appendix C: the flag constant term `r_B 𝓔_P(ξ) = 0` of the form series, reduced to the plane constant term

Formalized by Claude Sonnet 5.5.

A flag lies over a plane, so the flag restriction of the series class is the restriction of `r_P 𝓔_P(ω_f)` to the flag
stabilizer.  `seed_flag_vanish`: the seed (identity coset, row `I`) is mixed cuspidal and vanishes on every flag stabilizer.
`flag_restriction_eq_rest` (unconditional): the flag restriction of the series is that of the non-identity part `restFaceForm`.
`flag_vanishing_of_constantTerm`: `r_B 𝓔_P(ω_f) = 0` at every flag over the standard plane, given the plane constant term
`ConstantTermVanishing` (the obligation (b)).  No averaging over the Heisenberg radical is used.  Not proved: `ConstantTermVanishing`
itself, and the flags over the other plane cusps (the decomposition of `r_{h⁻¹Ph} 𝓔` into seeds and non-identity part, the O2).
-/

namespace TernaryPeriodPolynomials.Argument.Statements.EisensteinFlag

alias seed_flag_vanish := TernaryPeriodPolynomials.Argument.EisensteinClass.seed_flag_vanish
alias flag_restriction_eq_rest := TernaryPeriodPolynomials.Argument.EisensteinClass.flag_restriction_eq_rest
alias flag_vanishing_of_constantTerm :=
  TernaryPeriodPolynomials.Argument.EisensteinClass.flag_vanishing_of_constantTerm

/-! ### All plane cusps `h⁻¹ P h` (`FlagCusp`)

The real face classes of the series at the cusp `h⁻¹Ph` are complexified by `complexifyAt` (identity on cocycles), landing in the
complex representation `faceRep N h n` of the mixed cuspidal / locally inner groups; the flag restriction at every complete flag over
the plane `h⁻¹Ph` vanishes as soon as the complexified restriction to `Γ_{h⁻¹Ph}` is mixed cuspidal. -/

alias flag_mem_locallyInner_iff := TernaryPeriodPolynomials.Argument.EisensteinClass.flag_mem_locallyInner_iff
alias flag_vanishing_at_cusp := TernaryPeriodPolynomials.Argument.EisensteinClass.flag_vanishing_at_cusp
alias flag_restriction_eq_rest_at := TernaryPeriodPolynomials.Argument.EisensteinClass.flag_restriction_eq_rest_at
alias rB_eq_flag_of_cuspFace := TernaryPeriodPolynomials.Argument.EisensteinClass.rB_eq_flag_of_cuspFace

end TernaryPeriodPolynomials.Argument.Statements.EisensteinFlag
