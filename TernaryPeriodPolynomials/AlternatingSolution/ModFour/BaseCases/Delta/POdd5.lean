module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.KappaOneReduction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.PGen5
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section


/-!
`delta_p (oddGenerator 5) = d7 ^ 2 * oddGenerator 1`, by composition rather than a direct
oddGenerator-level computation. The direct route OOMs even in isolation (the extra `d7`
factor from `kappa 5 = 1` propagating through the whole `piOperator`/`Ebar` pipeline pushes
the single-theorem file over the 4 GiB ceiling; see the abandoned `DeltaFactsProbe3.lean`).
Instead: lift the generator-level fact `delta_p_gen5_probe` through the
structural, degree-independent `delta_p_oddGenerator_kappa_one` reduction (valid since
`kappa 5 = 1`), then close the remaining polynomial identity with `ring`.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_p_odd5_eq_probe : delta_p (oddGenerator 5) = d7 ^ 2 * oddGenerator 1 := by
  refine delta_p_eq_of_reflect (ev_oddGenerator 5).symm (lQ := mulL (powL d7L 2) (oddGeneratorL 1)) (by simp only [ev_mulL, ev_powL, ev_d7, ev_oddGenerator]) ?_
  decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
