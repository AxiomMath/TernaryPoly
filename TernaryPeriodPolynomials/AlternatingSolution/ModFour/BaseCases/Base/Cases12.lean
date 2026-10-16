module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases

@[expose] public section


/-! More base cases for the 32-case `W(j,m)` table (continuation; see `BaseCases.lean`
through earlier `BaseCasesN.lean` files). Case (2,0), degree
13: carries only `pi_2_0`.
`reduceTwo g` is literally `0` here (not just `W == 0`), so `pi_2_0`'s
proof is a single `simp`. -/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

set_option maxRecDepth 4096 in
theorem pi_2_0 :
    piOperator
      (0 : Poly2) = 0 := by
  simp [piOperator, piSubstitutions]

end TernaryPeriodPolynomials.Argument.ModFourBeta
