module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases

@[expose] public section


/-! Case (5,0): the giant 105-term degree-14 literal that is the common argument of
`half_5_0` (`BaseCases22.lean`) and `reduceTwo_g50` (`BaseCases22c.lean`), split into
five smaller pieces.




`g50_part1 + g50_part2 + ... + g50_part5` is exactly


the same sum as the original literal, merely reassociated. -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

noncomputable def g50_part1 : MvPolynomial (Fin 3) ℤ :=
  -4 * X 1 ^ 5 * X 2 ^ 10 + 60 * X 1 ^ 6 * X 2 ^ 9 - 384 * X 1 ^ 7 * X 2 ^ 8 + 1364 * X 1 ^ 8 * X 2 ^ 7 - 2928 * X 1 ^ 9 * X 2 ^ 6 + 3876 * X 1 ^ 10 * X 2 ^ 5 - 3100 * X 1 ^ 11 * X 2 ^ 4 + 1416 * X 1 ^ 12 * X 2 ^ 3 - 336 * X 1 ^ 13 * X 2 ^ 2 + 32 * X 1 ^ 14 * X 2 + 10 * X 0 * X 1 ^ 4 * X 2 ^ 10 - 180 * X 0 * X 1 ^ 5 * X 2 ^ 9 + 1344 * X 0 * X 1 ^ 6 * X 2 ^ 8 - 5456 * X 0 * X 1 ^ 7 * X 2 ^ 7 + 13176 * X 0 * X 1 ^ 8 * X 2 ^ 6 - 19380 * X 0 * X 1 ^ 9 * X 2 ^ 5 + 17050 * X 0 * X 1 ^ 10 * X 2 ^ 4 - 8496 * X 0 * X 1 ^ 11 * X 2 ^ 3 + 2184 * X 0 * X 1 ^ 12 * X 2 ^ 2 - 224 * X 0 * X 1 ^ 13 * X 2 - 4 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 10

noncomputable def g50_part2 : MvPolynomial (Fin 3) ℤ :=
  252 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 9 - 1728 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 8 + 9259 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 7 - 24732 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 6 + 41664 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 5 - 40666 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 4 + 22335 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 3 - 6264 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 2 + 696 * X 0 ^ 2 * X 1 ^ 12 * X 2 - 4 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 10 - 204 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 9 + 960 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 8 - 8681 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 7 + 25074 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 6 - 50376 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 5 + 55122 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 4 - 33795 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 3 + 10428 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 2 - 1264 * X 0 ^ 3 * X 1 ^ 11 * X 2 + 10 * X 0 ^ 4 * X 1 * X 2 ^ 10 + 252 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 9

noncomputable def g50_part3 : MvPolynomial (Fin 3) ℤ :=
  960 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 8 + 8392 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 7 - 9126 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 6 + 42612 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 5 - 44412 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 4 + 33009 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 3 - 11100 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 2 + 1487 * X 0 ^ 4 * X 1 ^ 10 * X 2 - 4 * X 0 ^ 5 * X 2 ^ 10 - 180 * X 0 ^ 5 * X 1 * X 2 ^ 9 - 1728 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 8 - 8681 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 7 - 9126 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 6 - 32916 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 5 + 17556 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 4 - 22722 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 3 + 7776 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 2 - 1187 * X 0 ^ 5 * X 1 ^ 9 * X 2 + 60 * X 0 ^ 6 * X 2 ^ 9 + 1344 * X 0 ^ 6 * X 1 * X 2 ^ 8 + 9259 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 7

noncomputable def g50_part4 : MvPolynomial (Fin 3) ℤ :=
  25074 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 6 + 42612 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 5 + 17556 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 4 + 17922 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 3 - 2520 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 2 + 709 * X 0 ^ 6 * X 1 ^ 8 * X 2 - 384 * X 0 ^ 7 * X 2 ^ 8 - 5456 * X 0 ^ 7 * X 1 * X 2 ^ 7 - 24732 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 6 - 50376 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 5 - 44412 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 4 - 22722 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 3 - 2520 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 2 - 466 * X 0 ^ 7 * X 1 ^ 7 * X 2 + 1364 * X 0 ^ 8 * X 2 ^ 7 + 13176 * X 0 ^ 8 * X 1 * X 2 ^ 6 + 41664 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 5 + 55122 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 4 + 33009 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 3 + 7776 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 2 + 709 * X 0 ^ 8 * X 1 ^ 6 * X 2

noncomputable def g50_part5 : MvPolynomial (Fin 3) ℤ :=
  -2928 * X 0 ^ 9 * X 2 ^ 6 - 19380 * X 0 ^ 9 * X 1 * X 2 ^ 5 - 40666 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 4 - 33795 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 3 - 11100 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 2 - 1187 * X 0 ^ 9 * X 1 ^ 5 * X 2 + 3876 * X 0 ^ 10 * X 2 ^ 5 + 17050 * X 0 ^ 10 * X 1 * X 2 ^ 4 + 22335 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 3 + 10428 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 2 + 1487 * X 0 ^ 10 * X 1 ^ 4 * X 2 - 3100 * X 0 ^ 11 * X 2 ^ 4 - 8496 * X 0 ^ 11 * X 1 * X 2 ^ 3 - 6264 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 2 - 1264 * X 0 ^ 11 * X 1 ^ 3 * X 2 + 1416 * X 0 ^ 12 * X 2 ^ 3 + 2184 * X 0 ^ 12 * X 1 * X 2 ^ 2 + 696 * X 0 ^ 12 * X 1 ^ 2 * X 2 - 336 * X 0 ^ 13 * X 2 ^ 2 - 224 * X 0 ^ 13 * X 1 * X 2 + 32 * X 0 ^ 14 * X 2

end TernaryPeriodPolynomials.Argument.ModFourBeta
