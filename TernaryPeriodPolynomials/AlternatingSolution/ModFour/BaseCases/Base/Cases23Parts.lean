module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases

@[expose] public section


/-! Case (7,0): the giant 143-term degree-17 literal that is the common argument of
`half_7_0` (`BaseCases23.lean`), `reduceTwo_g70` (`BaseCases23c.lean`), and `pi_7_0`
(`BaseCases23d.lean`), split into seven smaller pieces.

Splitting into separate top-level `def`s keeps each piece's own instance resolution
small and self-contained.

`g70_part1 + g70_part2 + ... + g70_part7` is exactly


the same sum as the original literal, merely reassociated. -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

noncomputable def g70_part1 : MvPolynomial (Fin 3) ℤ :=
  2 * X 1 ^ 4 * X 2 ^ 13 - 44 * X 1 ^ 5 * X 2 ^ 12 + 440 * X 1 ^ 6 * X 2 ^ 11 - 2652 * X 1 ^ 7 * X 2 ^ 10 + 10682 * X 1 ^ 8 * X 2 ^ 9 - 30024 * X 1 ^ 9 * X 2 ^ 8 + 59770 * X 1 ^ 10 * X 2 ^ 7 - 84112 * X 1 ^ 11 * X 2 ^ 6 + 82360 * X 1 ^ 12 * X 2 ^ 5 - 54280 * X 1 ^ 13 * X 2 ^ 4 + 22626 * X 1 ^ 14 * X 2 ^ 3 - 5288 * X 1 ^ 15 * X 2 ^ 2 + 520 * X 1 ^ 16 * X 2 - 4 * X 0 * X 1 ^ 3 * X 2 ^ 13 + 110 * X 0 * X 1 ^ 4 * X 2 ^ 12 - 1320 * X 0 * X 1 ^ 5 * X 2 ^ 11 + 9282 * X 0 * X 1 ^ 6 * X 2 ^ 10 - 42728 * X 0 * X 1 ^ 7 * X 2 ^ 9 + 135108 * X 0 * X 1 ^ 8 * X 2 ^ 8 - 298850 * X 0 * X 1 ^ 9 * X 2 ^ 7 + 462616 * X 0 * X 1 ^ 10 * X 2 ^ 6

noncomputable def g70_part2 : MvPolynomial (Fin 3) ℤ :=
  -494160 * X 0 * X 1 ^ 11 * X 2 ^ 5 + 352820 * X 0 * X 1 ^ 12 * X 2 ^ 4 - 158382 * X 0 * X 1 ^ 13 * X 2 ^ 3 + 39660 * X 0 * X 1 ^ 14 * X 2 ^ 2 - 4160 * X 0 * X 1 ^ 15 * X 2 + 6 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 13 - 44 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 12 + 1851 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 11 - 11934 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 10 + 73527 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 9 - 255308 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 8 + 651348 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 7 - 1116516 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 6 + 1319657 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 5 - 1029080 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 4 + 501365 * X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 3 - 135280 * X 0 ^ 2 * X 1 ^ 13 * X 2 ^ 2 + 15204 * X 0 ^ 2 * X 1 ^ 14 * X 2 - 4 * X 0 ^ 3 * X 1 * X 2 ^ 13 - 44 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 12 - 1502 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 11

noncomputable def g70_part3 : MvPolynomial (Fin 3) ℤ :=
  6630 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 10 - 71033 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 9 + 263074 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 8 - 812292 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 7 + 1554702 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 6 - 2068485 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 5 + 1778920 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 4 - 949224 * X 0 ^ 3 * X 1 ^ 11 * X 2 ^ 3 + 277810 * X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 2 - 33628 * X 0 ^ 3 * X 1 ^ 13 * X 2 + 2 * X 0 ^ 4 * X 2 ^ 13 + 110 * X 0 ^ 4 * X 1 * X 2 ^ 12 + 1851 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 11 + 6630 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 10 + 69786 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 9 - 97838 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 8 + 728034 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 7 - 1296932 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 6 + 2162750 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 5 - 2007500 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 4 + 1201802 * X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 3

noncomputable def g70_part4 : MvPolynomial (Fin 3) ℤ :=
  -382636 * X 0 ^ 4 * X 1 ^ 11 * X 2 ^ 2 + 50261 * X 0 ^ 4 * X 1 ^ 12 * X 2 - 44 * X 0 ^ 5 * X 2 ^ 12 - 1320 * X 0 ^ 5 * X 1 * X 2 ^ 11 - 11934 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 10 - 71033 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 9 - 97838 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 8 - 596250 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 7 + 522298 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 6 - 1675850 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 5 + 1513380 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 4 - 1082561 * X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 3 + 371910 * X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 2 - 53682 * X 0 ^ 5 * X 1 ^ 11 * X 2 + 440 * X 0 ^ 6 * X 2 ^ 11 + 9282 * X 0 ^ 6 * X 1 * X 2 ^ 10 + 73527 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 9 + 263074 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 8 + 728034 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 7 + 522298 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 6

noncomputable def g70_part5 : MvPolynomial (Fin 3) ℤ :=
  1429816 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 5 - 527120 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 4 + 786782 * X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 3 - 250748 * X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 2 + 42829 * X 0 ^ 6 * X 1 ^ 10 * X 2 - 2652 * X 0 ^ 7 * X 2 ^ 10 - 42728 * X 0 ^ 7 * X 1 * X 2 ^ 9 - 255308 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 8 - 812292 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 7 - 1296932 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 6 - 1675850 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 5 - 527120 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 4 - 622190 * X 0 ^ 7 * X 1 ^ 7 * X 2 ^ 3 + 87216 * X 0 ^ 7 * X 1 ^ 8 * X 2 ^ 2 - 27794 * X 0 ^ 7 * X 1 ^ 9 * X 2 + 10682 * X 0 ^ 8 * X 2 ^ 9 + 135108 * X 0 ^ 8 * X 1 * X 2 ^ 8 + 651348 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 7 + 1554702 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 6 + 2162750 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 5

noncomputable def g70_part6 : MvPolynomial (Fin 3) ℤ :=
  1513380 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 4 + 786782 * X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 3 + 87216 * X 0 ^ 8 * X 1 ^ 7 * X 2 ^ 2 + 21420 * X 0 ^ 8 * X 1 ^ 8 * X 2 - 30024 * X 0 ^ 9 * X 2 ^ 8 - 298850 * X 0 ^ 9 * X 1 * X 2 ^ 7 - 1116516 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 6 - 2068485 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 5 - 2007500 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 4 - 1082561 * X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 3 - 250748 * X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 2 - 27794 * X 0 ^ 9 * X 1 ^ 7 * X 2 + 59770 * X 0 ^ 10 * X 2 ^ 7 + 462616 * X 0 ^ 10 * X 1 * X 2 ^ 6 + 1319657 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 5 + 1778920 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 4 + 1201802 * X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 3 + 371910 * X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 2 + 42829 * X 0 ^ 10 * X 1 ^ 6 * X 2 - 84112 * X 0 ^ 11 * X 2 ^ 6

noncomputable def g70_part7 : MvPolynomial (Fin 3) ℤ :=
  -494160 * X 0 ^ 11 * X 1 * X 2 ^ 5 - 1029080 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 4 - 949224 * X 0 ^ 11 * X 1 ^ 3 * X 2 ^ 3 - 382636 * X 0 ^ 11 * X 1 ^ 4 * X 2 ^ 2 - 53682 * X 0 ^ 11 * X 1 ^ 5 * X 2 + 82360 * X 0 ^ 12 * X 2 ^ 5 + 352820 * X 0 ^ 12 * X 1 * X 2 ^ 4 + 501365 * X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 3 + 277810 * X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 2 + 50261 * X 0 ^ 12 * X 1 ^ 4 * X 2 - 54280 * X 0 ^ 13 * X 2 ^ 4 - 158382 * X 0 ^ 13 * X 1 * X 2 ^ 3 - 135280 * X 0 ^ 13 * X 1 ^ 2 * X 2 ^ 2 - 33628 * X 0 ^ 13 * X 1 ^ 3 * X 2 + 22626 * X 0 ^ 14 * X 2 ^ 3 + 39660 * X 0 ^ 14 * X 1 * X 2 ^ 2 + 15204 * X 0 ^ 14 * X 1 ^ 2 * X 2 - 5288 * X 0 ^ 15 * X 2 ^ 2 - 4160 * X 0 ^ 15 * X 1 * X 2 + 520 * X 0 ^ 16 * X 2

end TernaryPeriodPolynomials.Argument.ModFourBeta
