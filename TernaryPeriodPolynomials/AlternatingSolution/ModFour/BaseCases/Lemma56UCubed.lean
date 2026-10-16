module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs

@[expose] public section


/-!
# `U³ = 0` (second half of Lemma 5.6, `mf:lem:beta`)

`uOperator s` depends only on `s 4, s 5, s 7`, and its own outputs at indices `5` and `7`
are always `0` regardless of the input. Hence after two applications the coordinates
`4, 5, 7` of the result all vanish, so a third application sends everything to `0`.
-/

open MvPolynomial
open TernaryPeriodPolynomials.Argument

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem uOperator_five (s : Fin 8 → MvPolynomial (Fin 3) (ZMod 2)) :
    uOperator s 5 = 0 := by
  simp [uOperator]

private theorem uOperator_seven (s : Fin 8 → MvPolynomial (Fin 3) (ZMod 2)) :
    uOperator s 7 = 0 := by
  simp [uOperator]

private theorem uOperator_four_of_five_seven
    (s : Fin 8 → MvPolynomial (Fin 3) (ZMod 2)) (h5 : s 5 = 0) (h7 : s 7 = 0) :
    uOperator s 4 = 0 := by
  simp [uOperator, h5, h7]

theorem uOperator_cubed (r : Fin 8 → MvPolynomial (Fin 3) (ZMod 2)) :
    uOperator (uOperator (uOperator r)) = 0 := by
  have h5 : uOperator r 5 = 0 := uOperator_five r
  have h7 : uOperator r 7 = 0 := uOperator_seven r
  have ht4 : uOperator (uOperator r) 4 = 0 := uOperator_four_of_five_seven (uOperator r) h5 h7
  have ht5 : uOperator (uOperator r) 5 = 0 := uOperator_five (uOperator r)
  have ht7 : uOperator (uOperator r) 7 = 0 := uOperator_seven (uOperator r)
  set t := uOperator (uOperator r) with ht_def
  funext i
  fin_cases i <;> simp [uOperator, ht4, ht5, ht7]

end TernaryPeriodPolynomials.Argument.ModFourBeta
