module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.JPieceAlt
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.WDBaseCases
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases2
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases3
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases4
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases10
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases11
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases12
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases22
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases22c
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases22d
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases23
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases23c
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases23d
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd0
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd1
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd2
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd3
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd4
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd5
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd6
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd7
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd0
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd1
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd2
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd3
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd4
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd5
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd6
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd7

@[expose] public section



/-!
Alternating mirror of `JPieceSymEval.lean`: per-`j` CLOSED-FORM corollaries of `jpiece_alt`,
one standalone top-level theorem each, matching that file's architecture exactly.


The only new ingredient versus the symmetric file is the base value for `baseAlt j 0`: by
`baseAlt_zero_half_pi j half_j_0`, `threeTermNorm (baseAlt j 0) = C 2 * (g0_sym + threeTermNorm (WD j))`
where `g0_sym` is the *same* literal `half_j_0` already supplies for `baseSym j 0`. Hence
`piOperator (reduceTwo g0) = piOperator (reduceTwo g0_sym) + piOperator (reduceTwo (threeTermNorm (WD j)))`
(via `map_add`/`piOperator_add`), and the two summands are resolved exactly as in the symmetric
file (`reduceTwo_gj0`, `pi_j_0`) and by the new `pi_reduceTwo_threeTermNorm_WD_j` (`WDBaseCases.lean`)
respectively. Since `pi_j_0 = 0` for every `j ≠ 4` (and `= oddGenerator 3` for `j = 4`), the
alternating base value is `oddGenerator j` for `j ≠ 4` and `oddGenerator 3 + oddGenerator 4` for
`j = 4` — unlike the symmetric case, this term never fully vanishes, since `WD j`'s own
contribution (`oddGenerator j`) is always present.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

set_option maxRecDepth 4096 in
theorem jpiece_alt_0 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, IsAlternating v ∧ reduceTwo v = evalR0 p * oddGenerator 0 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 p * oddGenerator 0
        + evalR0 (pderiv 1 p) * delta_q (oddGenerator 0)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 0) := by
  obtain ⟨v, g, hvalt, hvred, hvg, hvpi⟩ :=
    jpiece_alt 0 (baseAlt_zero_half_pi 0 half_0_0) p
  rw [map_add, piOperator_add, reduceTwo_g00, pi_0_0] at hvpi
  simp only [pi_reduceTwo_threeTermNorm_WD_0,
    delta_p_odd0_eq_probe, delta_q_odd0_eq_probe, mul_zero, zero_add] at hvpi ⊢
  exact ⟨v, g, hvalt, hvred, hvg, hvpi⟩

theorem jpiece_alt_1 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, IsAlternating v ∧ reduceTwo v = evalR0 p * oddGenerator 1 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 p * oddGenerator 1
        + evalR0 (pderiv 1 p) * delta_q (oddGenerator 1)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 1) := by
  obtain ⟨v, g, hvalt, hvred, hvg, hvpi⟩ :=
    jpiece_alt 1 (baseAlt_zero_half_pi 1 half_1_0) p
  rw [map_add, piOperator_add, reduceTwo_g10, pi_1_0] at hvpi
  simp only [pi_reduceTwo_threeTermNorm_WD_1,
    delta_p_odd1_eq_probe, delta_q_odd1_eq_probe, mul_zero, zero_add] at hvpi ⊢
  exact ⟨v, g, hvalt, hvred, hvg, hvpi⟩

set_option maxRecDepth 4096 in
theorem jpiece_alt_2 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, IsAlternating v ∧ reduceTwo v = evalR0 p * oddGenerator 2 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 p * oddGenerator 2
        + evalR0 (pderiv 1 p) * delta_q (oddGenerator 2)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 2) := by
  obtain ⟨v, g, hvalt, hvred, hvg, hvpi⟩ :=
    jpiece_alt 2 (baseAlt_zero_half_pi 2 half_2_0) p
  rw [map_add, piOperator_add, reduceTwo_g20, pi_2_0] at hvpi
  simp only [pi_reduceTwo_threeTermNorm_WD_2,
    delta_p_odd2_eq_probe, delta_q_odd2_eq_probe, mul_zero, zero_add] at hvpi ⊢
  exact ⟨v, g, hvalt, hvred, hvg, hvpi⟩

theorem jpiece_alt_3 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, IsAlternating v ∧ reduceTwo v = evalR0 p * oddGenerator 3 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 p * oddGenerator 3
        + evalR0 (pderiv 1 p) * delta_q (oddGenerator 3)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 3) := by
  obtain ⟨v, g, hvalt, hvred, hvg, hvpi⟩ :=
    jpiece_alt 3 (baseAlt_zero_half_pi 3 half_3_0) p
  rw [map_add, piOperator_add, reduceTwo_g30, pi_3_0] at hvpi
  simp only [pi_reduceTwo_threeTermNorm_WD_3,
    delta_p_odd3_eq_probe, delta_q_odd3_eq_probe, mul_zero, zero_add] at hvpi ⊢
  exact ⟨v, g, hvalt, hvred, hvg, hvpi⟩

theorem jpiece_alt_4 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, IsAlternating v ∧ reduceTwo v = evalR0 p * oddGenerator 4 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 p * (oddGenerator 3 + oddGenerator 4)
        + evalR0 (pderiv 1 p) * delta_q (oddGenerator 4)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 4) := by
  obtain ⟨v, g, hvalt, hvred, hvg, hvpi⟩ :=
    jpiece_alt 4 (baseAlt_zero_half_pi 4 half_4_0) p
  rw [map_add, piOperator_add, reduceTwo_g40, pi_4_0] at hvpi
  simp only [pi_reduceTwo_threeTermNorm_WD_4,
    delta_p_odd4_eq_probe, delta_q_odd4_eq_probe] at hvpi ⊢
  exact ⟨v, g, hvalt, hvred, hvg, hvpi⟩

theorem jpiece_alt_5 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, IsAlternating v ∧ reduceTwo v = evalR0 p * oddGenerator 5 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 p * oddGenerator 5
        + evalR0 (pderiv 1 p) * delta_q (oddGenerator 5)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 5) := by
  obtain ⟨v, g, hvalt, hvred, hvg, hvpi⟩ :=
    jpiece_alt 5 (baseAlt_zero_half_pi 5 half_5_0) p
  rw [map_add, piOperator_add, reduceTwo_g50, pi_5_0] at hvpi
  simp only [pi_reduceTwo_threeTermNorm_WD_5,
    delta_p_odd5_eq_probe, delta_q_odd5_eq_probe, zero_add] at hvpi ⊢
  exact ⟨v, g, hvalt, hvred, hvg, hvpi⟩

set_option maxRecDepth 4096 in
theorem jpiece_alt_6 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, IsAlternating v ∧ reduceTwo v = evalR0 p * oddGenerator 6 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 p * oddGenerator 6
        + evalR0 (pderiv 1 p) * delta_q (oddGenerator 6)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 6) := by
  obtain ⟨v, g, hvalt, hvred, hvg, hvpi⟩ :=
    jpiece_alt 6 (baseAlt_zero_half_pi 6 half_6_0) p
  rw [map_add, piOperator_add, reduceTwo_g60, pi_6_0] at hvpi
  simp only [pi_reduceTwo_threeTermNorm_WD_6,
    delta_p_odd6_eq_probe, delta_q_odd6_eq_probe, mul_zero, zero_add] at hvpi ⊢
  exact ⟨v, g, hvalt, hvred, hvg, hvpi⟩

theorem jpiece_alt_7 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, IsAlternating v ∧ reduceTwo v = evalR0 p * oddGenerator 7 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 p * oddGenerator 7
        + evalR0 (pderiv 1 p) * delta_q (oddGenerator 7)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 7) := by
  obtain ⟨v, g, hvalt, hvred, hvg, hvpi⟩ :=
    jpiece_alt 7 (baseAlt_zero_half_pi 7 half_7_0) p
  rw [map_add, piOperator_add, reduceTwo_g70, pi_7_0] at hvpi
  simp only [pi_reduceTwo_threeTermNorm_WD_7,
    delta_p_odd7_eq_probe, delta_q_odd7_eq_probe, zero_add] at hvpi ⊢
  exact ⟨v, g, hvalt, hvred, hvg, hvpi⟩

end TernaryPeriodPolynomials.Argument.ModFourBeta
