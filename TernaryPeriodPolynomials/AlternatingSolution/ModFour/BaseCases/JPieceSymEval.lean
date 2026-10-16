module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.JPieceSym
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
Per-`j` CLOSED-FORM corollaries of `jpiece_sym`, one standalone top-level theorem each,
with the base-value table (`pi_j_0`) and delta-probe table already substituted into the
statement.








-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem jpiece_0 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, v.IsSymmetric ∧ reduceTwo v = evalR0 p * oddGenerator 0 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 (pderiv 1 p) * delta_q (oddGenerator 0)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 0) := by
  obtain ⟨v, g, hvsym, hvred, hvg, hvpi⟩ := jpiece_sym 0 half_0_0 p
  simp only [reduceTwo_g00, pi_0_0, delta_p_odd0_eq_probe, delta_q_odd0_eq_probe,
    mul_zero, zero_add] at hvpi ⊢
  exact ⟨v, g, hvsym, hvred, hvg, hvpi⟩

theorem jpiece_1 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, v.IsSymmetric ∧ reduceTwo v = evalR0 p * oddGenerator 1 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 (pderiv 1 p) * delta_q (oddGenerator 1)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 1) := by
  obtain ⟨v, g, hvsym, hvred, hvg, hvpi⟩ := jpiece_sym 1 half_1_0 p
  simp only [reduceTwo_g10, pi_1_0, delta_p_odd1_eq_probe, delta_q_odd1_eq_probe,
    mul_zero, zero_add] at hvpi ⊢
  exact ⟨v, g, hvsym, hvred, hvg, hvpi⟩

theorem jpiece_2 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, v.IsSymmetric ∧ reduceTwo v = evalR0 p * oddGenerator 2 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 (pderiv 1 p) * delta_q (oddGenerator 2)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 2) := by
  obtain ⟨v, g, hvsym, hvred, hvg, hvpi⟩ := jpiece_sym 2 half_2_0 p
  simp only [reduceTwo_g20, pi_2_0, delta_p_odd2_eq_probe, delta_q_odd2_eq_probe,
    mul_zero, zero_add] at hvpi ⊢
  exact ⟨v, g, hvsym, hvred, hvg, hvpi⟩

theorem jpiece_3 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, v.IsSymmetric ∧ reduceTwo v = evalR0 p * oddGenerator 3 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 (pderiv 1 p) * delta_q (oddGenerator 3)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 3) := by
  obtain ⟨v, g, hvsym, hvred, hvg, hvpi⟩ := jpiece_sym 3 half_3_0 p
  simp only [reduceTwo_g30, pi_3_0, delta_p_odd3_eq_probe, delta_q_odd3_eq_probe,
    mul_zero, zero_add] at hvpi ⊢
  exact ⟨v, g, hvsym, hvred, hvg, hvpi⟩

theorem jpiece_4 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, v.IsSymmetric ∧ reduceTwo v = evalR0 p * oddGenerator 4 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 p * oddGenerator 3
        + evalR0 (pderiv 1 p) * delta_q (oddGenerator 4)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 4) := by
  obtain ⟨v, g, hvsym, hvred, hvg, hvpi⟩ := jpiece_sym 4 half_4_0 p
  simp only [reduceTwo_g40, pi_4_0, delta_p_odd4_eq_probe, delta_q_odd4_eq_probe] at hvpi ⊢
  exact ⟨v, g, hvsym, hvred, hvg, hvpi⟩

theorem jpiece_5 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, v.IsSymmetric ∧ reduceTwo v = evalR0 p * oddGenerator 5 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 (pderiv 1 p) * delta_q (oddGenerator 5)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 5) := by
  obtain ⟨v, g, hvsym, hvred, hvg, hvpi⟩ := jpiece_sym 5 half_5_0 p
  simp only [reduceTwo_g50, pi_5_0, delta_p_odd5_eq_probe, delta_q_odd5_eq_probe,
    mul_zero, zero_add] at hvpi ⊢
  exact ⟨v, g, hvsym, hvred, hvg, hvpi⟩

theorem jpiece_6 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, v.IsSymmetric ∧ reduceTwo v = evalR0 p * oddGenerator 6 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 (pderiv 1 p) * delta_q (oddGenerator 6)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 6) := by
  obtain ⟨v, g, hvsym, hvred, hvg, hvpi⟩ := jpiece_sym 6 half_6_0 p
  simp only [reduceTwo_g60, pi_6_0, delta_p_odd6_eq_probe, delta_q_odd6_eq_probe,
    mul_zero, zero_add] at hvpi ⊢
  exact ⟨v, g, hvsym, hvred, hvg, hvpi⟩

theorem jpiece_7 (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, v.IsSymmetric ∧ reduceTwo v = evalR0 p * oddGenerator 7 ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 (pderiv 1 p) * delta_q (oddGenerator 7)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator 7) := by
  obtain ⟨v, g, hvsym, hvred, hvg, hvpi⟩ := jpiece_sym 7 half_7_0 p
  simp only [reduceTwo_g70, pi_7_0, delta_p_odd7_eq_probe, delta_q_odd7_eq_probe,
    mul_zero, zero_add] at hvpi ⊢
  exact ⟨v, g, hvsym, hvred, hvg, hvpi⟩

end TernaryPeriodPolynomials.Argument.ModFourBeta
