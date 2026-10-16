module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.AltBasics
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.LeibnizCaseGenericAlt
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.QuadrantPderivEvalR0
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.OperatorAdditivityBeta
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.SymmetricAlternatingBasics

@[expose] public section



/-!
Alternating mirror of `JPieceSym.lean`'s `jpiece_sym`: given a base witness `g0` for
`baseAlt j 0` and any `p : Poly2`, builds an alternating witness `v`/`g` for the single
`expandOdd`-summand `evalR0 p * oddGenerator j`, with its `piOperator`-value in closed
form, identical in shape to `jpiece_sym` (the quadrant-decomposition / Leibniz-case
machinery is symmetry-agnostic; only the "`v` is alternating" sub-goal differs in proof
method, and `baseSym` is replaced by `baseAlt` throughout).
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem jpiece_alt (j : Fin 8) {g0 : MvPolynomial (Fin 3) ℤ}
    (h0 : threeTermNorm (baseAlt j 0) = C 2 * g0) (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, IsAlternating v ∧ reduceTwo v = evalR0 p * oddGenerator j ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 p * piOperator (reduceTwo g0)
        + evalR0 (pderiv 1 p) * delta_q (oddGenerator j)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator j) := by
  obtain ⟨A, B, D, E, hp⟩ := exists_quadrant p
  obtain ⟨PA, hPA⟩ := exists_lift A
  obtain ⟨PB, hPB⟩ := exists_lift B
  obtain ⟨PD, hPD⟩ := exists_lift D
  obtain ⟨PE, hPE⟩ := exists_lift E
  obtain ⟨gA, hgA⟩ := baseAlt_term_half PA j 0
  obtain ⟨gB, hgB⟩ := baseAlt_term_half PB j 1
  obtain ⟨gD, hgD⟩ := baseAlt_term_half PD j 2
  obtain ⟨gE, hgE⟩ := baseAlt_term_half PE j 3
  have hc1 := case_j1_generic_alt h0
  have hc2 := case_j2_generic_alt h0
  have hc3 := case_j3_generic_alt h0
  have hAB := lemma_5_5_clause3 _ _ _ _ hgA hgB
  have hABD := lemma_5_5_clause3 _ _ _ _ hAB.1 hgD
  have hABDE := lemma_5_5_clause3 _ _ _ _ hABD.1 hgE
  refine ⟨evalSquaredLift PA * baseAlt j 0 + evalSquaredLift PB * baseAlt j 1
      + evalSquaredLift PD * baseAlt j 2 + evalSquaredLift PE * baseAlt j 3,
    gA + gB + gD + gE, ?_, ?_, hABDE.1, ?_⟩
  · -- `IsAlternating v`
    apply isAlternating_add
    apply isAlternating_add
    apply isAlternating_add
    · exact symmetric_mul_alternating (evalSquaredLift_isSymmetric PA) (baseAlt_isAlternating j 0)
    · exact symmetric_mul_alternating (evalSquaredLift_isSymmetric PB) (baseAlt_isAlternating j 1)
    · exact symmetric_mul_alternating (evalSquaredLift_isSymmetric PD) (baseAlt_isAlternating j 2)
    · exact symmetric_mul_alternating (evalSquaredLift_isSymmetric PE) (baseAlt_isAlternating j 3)
  · -- `reduceTwo v = evalR0 p * oddGenerator j`
    have hrA : reduceTwo (evalSquaredLift PA * baseAlt j 0) = evalR2 A * oddGenerator j := by
      rw [map_mul, reduceTwo_evalSquaredLift, hPA, reduceTwo_baseAlt]
      simp [mult]
      exact Or.inl rfl
    have hrB : reduceTwo (evalSquaredLift PB * baseAlt j 1)
        = evalR2 B * (d6 * oddGenerator j) := by
      rw [map_mul, reduceTwo_evalSquaredLift, hPB, reduceTwo_baseAlt]
      simp [mult, reduceTwo_liftD6]
      exact Or.inl rfl
    have hrD : reduceTwo (evalSquaredLift PD * baseAlt j 2)
        = evalR2 D * (d4 * oddGenerator j) := by
      rw [map_mul, reduceTwo_evalSquaredLift, hPD, reduceTwo_baseAlt]
      simp [mult, reduceTwo_liftD4]
      exact Or.inl rfl
    have hrE : reduceTwo (evalSquaredLift PE * baseAlt j 3)
        = evalR2 E * (d4 * d6 * oddGenerator j) := by
      rw [map_mul, reduceTwo_evalSquaredLift, hPE, reduceTwo_baseAlt]
      simp [mult, reduceTwo_liftD4, reduceTwo_liftD6]
      exact Or.inl rfl
    show reduceTwo (evalSquaredLift PA * baseAlt j 0 + evalSquaredLift PB * baseAlt j 1
        + evalSquaredLift PD * baseAlt j 2 + evalSquaredLift PE * baseAlt j 3)
        = evalR0 p * oddGenerator j
    rw [map_add, map_add, map_add, hrA, hrB, hrD, hrE, evalR0_quadrant_eq hp]
    ring
  · -- `piOperator (reduceTwo g) = ...`
    have e4A : piOperator (reduceTwo gA) = evalR2 A * piOperator (reduceTwo g0) := by
      have h := lemma_5_5_clause4 PA (baseAlt j 0) g0 gA h0 hgA
      rwa [reduceTwo_evalSquaredLift, hPA] at h
    have e4B : piOperator (reduceTwo gB)
        = evalR2 B * (d6 * piOperator (reduceTwo g0) + delta_q (oddGenerator j)) := by
      have h := lemma_5_5_clause4 PB (baseAlt j 1) _ gB hc1.1 hgB
      rwa [reduceTwo_evalSquaredLift, hPB, hc1.2] at h
    have e4D : piOperator (reduceTwo gD)
        = evalR2 D * (d4 * piOperator (reduceTwo g0) + delta_p (oddGenerator j)) := by
      have h := lemma_5_5_clause4 PD (baseAlt j 2) _ gD hc2.1 hgD
      rwa [reduceTwo_evalSquaredLift, hPD, hc2.2] at h
    have e4E : piOperator (reduceTwo gE) = evalR2 E * (d4 * d6 * piOperator (reduceTwo g0)
        + d4 * delta_q (oddGenerator j) + d6 * delta_p (oddGenerator j)) := by
      have h := lemma_5_5_clause4 PE (baseAlt j 3) _ gE hc3.1 hgE
      rwa [reduceTwo_evalSquaredLift, hPE, hc3.2] at h
    rw [hABDE.2, hABD.2, hAB.2, e4A, e4B, e4D, e4E,
      evalR0_quadrant_eq hp, evalR0_pderiv1_quadrant_eq hp, evalR0_pderiv0_quadrant_eq hp]
    ring

end TernaryPeriodPolynomials.Argument.ModFourBeta
