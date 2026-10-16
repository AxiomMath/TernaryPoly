module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.SymIsSymmetric
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.SymEvenNorm
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.LeibnizCaseGeneric
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.QuadrantPderivEvalR0
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.OperatorAdditivityBeta
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.SymmetricAlternatingBasics

@[expose] public section



/-!
Per-`j` symmetric-case helper for `modFour_beta_triangular`'s first conjunct: given a base witness
`g0` for `baseSym j 0` and any `p : Poly2`, builds a symmetric witness `v`/`g` for the
single `expandOdd`-summand `evalR0 p * oddGenerator j`, with its `piOperator`-value in
closed form in terms of `piOperator (reduceTwo g0)`, `delta_p (oddGenerator j)` and
`delta_q (oddGenerator j)`. Summing this over `j : Fin 8` with `p := r j` reconstructs
`expandOdd (uOperator r)`.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem jpiece_sym (j : Fin 8) {g0 : MvPolynomial (Fin 3) ℤ}
    (h0 : threeTermNorm (baseSym j 0) = C 2 * g0) (p : Poly2) :
    ∃ v g : MvPolynomial (Fin 3) ℤ, v.IsSymmetric ∧ reduceTwo v = evalR0 p * oddGenerator j ∧
      threeTermNorm v = C 2 * g ∧
      piOperator (reduceTwo g) = evalR0 p * piOperator (reduceTwo g0)
        + evalR0 (pderiv 1 p) * delta_q (oddGenerator j)
        + evalR0 (pderiv 0 p) * delta_p (oddGenerator j) := by
  obtain ⟨A, B, D, E, hp⟩ := exists_quadrant p
  obtain ⟨PA, hPA⟩ := exists_lift A
  obtain ⟨PB, hPB⟩ := exists_lift B
  obtain ⟨PD, hPD⟩ := exists_lift D
  obtain ⟨PE, hPE⟩ := exists_lift E
  obtain ⟨gA, hgA⟩ := baseSym_term_half PA j 0
  obtain ⟨gB, hgB⟩ := baseSym_term_half PB j 1
  obtain ⟨gD, hgD⟩ := baseSym_term_half PD j 2
  obtain ⟨gE, hgE⟩ := baseSym_term_half PE j 3
  have hc1 := case_j1_generic h0
  have hc2 := case_j2_generic h0
  have hc3 := case_j3_generic h0
  have hAB := lemma_5_5_clause3 _ _ _ _ hgA hgB
  have hABD := lemma_5_5_clause3 _ _ _ _ hAB.1 hgD
  have hABDE := lemma_5_5_clause3 _ _ _ _ hABD.1 hgE
  refine ⟨evalSquaredLift PA * baseSym j 0 + evalSquaredLift PB * baseSym j 1
      + evalSquaredLift PD * baseSym j 2 + evalSquaredLift PE * baseSym j 3,
    gA + gB + gD + gE, ?_, ?_, hABDE.1, ?_⟩
  · -- `v.IsSymmetric`
    apply IsSymmetric.add
    apply IsSymmetric.add
    apply IsSymmetric.add
    · exact (evalSquaredLift_isSymmetric PA).mul (baseSym_isSymmetric j 0)
    · exact (evalSquaredLift_isSymmetric PB).mul (baseSym_isSymmetric j 1)
    · exact (evalSquaredLift_isSymmetric PD).mul (baseSym_isSymmetric j 2)
    · exact (evalSquaredLift_isSymmetric PE).mul (baseSym_isSymmetric j 3)
  · -- `reduceTwo v = evalR0 p * oddGenerator j`
    have hrA : reduceTwo (evalSquaredLift PA * baseSym j 0) = evalR2 A * oddGenerator j := by
      rw [map_mul, reduceTwo_evalSquaredLift, hPA, reduceTwo_baseSym]
      simp [mult]
      exact Or.inl rfl
    have hrB : reduceTwo (evalSquaredLift PB * baseSym j 1)
        = evalR2 B * (d6 * oddGenerator j) := by
      rw [map_mul, reduceTwo_evalSquaredLift, hPB, reduceTwo_baseSym]
      simp [mult, reduceTwo_liftD6]
      exact Or.inl rfl
    have hrD : reduceTwo (evalSquaredLift PD * baseSym j 2)
        = evalR2 D * (d4 * oddGenerator j) := by
      rw [map_mul, reduceTwo_evalSquaredLift, hPD, reduceTwo_baseSym]
      simp [mult, reduceTwo_liftD4]
      exact Or.inl rfl
    have hrE : reduceTwo (evalSquaredLift PE * baseSym j 3)
        = evalR2 E * (d4 * d6 * oddGenerator j) := by
      rw [map_mul, reduceTwo_evalSquaredLift, hPE, reduceTwo_baseSym]
      simp [mult, reduceTwo_liftD4, reduceTwo_liftD6]
      exact Or.inl rfl
    show reduceTwo (evalSquaredLift PA * baseSym j 0 + evalSquaredLift PB * baseSym j 1
        + evalSquaredLift PD * baseSym j 2 + evalSquaredLift PE * baseSym j 3)
        = evalR0 p * oddGenerator j
    rw [map_add, map_add, map_add, hrA, hrB, hrD, hrE, evalR0_quadrant_eq hp]
    ring
  · -- `piOperator (reduceTwo g) = ...`
    have e4A : piOperator (reduceTwo gA) = evalR2 A * piOperator (reduceTwo g0) := by
      have h := lemma_5_5_clause4 PA (baseSym j 0) g0 gA h0 hgA
      rwa [reduceTwo_evalSquaredLift, hPA] at h
    have e4B : piOperator (reduceTwo gB)
        = evalR2 B * (d6 * piOperator (reduceTwo g0) + delta_q (oddGenerator j)) := by
      have h := lemma_5_5_clause4 PB (baseSym j 1) _ gB hc1.1 hgB
      rwa [reduceTwo_evalSquaredLift, hPB, hc1.2] at h
    have e4D : piOperator (reduceTwo gD)
        = evalR2 D * (d4 * piOperator (reduceTwo g0) + delta_p (oddGenerator j)) := by
      have h := lemma_5_5_clause4 PD (baseSym j 2) _ gD hc2.1 hgD
      rwa [reduceTwo_evalSquaredLift, hPD, hc2.2] at h
    have e4E : piOperator (reduceTwo gE) = evalR2 E * (d4 * d6 * piOperator (reduceTwo g0)
        + d4 * delta_q (oddGenerator j) + d6 * delta_p (oddGenerator j)) := by
      have h := lemma_5_5_clause4 PE (baseSym j 3) _ gE hc3.1 hgE
      rwa [reduceTwo_evalSquaredLift, hPE, hc3.2] at h
    rw [hABDE.2, hABD.2, hAB.2, e4A, e4B, e4D, e4E,
      evalR0_quadrant_eq hp, evalR0_pderiv1_quadrant_eq hp, evalR0_pderiv0_quadrant_eq hp]
    ring

end TernaryPeriodPolynomials.Argument.ModFourBeta
