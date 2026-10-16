module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.CoeffAbsTable
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.PivotDecompositions
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.GenAbsComponent
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.PsiMap

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial
open TernaryPoly.DicksonQuotient (Poly a b c d4 d6 d7 invariantEval standardMonomial
  invariantEval_a invariantEval_b invariantEval_c)


/-- On-support degree bound: wherever `coeffAbs i m ≠ 0`, slot `m`'s `stdDeg` is at most row
`i`'s `genAbsDeg`. Needed because `isWeightedHomogeneous_coeffAbs` alone (stated with truncated
`ℕ`-subtraction `genAbsDeg i - stdDeg m`) does not by itself rule out `stdDeg m > genAbsDeg i`,
where that subtraction silently floors to `0`. -/
theorem stdDeg_le_genAbsDeg_of_coeffAbs_ne_zero (i : Fin 8) (m : Fin 28)
    (h : coeffAbs i m ≠ 0) : stdDeg m ≤ genAbsDeg i := by
  fin_cases i <;> fin_cases m <;>
    simp_all [coeffAbs, coeffAbs0, coeffAbs1, coeffAbs2, coeffAbs3, coeffAbs4, coeffAbs5,
      coeffAbs6, coeffAbs7, stdDeg, genAbsDeg]

/-- Each `qTerm`-summand is `![4,6,7]`-weighted-homogeneous of the degree the final assembly
needs (`N - stdDeg m`), whether or not `genAbsDeg i ≤ N` and whether or not `coeffAbs i m = 0`. -/
theorem isWeightedHomogeneous_qTerm (p : Fin 8 → Poly) (N : ℕ) (i : Fin 8) (m : Fin 28) :
    IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ)
      (if genAbsDeg i ≤ N then
          weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (N - genAbsDeg i) (p i) *
            coeffAbs i m
        else 0)
      (N - stdDeg m) := by
  split_ifs with hN
  · rcases eq_or_ne (coeffAbs i m) 0 with h0 | h0
    · rw [h0, mul_zero]
      exact isWeightedHomogeneous_zero _ _ _
    · have hle : stdDeg m ≤ genAbsDeg i := stdDeg_le_genAbsDeg_of_coeffAbs_ne_zero i m h0
      have hc := isWeightedHomogeneous_coeffAbs i m
      have hcomp := weightedHomogeneousComponent_isWeightedHomogeneous
        (w := (![4, 6, 7] : Fin 3 → ℕ)) (N - genAbsDeg i) (p i)
      have hmul := hcomp.mul hc
      have hdeg : (N - genAbsDeg i) + (genAbsDeg i - stdDeg m) = N - stdDeg m := by omega
      rwa [hdeg] at hmul
  · exact isWeightedHomogeneous_zero _ _ _

/-- The slot-`m` coefficient family extracted from `p`'s own `![4,6,7]`-truncation at degree
`N`: `qFam p N m := ∑ i, (if genAbsDeg i ≤ N then <degree-(N-genAbsDeg i) component of p i> *
coeffAbs i m else 0)`. -/
noncomputable def qFam (p : Fin 8 → Poly) (N : ℕ) (m : Fin 28) : Poly :=
  ∑ i : Fin 8, if genAbsDeg i ≤ N then
      weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (N - genAbsDeg i) (p i) * coeffAbs i m
    else 0

theorem isWeightedHomogeneous_qFam (p : Fin 8 → Poly) (N : ℕ) (m : Fin 28) :
    IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (qFam p N m) (N - stdDeg m) :=
  (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp
    (Submodule.sum_mem _ (fun i _ =>
      (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        (isWeightedHomogeneous_qTerm p N i m)))


/-- Each `genAbs i` is literally the `invariantEval`-pushforward of its `coeffAbs i` row, summed
against `standardMonomial`. The bridge back from the `![4,6,7]`-abstract coefficient table
(`CoeffAbsTable.lean`) to the concrete `genAbs` expansions (`PivotDecompositions.lean`). -/
theorem genAbs_eq_sum_coeffAbs (i : Fin 8) :
    genAbs i = ∑ j : Fin 28, invariantEval (coeffAbs i j) * standardMonomial j := by
  fin_cases i <;>
    simp [genAbs0_decomp, genAbs1_decomp, genAbs2_decomp, genAbs3_decomp, genAbs4_decomp,
      genAbs5_decomp, genAbs6_decomp, genAbs7_decomp, coeffAbs, coeffAbs0, coeffAbs1, coeffAbs2,
      coeffAbs3, coeffAbs4, coeffAbs5, coeffAbs6, coeffAbs7, Fin.sum_univ_succ,
      invariantEval_a, invariantEval_b, invariantEval_c, map_one, map_zero] <;>
    ring


/-- **Lemma A, pivot extraction.** Given the global hypothesis `∑ i, invariantEval (p i) *
genAbs i = 0`, any truncation degree `N`, and any slot `m₀` with `stdDeg m₀ ≤ N`, the slot-`m₀`
coefficient family `qFam p N` vanishes. This is the per-degree, per-slot zero fact that
`LemmaA.lean`'s elimination argument will instantiate at each pivot. -/
theorem qFam_eq_zero (p : Fin 8 → Poly) (hsum : ∑ i : Fin 8, invariantEval (p i) * genAbs i = 0)
    (N : ℕ) (m₀ : Fin 28) (hm₀ : stdDeg m₀ ≤ N) : qFam p N m₀ = 0 := by
  have step1 : ∀ i : Fin 28,
      (if stdDeg i ≤ N then invariantEval (qFam p N i) * standardMonomial i else 0)
      = ∑ k : Fin 8, (if stdDeg i ≤ N then
            (if genAbsDeg k ≤ N then
                invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
                  (N - genAbsDeg k) (p k) * coeffAbs k i)
              else 0) * standardMonomial i
          else 0) := by
    intro i
    split_ifs with h
    · simp only [qFam, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [apply_ite invariantEval, map_zero]
    · simp
  have step2 : ∀ k : Fin 8, ∑ i : Fin 28, (if stdDeg i ≤ N then
          (if genAbsDeg k ≤ N then
              invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
                (N - genAbsDeg k) (p k) * coeffAbs k i)
            else 0) * standardMonomial i
        else 0)
      = if genAbsDeg k ≤ N then
          invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
            (N - genAbsDeg k) (p k)) * genAbs k
        else 0 := by
    intro k
    split_ifs with hk
    · have hsimp : ∀ i : Fin 28, (if stdDeg i ≤ N then
            invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
              (N - genAbsDeg k) (p k) * coeffAbs k i) * standardMonomial i
          else 0)
          = invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
              (N - genAbsDeg k) (p k) * coeffAbs k i) * standardMonomial i := by
        intro i
        split_ifs with h
        · rfl
        · have hz : coeffAbs k i = 0 := by
            by_contra hne
            exact h (le_trans (stdDeg_le_genAbsDeg_of_coeffAbs_ne_zero k i hne) hk)
          simp [hz]
      rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
      have hmul : ∀ i : Fin 28,
          invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
              (N - genAbsDeg k) (p k) * coeffAbs k i) * standardMonomial i =
          invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
              (N - genAbsDeg k) (p k)) * (invariantEval (coeffAbs k i) * standardMonomial i) := by
        intro i
        rw [map_mul, mul_assoc]
      rw [Finset.sum_congr rfl (fun i _ => hmul i), ← Finset.mul_sum, ← genAbs_eq_sum_coeffAbs k]
    · apply Finset.sum_eq_zero
      intro i _
      simp
  have hL0 : ∑ i : Fin 28,
      (if stdDeg i ≤ N then invariantEval (qFam p N i) * standardMonomial i else 0) = 0 := by
    calc ∑ i : Fin 28, (if stdDeg i ≤ N then invariantEval (qFam p N i) * standardMonomial i else 0)
        = ∑ i : Fin 28, ∑ k : Fin 8, (if stdDeg i ≤ N then
              (if genAbsDeg k ≤ N then
                  invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
                    (N - genAbsDeg k) (p k) * coeffAbs k i)
                else 0) * standardMonomial i
            else 0) := Finset.sum_congr rfl (fun i _ => step1 i)
      _ = ∑ k : Fin 8, ∑ i : Fin 28, (if stdDeg i ≤ N then
              (if genAbsDeg k ≤ N then
                  invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
                    (N - genAbsDeg k) (p k) * coeffAbs k i)
                else 0) * standardMonomial i
            else 0) := Finset.sum_comm
      _ = ∑ k : Fin 8, (if genAbsDeg k ≤ N then
            invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
              (N - genAbsDeg k) (p k)) * genAbs k
          else 0) := Finset.sum_congr rfl (fun k _ => step2 k)
      _ = 0 := weightedHomogeneousComponent_sum_invariantEval_mul_genAbs p N hsum
  have heq : ∑ m : {m : Fin 28 // stdDeg m ≤ N}, invariantEval (qFam p N m.1) * standardMonomial m.1 =
      ∑ m : {m : Fin 28 // stdDeg m ≤ N}, invariantEval (0 : Poly) * standardMonomial m.1 := by
    have hlhs : ∑ m : {m : Fin 28 // stdDeg m ≤ N},
        invariantEval (qFam p N m.1) * standardMonomial m.1 = 0 := by
      rw [← hL0, ← Finset.sum_filter]
      exact (Finset.sum_subtype (Finset.univ.filter (fun i : Fin 28 => stdDeg i ≤ N)) (by simp)
        (fun i => invariantEval (qFam p N i) * standardMonomial i)).symm
    rw [hlhs]
    simp
  exact psi_injective_elementary N (fun m => qFam p N m.1) (fun _ => 0)
    (fun m => isWeightedHomogeneous_qFam p N m.1) (fun m => isWeightedHomogeneous_zero _ _ _)
    heq ⟨m₀, hm₀⟩

end TernaryPeriodPolynomials.Argument.CharTwoKernel
