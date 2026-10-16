module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.LemmaAPivot
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.ComponentVanishing

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial
open TernaryPoly.DicksonQuotient (Poly a b c d4 d6 d7 invariantEval standardMonomial
  invariantEval_a invariantEval_b invariantEval_c)


/-- **Lemma A, independent-row elimination.** If row `i` owns a slot `m` where its own
`![4,6,7]`-abstract coefficient is nonzero and every other row's coefficient at `m` is zero, the
pivot-extraction fact `qFam_eq_zero` (applied at every truncation degree `genAbsDeg i + d`)
isolates `p i`'s own `d`-th `![4,6,7]`-component and forces it to vanish, for every `d`; hence
`p i = 0` entirely. -/
theorem elim_independent (p : Fin 8 → Poly) (hsum : ∑ i : Fin 8, invariantEval (p i) * genAbs i = 0)
    (i : Fin 8) (m : Fin 28) (hm_le : stdDeg m ≤ genAbsDeg i) (hcoeff_ne : coeffAbs i m ≠ 0)
    (hcoeff_others : ∀ k : Fin 8, k ≠ i → coeffAbs k m = 0) : p i = 0 := by
  apply eq_zero_of_forall_weightedHomogeneousComponent_eq_zero (w := (![4, 6, 7] : Fin 3 → ℕ))
  intro d
  have hle : stdDeg m ≤ genAbsDeg i + d := by omega
  have hz := qFam_eq_zero p hsum (genAbsDeg i + d) m hle
  have hsingle : qFam p (genAbsDeg i + d) m =
      if genAbsDeg i ≤ genAbsDeg i + d then
        weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
          (genAbsDeg i + d - genAbsDeg i) (p i) * coeffAbs i m
      else 0 := by
    unfold qFam
    refine Finset.sum_eq_single i (fun k _ hki => ?_) (fun h => absurd (Finset.mem_univ i) h)
    simp [hcoeff_others k hki]
  rw [hsingle, ite_eq_left (show genAbsDeg i ≤ genAbsDeg i + d by omega),
    show genAbsDeg i + d - genAbsDeg i = d by omega] at hz
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact h0
  · exact absurd h0 hcoeff_ne


/-- **Lemma A, row 3 (dependent elimination).** Row 3's slots `{1, 4, 18}` are each shared with
another row (`1` with row 5, `4` with rows 4 and 6, `18` with row 4 only). Taking the pivot slot
`18`, the only two rows contributing there are 3 and 4; once row 4 is known to vanish entirely
(`hp4`), the slot-18 pivot equation isolates row 3's own component and forces it to vanish too. -/
theorem elim_row3 (p : Fin 8 → Poly) (hsum : ∑ i : Fin 8, invariantEval (p i) * genAbs i = 0)
    (hp4 : p 4 = 0) : p 3 = 0 := by
  apply eq_zero_of_forall_weightedHomogeneousComponent_eq_zero (w := (![4, 6, 7] : Fin 3 → ℕ))
  intro d
  have hle : stdDeg (18 : Fin 28) ≤ genAbsDeg 3 + d := by simp [stdDeg, genAbsDeg]
  have hz := qFam_eq_zero p hsum (genAbsDeg 3 + d) 18 hle
  have hexpand : qFam p (genAbsDeg 3 + d) 18 =
      weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) d (p 3) +
      weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) d (p 4) := by
    show (∑ k : Fin 8, if genAbsDeg k ≤ genAbsDeg 3 + d then
        weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
          (genAbsDeg 3 + d - genAbsDeg k) (p k) * coeffAbs k 18
      else 0) = _
    simp [Fin.sum_univ_succ, coeffAbs, coeffAbs0, coeffAbs1, coeffAbs2,
      coeffAbs3, coeffAbs4, coeffAbs5, coeffAbs6, coeffAbs7, genAbsDeg]
  rw [hexpand, hp4, map_zero, add_zero] at hz
  exact hz


/-- **Lemma A.** The abstract-copy generating family `genAbs` is `invariantEval`-linearly
independent: the only way `∑ i, invariantEval (p i) * genAbs i = 0` is `p ≡ 0`. Seven of the eight
rows (`0,1,2,4,5,6,7`) are eliminated independently via their own unique coefficient-`1` pivot
slot (`9,12,14,20,23,24,26` respectively); row `3` is eliminated last, using row `4`'s now-known
vanishing to cancel their shared slot-`18` cross term. -/
theorem lemma_A (p : Fin 8 → Poly) (hsum : ∑ i : Fin 8, invariantEval (p i) * genAbs i = 0) :
    ∀ i : Fin 8, p i = 0 := by
  have h0 : p 0 = 0 := elim_independent p hsum 0 9
    (by simp [stdDeg, genAbsDeg]) (by simp [coeffAbs, coeffAbs0])
    (by intro k hk; fin_cases k <;>
      simp_all [coeffAbs, coeffAbs0, coeffAbs1, coeffAbs2, coeffAbs3, coeffAbs4, coeffAbs5,
        coeffAbs6, coeffAbs7])
  have h1 : p 1 = 0 := elim_independent p hsum 1 12
    (by simp [stdDeg, genAbsDeg]) (by simp [coeffAbs, coeffAbs1])
    (by intro k hk; fin_cases k <;>
      simp_all [coeffAbs, coeffAbs0, coeffAbs1, coeffAbs2, coeffAbs3, coeffAbs4, coeffAbs5,
        coeffAbs6, coeffAbs7])
  have h2 : p 2 = 0 := elim_independent p hsum 2 14
    (by simp [stdDeg, genAbsDeg]) (by simp [coeffAbs, coeffAbs2])
    (by intro k hk; fin_cases k <;>
      simp_all [coeffAbs, coeffAbs0, coeffAbs1, coeffAbs2, coeffAbs3, coeffAbs4, coeffAbs5,
        coeffAbs6, coeffAbs7])
  have h4 : p 4 = 0 := elim_independent p hsum 4 20
    (by simp [stdDeg, genAbsDeg]) (by simp [coeffAbs, coeffAbs4])
    (by intro k hk; fin_cases k <;>
      simp_all [coeffAbs, coeffAbs0, coeffAbs1, coeffAbs2, coeffAbs3, coeffAbs4, coeffAbs5,
        coeffAbs6, coeffAbs7])
  have h5 : p 5 = 0 := elim_independent p hsum 5 23
    (by simp [stdDeg, genAbsDeg]) (by simp [coeffAbs, coeffAbs5])
    (by intro k hk; fin_cases k <;>
      simp_all [coeffAbs, coeffAbs0, coeffAbs1, coeffAbs2, coeffAbs3, coeffAbs4, coeffAbs5,
        coeffAbs6, coeffAbs7])
  have h6 : p 6 = 0 := elim_independent p hsum 6 24
    (by simp [stdDeg, genAbsDeg]) (by simp [coeffAbs, coeffAbs6])
    (by intro k hk; fin_cases k <;>
      simp_all [coeffAbs, coeffAbs0, coeffAbs1, coeffAbs2, coeffAbs3, coeffAbs4, coeffAbs5,
        coeffAbs6, coeffAbs7])
  have h7 : p 7 = 0 := elim_independent p hsum 7 26
    (by simp [stdDeg, genAbsDeg]) (by simp [coeffAbs, coeffAbs7])
    (by intro k hk; fin_cases k <;>
      simp_all [coeffAbs, coeffAbs0, coeffAbs1, coeffAbs2, coeffAbs3, coeffAbs4, coeffAbs5,
        coeffAbs6, coeffAbs7])
  have h3 : p 3 = 0 := elim_row3 p hsum h4
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

end TernaryPeriodPolynomials.Argument.CharTwoKernel
