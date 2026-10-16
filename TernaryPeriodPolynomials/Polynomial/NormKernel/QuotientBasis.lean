module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.LemmaAPivot
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.ComponentVanishing

@[expose] public section


/-!
# Appendix D: the 28 standard monomials are a basis of `S/I`

In `S = 𝔽₂[a, b, c]` with `I = (d₄, d₆, d₇)`, the residue classes of the 28 standard monomials form an
`𝔽₂`-basis of `S/I` (`quotientBasis`, `ar`/`mf:app:kernel`, "a basis of `S/I` consists of the residue
classes of the 28 standard monomials"). The proof uses the free-module decomposition
`S = ⊕ R·m` over `R = 𝔽₂[d₄, d₆, d₇]` (`CharTwoKernel.psi_injective`, `exists_standard_expansion`):
the expansion is unique (`standard_expansion_unique`), and modulo `I` each coefficient reduces to its
constant term.

Written by Claude Opus 5.5.
-/


noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixD

open MvPolynomial
open TernaryPoly.DicksonQuotient (Poly a b c d4 d6 d7 invariantEval standardMonomial dicksonIdeal
  invariantEval_a invariantEval_b invariantEval_c exists_standard_expansion)
open TernaryPeriodPolynomials.Argument.CharTwoKernel

theorem component_invariantEval_mul_std (i : Fin 28) (q : Poly) (N : ℕ) :
    weightedHomogeneousComponent stdWeight N (invariantEval q * standardMonomial i) =
      if stdDeg i ≤ N then
        invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (N - stdDeg i) q) *
          standardMonomial i
      else 0 := by
  split_ifs with h
  · have e1 := weightedHomogeneousComponent_mul_of_homog (isWeightedHomogeneous_standardMonomial i)
      (invariantEval q) (N - stdDeg i)
    rw [Nat.sub_add_cancel h] at e1
    rw [e1, show invariantEval = aeval (R := ZMod 2) ![d4, d6, d7] from rfl,
      weightedHomogeneousComponent_aeval hhom_467]
  · exact weightedHomogeneousComponent_mul_eq_zero_of_lt
      (isWeightedHomogeneous_standardMonomial i) _ (by omega)

/-- **Uniqueness of the standard expansion** over `R = 𝔽₂[d₄, d₆, d₇]`, in every degree. -/
theorem standard_expansion_unique (p : Fin 28 → Poly)
    (h : ∑ i, invariantEval (p i) * standardMonomial i = 0) : ∀ i, p i = 0 := by
  intro i
  apply eq_zero_of_forall_weightedHomogeneousComponent_eq_zero (w := (![4, 6, 7] : Fin 3 → ℕ))
  intro d
  have hc := congrArg (weightedHomogeneousComponent stdWeight (d + stdDeg i)) h
  rw [map_sum, map_zero] at hc
  simp only [component_invariantEval_mul_std] at hc
  rw [← Finset.sum_filter] at hc
  rw [Finset.sum_subtype (Finset.univ.filter fun j => stdDeg j ≤ d + stdDeg i)
    (p := fun j => stdDeg j ≤ d + stdDeg i) (by simp)] at hc
  have key := psi_injective_elementary (d + stdDeg i)
    (fun m => weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (d + stdDeg i - stdDeg m.1)
      (p m.1)) (fun _ => 0)
    (fun m => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    (fun _ => isWeightedHomogeneous_zero _ _ _) (by simpa using hc) ⟨i, by omega⟩
  simpa using key

/-- `invariantEval p ≡ p(0)` modulo `I`. -/
theorem invariantEval_sub_C_mem (p : Poly) :
    invariantEval p - C (constantCoeff p) ∈ dicksonIdeal := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    have := dicksonIdeal.add_mem hp hq
    rw [map_add, map_add, map_add]
    convert this using 1
    ring
  | mul_X p i hp =>
    rw [map_mul, map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero]
    apply dicksonIdeal.mul_mem_left
    fin_cases i
    · exact Ideal.subset_span (by simp [invariantEval_a.symm, TernaryPoly.DicksonQuotient.a])
    · exact Ideal.subset_span (by simp [invariantEval_b.symm, TernaryPoly.DicksonQuotient.b])
    · exact Ideal.subset_span (by simp [invariantEval_c.symm, TernaryPoly.DicksonQuotient.c])

theorem mem_dicksonIdeal_iff (x : Poly) :
    x ∈ dicksonIdeal ↔ ∃ s4 s6 s7 : Poly, x = s4 * d4 + s6 * d6 + s7 * d7 := by
  unfold TernaryPoly.DicksonQuotient.dicksonIdeal
  constructor
  · intro hx
    obtain ⟨s4, z, hz, rfl⟩ := Ideal.mem_span_insert.mp hx
    obtain ⟨s6, z', hz', rfl⟩ := Ideal.mem_span_insert.mp hz
    obtain ⟨s7, rfl⟩ := Ideal.mem_span_singleton'.mp hz'
    exact ⟨s4, s6, s7, by ring⟩
  · rintro ⟨s4, s6, s7, rfl⟩
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

private theorem smul_mk (r : ZMod 2) (x : Poly) :
    r • Ideal.Quotient.mk dicksonIdeal x = Ideal.Quotient.mk dicksonIdeal (C r * x) := by
  rw [← smul_eq_C_mul]
  exact (map_smul (Ideal.Quotient.mkₐ (ZMod 2) dicksonIdeal) r x).symm

/-- A combination of standard monomials with constant coefficients lying in `I` is zero. -/
theorem std_coeff_eq_zero_of_mem (g : Fin 28 → ZMod 2)
    (hg : ∑ i, C (g i) * standardMonomial i ∈ dicksonIdeal) : ∀ i, g i = 0 := by
  obtain ⟨s4, s6, s7, hs⟩ := (mem_dicksonIdeal_iff _).mp hg
  obtain ⟨e4, he4⟩ := exists_standard_expansion s4
  obtain ⟨e6, he6⟩ := exists_standard_expansion s6
  obtain ⟨e7, he7⟩ := exists_standard_expansion s7
  have hX0 : invariantEval (X 0) = d4 := invariantEval_a
  have hX1 : invariantEval (X 1) = d6 := invariantEval_b
  have hX2 : invariantEval (X 2) = d7 := invariantEval_c
  have hzero : ∑ i, invariantEval (C (g i) - (X 0 * e4 i + X 1 * e6 i + X 2 * e7 i)) *
      standardMonomial i = 0 := by
    have hsplit : ∑ i, invariantEval (C (g i) - (X 0 * e4 i + X 1 * e6 i + X 2 * e7 i)) *
        standardMonomial i = ∑ i, C (g i) * standardMonomial i -
          (d4 * ∑ i, invariantEval (e4 i) * standardMonomial i +
            d6 * ∑ i, invariantEval (e6 i) * standardMonomial i +
            d7 * ∑ i, invariantEval (e7 i) * standardMonomial i) := by
      simp only [map_sub, map_add, map_mul, hX0, hX1, hX2, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
        Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsplit, ← he4, ← he6, ← he7, hs]
    ring
  intro i
  have h := standard_expansion_unique _ hzero i
  have hcc := congrArg constantCoeff (sub_eq_zero.mp h)
  simpa using hcc

theorem std_linearIndependent :
    LinearIndependent (ZMod 2)
      (fun i => Ideal.Quotient.mk dicksonIdeal (standardMonomial i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  apply std_coeff_eq_zero_of_mem g
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
  rw [← hg]
  exact Finset.sum_congr rfl fun i _ => (smul_mk (g i) _).symm

theorem std_span :
    ⊤ ≤ Submodule.span (ZMod 2)
      (Set.range fun i => Ideal.Quotient.mk dicksonIdeal (standardMonomial i)) := by
  rintro x -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨p, hp⟩ := exists_standard_expansion f
  have hdiff : f - ∑ i, C (constantCoeff (p i)) * standardMonomial i ∈ dicksonIdeal := by
    rw [hp, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [← sub_mul]
    exact Ideal.mul_mem_right _ _ (invariantEval_sub_C_mem (p i))
  have hmk : Ideal.Quotient.mk dicksonIdeal f =
      ∑ i, constantCoeff (p i) • Ideal.Quotient.mk dicksonIdeal (standardMonomial i) := by
    rw [← sub_eq_zero, ← Finset.sum_congr rfl fun i _ => (smul_mk _ _).symm, ← map_sum,
      ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hdiff
  rw [hmk]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Appendix D: a basis of `S/I`.** The residue classes of the 28 standard monomials. -/
def quotientBasis : Module.Basis (Fin 28) (ZMod 2) (Poly ⧸ dicksonIdeal) :=
  Module.Basis.mk std_linearIndependent std_span

theorem quotientBasis_apply (i : Fin 28) :
    quotientBasis i = Ideal.Quotient.mk dicksonIdeal (standardMonomial i) := by
  simp [quotientBasis]

theorem finrank_quotient : Module.finrank (ZMod 2) (Poly ⧸ dicksonIdeal) = 28 := by
  rw [Module.finrank_eq_card_basis quotientBasis, Fintype.card_fin]

end TernaryPeriodPolynomials.Argument.AppendixD
