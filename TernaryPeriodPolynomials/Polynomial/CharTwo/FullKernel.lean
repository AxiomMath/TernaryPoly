module

public import TernaryPeriodPolynomials.Polynomial.DicksonQuotient
public import TernaryPeriodPolynomials.Polynomial.CharTwo.KernelSpan

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoNorm

/-- The formal Dickson coordinates evaluate to the actual invariant polynomials. -/
theorem elementaryEval_dicksonInvariant (i : Fin 3) :
    elementaryEval (![DicksonQuotient.d4,DicksonQuotient.d6,DicksonQuotient.d7] i) = invariant i := by
  fin_cases i <;>
    simp [elementaryEval, DicksonQuotient.d4, DicksonQuotient.d6, DicksonQuotient.d7,
      DicksonQuotient.a, DicksonQuotient.b, DicksonQuotient.c, invariant, d4, d6, d7, cplus]

/-- Every formal polynomial in the Dickson coordinates maps to the same invariant expression. -/
theorem elementaryEval_dicksonEval (p : Poly) :
    elementaryEval (DicksonQuotient.invariantEval p) = invariantEval p := by
  have h : elementaryEval.comp DicksonQuotient.invariantEval = invariantEval := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, DicksonQuotient.invariantEval, bind₁_X_right,
      invariantEval] using elementaryEval_dicksonInvariant i
  exact DFunLike.congr_fun h p

/-- The formal 28-standard-monomial table is precisely the computed projector-image table. -/
theorem elementaryEval_standardMonomial (i : Fin 28) :
    elementaryEval (DicksonQuotient.standardMonomial i) = CharTwoProjectorImages.standardMonomial i := by
  fin_cases i <;>
    simp [elementaryEval, DicksonQuotient.standardMonomial, CharTwoProjectorImages.standardMonomial,
      DicksonQuotient.a, DicksonQuotient.b, DicksonQuotient.c]

/-- Every symmetric polynomial has a complete standard expansion in every degree. -/
theorem symmetric_standard_expansion {f : Poly} (hs : CharTwoProjector.Symmetric f) :
    ∃ q : Fin 28 → Poly,
      f = ∑ i, invariantEval (q i)*CharTwoProjectorImages.standardMonomial i := by
  obtain ⟨p,hp⟩ := exists_elementaryEval hs
  obtain ⟨q,hq⟩ := DicksonQuotient.exists_standard_expansion p
  refine ⟨q,?_⟩
  rw [← hp,hq,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul,elementaryEval_dicksonEval,elementaryEval_standardMonomial]

/-- The entire symmetric norm kernel is contained in the eight-generator polynomial span. -/
theorem norm_kernel_mem_generatorSpan {f : Poly} (hs : CharTwoProjector.Symmetric f)
    (hn : norm f = 0) : f ∈ generatorSpan := by
  obtain ⟨q,hq⟩ := symmetric_standard_expansion hs
  exact norm_kernel_mem_of_standard_expansion hs hn q hq

/-- Complete eight-generator polynomial spanning of the symmetric norm kernel. -/
theorem norm_kernel_iff_expansion {f : Poly} (hs : CharTwoProjector.Symmetric f) :
    norm f = 0 ↔ ∃ q : Fin 8 → Poly, f = ∑ i, invariantEval (q i)*generator i := by
  constructor
  · intro hn
    exact (mem_generatorSpan_iff f).mp (norm_kernel_mem_generatorSpan hs hn)
  · rintro ⟨q,rfl⟩
    exact norm_sum_invariantEval_mul_generator q

end TernaryPoly.CharTwoNorm
