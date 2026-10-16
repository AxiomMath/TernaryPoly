module

public import TernaryPeriodPolynomials.Polynomial.DicksonQuotient
public import TernaryPeriodPolynomials.Polynomial.CharTwo.SymmetricCoordinates

@[expose] public section





open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

/-! Bridge between the abstract Dickson-quotient copy `TernaryPoly.DicksonQuotient.Poly` and the
real elementary-symmetric copy `TernaryPoly.CharTwoNorm.Poly` (definitionally the same type,
`MvPolynomial (Fin 3) (ZMod 2)`), via `TernaryPoly.CharTwoNorm.elementaryEval`. -/

theorem elementaryEval_dickson_a :
    TernaryPoly.CharTwoNorm.elementaryEval TernaryPoly.DicksonQuotient.a =
      TernaryPoly.CharTwoNorm.a := by
  simp [TernaryPoly.DicksonQuotient.a, TernaryPoly.CharTwoNorm.elementaryEval]

theorem elementaryEval_dickson_b :
    TernaryPoly.CharTwoNorm.elementaryEval TernaryPoly.DicksonQuotient.b =
      TernaryPoly.CharTwoNorm.b := by
  simp [TernaryPoly.DicksonQuotient.b, TernaryPoly.CharTwoNorm.elementaryEval]

theorem elementaryEval_dickson_c :
    TernaryPoly.CharTwoNorm.elementaryEval TernaryPoly.DicksonQuotient.c =
      TernaryPoly.CharTwoNorm.c := by
  simp [TernaryPoly.DicksonQuotient.c, TernaryPoly.CharTwoNorm.elementaryEval]

theorem elementaryEval_dickson_d4 :
    TernaryPoly.CharTwoNorm.elementaryEval TernaryPoly.DicksonQuotient.d4 =
      TernaryPoly.CharTwoNorm.d4 := by
  simp [TernaryPoly.DicksonQuotient.d4, TernaryPoly.CharTwoNorm.d4,
    elementaryEval_dickson_a, elementaryEval_dickson_b, elementaryEval_dickson_c]

theorem elementaryEval_dickson_d6 :
    TernaryPoly.CharTwoNorm.elementaryEval TernaryPoly.DicksonQuotient.d6 =
      TernaryPoly.CharTwoNorm.d6 := by
  simp [TernaryPoly.DicksonQuotient.d6, TernaryPoly.CharTwoNorm.d6,
    elementaryEval_dickson_a, elementaryEval_dickson_b, elementaryEval_dickson_c]

theorem elementaryEval_dickson_d7 :
    TernaryPoly.CharTwoNorm.elementaryEval TernaryPoly.DicksonQuotient.d7 =
      TernaryPoly.CharTwoNorm.d7 := by
  simp [TernaryPoly.DicksonQuotient.d7, TernaryPoly.CharTwoNorm.d7, TernaryPoly.CharTwoNorm.cplus,
    elementaryEval_dickson_a, elementaryEval_dickson_b, elementaryEval_dickson_c]

/-- The bridge identity as a composite of algebra homs: evaluating the abstract Dickson
substitution, then passing to real coordinates, agrees with evaluating the real Dickson
substitution directly. -/
theorem elementaryEval_comp_invariantEval :
    TernaryPoly.CharTwoNorm.elementaryEval.comp TernaryPoly.DicksonQuotient.invariantEval =
      TernaryPoly.CharTwoNorm.invariantEval := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [AlgHom.comp_apply, TernaryPoly.DicksonQuotient.invariantEval,
      TernaryPoly.CharTwoNorm.invariantEval, TernaryPoly.CharTwoNorm.invariant,
      elementaryEval_dickson_d4, elementaryEval_dickson_d6, elementaryEval_dickson_d7]

theorem elementaryEval_invariantEval (p : TernaryPoly.DicksonQuotient.Poly) :
    TernaryPoly.CharTwoNorm.elementaryEval (TernaryPoly.DicksonQuotient.invariantEval p) =
      TernaryPoly.CharTwoNorm.invariantEval p :=
  DFunLike.congr_fun elementaryEval_comp_invariantEval p

/-- General transport lemma: pushing an `invariantEval`-weighted sum in the abstract copy
through `elementaryEval` lands exactly on the corresponding real-coefficient sum. -/
theorem elementaryEval_sum_invariantEval_mul {ι : Type*} (s : Finset ι)
    (p g : ι → TernaryPoly.DicksonQuotient.Poly) :
    TernaryPoly.CharTwoNorm.elementaryEval
        (∑ i ∈ s, TernaryPoly.DicksonQuotient.invariantEval (p i) * g i) =
      ∑ i ∈ s, TernaryPoly.CharTwoNorm.invariantEval (p i) *
        TernaryPoly.CharTwoNorm.elementaryEval (g i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_mul, elementaryEval_invariantEval]

end TernaryPeriodPolynomials.Argument.CharTwoKernel
