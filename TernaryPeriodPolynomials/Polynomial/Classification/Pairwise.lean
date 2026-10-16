module

public import TernaryPeriodPolynomials.Polynomial.Classification.Rational
public import TernaryPeriodPolynomials.Polynomial.CoefficientBaseChange
public import TernaryPeriodPolynomials.Polynomial.Support

@[expose] public section



/-!
# Pairwise decomposition of solutions over `ℚ`-algebras

Every solution of the cyclic and three-term relations over a commutative `ℚ`-algebra has no
monomial involving all three variables (`solution_pairwise`). Over `ℚ` this is
`rational_pairwise`; the general case follows by base change of the coefficients.
-/

open MvPolynomial TensorProduct

namespace TernaryPeriodPolynomials.Argument.Classification

/-- `TernaryPoly.Paper.Solution` and `TernaryPoly.PeriodRelations` are the same raw
conjunction at `R = ℚ` (both unfold, by `Iff.rfl`, to the identical cyclic/norm equations). -/
theorem solution_iff_periodRelations (f : TernaryPoly.TernaryPolynomial) :
    TernaryPoly.Paper.Solution f ↔ TernaryPoly.PeriodRelations f := Iff.rfl

/-- `TernaryPoly.Paper.Pairwise` and `TernaryPoly.Pairwise` are the same raw formula at
`R = ℚ`. -/
theorem pairwise_iff_original_pairwise (f : TernaryPoly.TernaryPolynomial) :
    TernaryPoly.Paper.Pairwise f ↔ TernaryPoly.Pairwise f := Iff.rfl

/-- The `ℚ`-level new-route pairwise decomposition, restated for
`TernaryPoly.Paper.Solution`/`Pairwise`: replaces
`TernaryPoly.Paper.OriginalSupportBridge.rational_solution_pairwise`. -/
theorem rational_solution_pairwise (f : TernaryPoly.TernaryPolynomial)
    (hf : TernaryPoly.Paper.Solution f) : TernaryPoly.Paper.Pairwise f :=
  (pairwise_iff_original_pairwise f).mpr
    (rational_pairwise ((solution_iff_periodRelations f).mp hf))

/-- Fully mixed support is excluded over every commutative `ℚ`-algebra. -/
theorem solution_pairwise {R : Type*} [CommRing R] [Algebra ℚ R]
    (f : TernaryPoly.Paper.Ternary R) (hf : TernaryPoly.Paper.Solution f) :
    TernaryPoly.Paper.Pairwise f := by
  obtain ⟨t, ht⟩ := (TernaryPoly.Paper.solutions_baseChangeEquiv R).surjective ⟨f, hf⟩
  have h : ∀ t : R ⊗[ℚ] TernaryPoly.Paper.solutions ℚ,
      TernaryPoly.Paper.Pairwise
        (TernaryPoly.Paper.solutions_baseChangeEquiv R t).val := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a g =>
      rw [TernaryPoly.Paper.solutions_baseChangeEquiv_tmul]
      exact ((rational_solution_pairwise g.val g.property).map (algebraMap ℚ R)).smul a
    | add a b ha hb =>
      simpa only [map_add, AddMemClass.coe_add] using ha.add hb
  simpa only [ht] using h t

end TernaryPeriodPolynomials.Argument.Classification
