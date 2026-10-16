module

public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Period

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryModularSymbol

/-- Separate oddness annihilates every homogeneous degree-zero period. -/
theorem periodSpace_zero_eq (q : OrdinaryResiduePeriod.periodSpace 0) : q = 0 := by
  have hC : q.val.val = MvPolynomial.C (q.val.val.coeff 0) :=
    (homogeneousComponent_eq_self q.val.property).symm.trans (homogeneousComponent_zero _)
  have hn : bind₁ ![-X 0,X 1] q.val.val = -q.val.val := q.property.odd_first
  rw [hC] at hn
  simp only [bind₁_C_right] at hn
  apply Subtype.ext
  apply Subtype.ext
  rw [hC]
  exact CharZero.eq_neg_self_iff.mp hn

/-- Every degree-zero modular-symbol functional is zero. -/
theorem periodHom_zero_eq (f : PeriodHom 0) : f = 0 := by
  apply periodEvaluation_injective 0
  rw [map_zero]
  exact periodSpace_zero_eq _

end TernaryPoly.BinaryModularSymbol
