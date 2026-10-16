module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.ZeroFive
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesA
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesB

@[expose] public section



/-! R5, the boundary Hodge-star rule at the Λ⁰→Λ⁵→Λ⁴ end: `contractionFive q = star1to4
(exteriorZero q)`. Unlike R0 (`StarRuleFive.lean`), the output `FourCoordinates` still carries
four free named indices, so this needs the usual `funext` + `fin_cases` treatment, mirroring
R1-R4's case-split style. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity
open TernaryPeriodPolynomials.Argument.CoercivityOne

/-- Cyclically moving the last argument of `eps5` to the front is an even permutation. -/
theorem eps5_cycle5 (a b c d e : Fin 5) : eps5 e a b c d = eps5 a b c d e := by
  show epsFive ![e, a, b, c, d] = epsFive ![a, b, c, d, e]
  have h : (![e, a, b, c, d] : Fin 5 → Fin 5) = ![a, b, c, d, e] ∘ (finRotate 5).symm := by
    funext w; fin_cases w <;> rfl
  rw [h, epsFive_comp_perm, Equiv.Perm.sign_symm, sign_finRotate]
  norm_num

theorem contractionFive_star1to4 (q : Poly) :
    contractionFive q = star1to4 (exteriorZero q) := by
  funext i j k l
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eps5_cycle5]
  rfl

end TernaryPeriodPolynomials.Argument.Coercivity
