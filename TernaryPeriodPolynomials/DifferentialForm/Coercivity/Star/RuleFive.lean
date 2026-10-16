module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.ZeroFive
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesA
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesB

@[expose] public section



/-! R0, the boundary Hodge-star rule at the Λ¹→Λ⁴→Λ⁵ end, mirroring R1-R4
(`StarRuleOne.lean`..`StarRuleFour.lean`) one step further: `exteriorFour (star1to4 β) =
contractionOne β`. Unlike R1-R4, `exteriorFour`'s defining equation already has every tangent
index as a concrete numeral (no free output index survives at top degree), so this needs no
`fin_cases` case split at all: `β` stays fully general and `simp` collapses each inner
`Fin.sum_univ_five` expansion directly via the `eps5_v_*`/`eps5_eq_zero_*` simp sets. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity
open TernaryPeriodPolynomials.Argument.CoercivityOne

theorem exteriorFour_star1to4 (β : OneCoordinates) :
    exteriorFour (star1to4 β) = contractionOne β := by
  simp [exteriorFour, star1to4, contractionOne, Fin.sum_univ_five,
    Derivation.map_smul]

end TernaryPeriodPolynomials.Argument.Coercivity
