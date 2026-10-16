module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Rational

@[expose] public section


/-! The actual nested principal-six deck group and principalSix are explicitly isomorphic. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open IntegralGL3Congruence SymmetricSpaceCovering SymmetricSpacePositive

/-- The inverse inserts the proved membership in the subgroup K. -/
def principalDeck : principalSix →* DeckGroup where
  toFun g := ⟨⟨g.val, principalSix_le_K g.property⟩, g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def deckPrincipalEquiv : DeckGroup ≃* principalSix where
  toFun := deckPrincipal
  invFun := principalDeck
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' := map_mul deckPrincipal

@[simp] theorem deckPrincipalEquiv_toMonoidHom :
    deckPrincipalEquiv.toMonoidHom = deckPrincipal := rfl

@[simp] theorem deckPrincipal_smul (g : DeckGroup) (x : Space) :
    deckPrincipal g • x = g • x := rfl

end TernaryPoly.PolynomialCoefficientMetric
