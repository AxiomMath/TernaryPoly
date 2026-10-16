module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.Operators
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.SquaredLiftInvariance

@[expose] public section



/-!
# Reducing the `kappa = 1` `delta_p`/`delta_q` cases to the generator level

For `j` with `kappa j = 1`, `oddGenerator j = generator j * d7`. Since `d7` is fixed by
every one of the eighteen `piOperator` substitutions
(`DicksonInvariance18.piSubstitutions_invariant`) and by `sub₁, sub₂` individually
(`TernaryPoly.CharTwoNorm.sub₁_invariant`/`sub₂_invariant`), `d7` factors all the way out of
`delta_p (oddGenerator j)`/`delta_q (oddGenerator j)`, reducing these to
`d7 * delta_p (generator j)`/`d7 * delta_q (generator j)` — a computation at `generator j`'s
(much lower) degree instead of `oddGenerator j`'s.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-- `d7` is fixed by every one of the eighteen `piOperator` substitutions. -/
theorem d7_pi_fixed : ∀ t ∈ piSubstitutions, bind₁ t d7 = d7 := by
  intro t ht
  simpa [invariant] using piSubstitutions_invariant t ht 2

/-- Generic `kappa = 1` reduction, abstracting over the `Ebar1_*`/`Ebar2_*` pair so it covers
both `delta_p` and `delta_q` at once. Purely structural: `E1`, `E2`, `generator j` stay
opaque throughout. -/
theorem delta_generic_kappa_one (E1 E2 : Poly2) {j : Fin 8} (hk : kappa j = 1) :
    piOperator (E1 * sub₁ (oddGenerator j) + E2 * sub₂ (oddGenerator j))
      = d7 * piOperator (E1 * sub₁ (generator j) + E2 * sub₂ (generator j)) := by
  have hsub1 : sub₁ d7 = d7 := by simpa [invariant] using sub₁_invariant 2
  have hsub2 : sub₂ d7 = d7 := by simpa [invariant] using sub₂_invariant 2
  have hog : oddGenerator j = generator j * d7 := by
    show generator j * d7 ^ kappa j = generator j * d7
    rw [hk, pow_one]
  rw [hog, map_mul, map_mul, hsub1, hsub2,
    show E1 * (sub₁ (generator j) * d7) + E2 * (sub₂ (generator j) * d7)
       = d7 * (E1 * sub₁ (generator j) + E2 * sub₂ (generator j)) from by ring]
  exact piOperator_mul_of_fixed d7_pi_fixed

theorem delta_p_oddGenerator_kappa_one {j : Fin 8} (hk : kappa j = 1) :
    delta_p (oddGenerator j) = d7 * delta_p (generator j) :=
  delta_generic_kappa_one Ebar1_D4 Ebar2_D4 hk

theorem delta_q_oddGenerator_kappa_one {j : Fin 8} (hk : kappa j = 1) :
    delta_q (oddGenerator j) = d7 * delta_q (generator j) :=
  delta_generic_kappa_one Ebar1_D6 Ebar2_D6 hk

end TernaryPeriodPolynomials.Argument.ModFourBeta
