module

public import TernaryPeriodPolynomials.ModularForm.PeriodHecke.Endpoints
public import TernaryPeriodPolynomials.ModularForm.Symbol.Odd

@[expose] public section


noncomputable section

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod BinaryCuspHeckeEndomorphism BinaryRationalHeckePrime BinaryModularSymbol

/-- Odd projection commutes with actual prime transfer on the genuine holomorphic symbol.
The scalar is exactly the p^(d+1), expressed in its original rational coefficient action. -/
theorem oddHom_hecke {d : ℕ} (f : Forms d) (p : ℕ) [Fact p.Prime] :
    oddHom (T d p f) = (p : ℚ)^(d+1) •
      BinaryRationalHecke.rationalHecke (primeDiagonal p) functionAction (oddHom f) := by
  apply Subtype.ext
  rw [Submodule.coe_smul, rationalHecke_prime_adjugate]
  change (1/2 : ℚ) • (full (T d p f)+homAction functionAction reflection (full (T d p f))) =
    (p : ℚ)^(d+1) • ∑ i : PrimeIndex p, homAction functionAction (adjugateRepresentative p i)
      ((1/2 : ℚ) • (full f+homAction functionAction reflection (full f)))
  rw [full_hecke, map_smul, adjugate_sum_reflection (homAction functionAction) p (full f) (full_fixed_sl f)]
  simp only [map_smul, map_add]
  rw [←Finset.smul_sum, Finset.sum_add_distrib]
  module

end TernaryPoly.BinaryCuspSymbol
