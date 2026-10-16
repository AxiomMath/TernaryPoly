module

public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Equiv
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Double

@[expose] public section

noncomputable section
namespace TernaryPoly.BinaryRationalHecke
open BinaryModularSymbol

/-- Hecke action on literal homogeneous periods, transported from the actual symbol correspondence. -/
def periodHecke (d : ℕ) (g : GL2) : Module.End ℚ (OrdinaryResiduePeriod.periodSpace d) :=
  (periodEquiv d).toLinearMap.comp
    ((rationalHecke g (BinaryModularSymbolCoefficients.homogeneousAction d (-1))).comp
      (periodEquiv d).symm.toLinearMap)

/-- Literal reference evaluation intertwines actual modular-symbol Hecke and period Hecke. -/
theorem periodHecke_evaluation (d : ℕ) (g : GL2) (f : PeriodHom d) :
    periodHecke d g (periodEquiv d f) =
      periodEquiv d (rationalHecke g (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) f) := by
  change periodEquiv d (rationalHecke g _ ((periodEquiv d).symm (periodEquiv d f))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The exact prime period formula retains the actual inverse action on its symbol endpoints. -/
theorem periodHecke_prime (d p : ℕ) [Fact p.Prime] (q : OrdinaryResiduePeriod.periodSpace d) :
    (periodHecke d (BinaryRationalHeckePrime.primeDiagonal p) q).val =
      ∑ i : BinaryRationalHeckePrime.PrimeIndex p,
        BinaryModularSymbolCoefficients.homogeneousAction d (-1)
          (BinaryRationalHeckePrime.primeRepresentative p i)
          (((periodEquiv d).symm q).val
            (action (BinaryRationalHeckePrime.primeRepresentative p i)⁻¹ reference)) := by
  change (rationalHecke (BinaryRationalHeckePrime.primeDiagonal p)
    (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) ((periodEquiv d).symm q)).val reference = _
  have he := congrArg (fun h : St →ₗ[ℚ] BinaryModularSymbolCoefficients.HomogeneousPoly d => h reference)
    (BinaryRationalHeckePrime.rationalHecke_prime p
      (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) ((periodEquiv d).symm q))
  simpa only [LinearMap.sum_apply,homAction_apply] using he

end TernaryPoly.BinaryRationalHecke
