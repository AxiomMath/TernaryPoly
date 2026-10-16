module

public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Representatives
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Cosets
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.CosetsTransfer

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryRationalHeckePrime
open CategoryTheory BinaryRationalHeckeArithmetic OrdinaryHeckeTransfer
open BinaryModularSymbol (GL2 St Hom symbol lineAction homAction)
open RationalCohomologyDescent
open OrdinaryHeckeCosets (rightCoset_summand_eq)

instance primeIntersection_finiteIndex (p : ℕ) [Fact p.Prime] :
    (intersection Gamma (primeDiagonal p)).FiniteIndex := intersection_finiteIndex _

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The generic left-coefficient Hecke operator has this literal lower-triangular sum.
This is only the exact transfer convention; no right-homology or binary-Hecke normalization is asserted. -/
theorem hecke_prime_apply (p : ℕ) [Fact p.Prime] (A : Rep ℚ GL2)
    (v : (Rep.res Gamma.subtype A).ρ.invariants) :
    (hecke Gamma (primeDiagonal p) A v).val=
      ∑ i : PrimeIndex p, A.ρ (primeRepresentative p i) v.val := by
  rw [hecke_apply,←(prime_coset_equiv p).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  have hq : (Quotient.mk (QuotientGroup.rightRel (intersection Gamma (primeDiagonal p)))
      (primeCoset p i).out)=Quotient.mk _ (integralEquiv (chartLift i)) := Quotient.out_eq _
  have he := rightCoset_summand_eq Gamma (primeDiagonal p) A v
    (primeCoset p i).out (integralEquiv (chartLift i)) hq
  change A.ρ ((primeCoset p i).out.val⁻¹*primeDiagonal p) v.val=_
  rw [he,inverse_coset_normalization,map_mul,Module.End.mul_apply]
  have hv := (Representation.mem_invariants _ _).mp v.property
    ((integralEquiv (chartPermutation i))⁻¹)
  exact congrArg (A.ρ (primeRepresentative p i)) hv

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- The actual binary Hom Hecke operator is exactly the p+1 lower-triangular terms. -/
theorem rationalHecke_prime (p : ℕ) [Fact p.Prime] (ρ : Representation ℚ GL2 E) (f : Hom ρ) :
    (BinaryRationalHecke.rationalHecke (primeDiagonal p) ρ f).val =
      ∑ i : PrimeIndex p, homAction ρ (primeRepresentative p i) f.val := by
  exact hecke_prime_apply p (Rep.of (homAction ρ)) (BinaryRationalHecke.homEquiv ρ f)

/-- Every summand acts both on the actual coefficients and on both rational endpoints. -/
theorem rationalHecke_prime_symbol (p : ℕ) [Fact p.Prime] (ρ : Representation ℚ GL2 E)
    (f : Hom ρ) (L M : BinaryModularSymbol.Line) :
    (BinaryRationalHecke.rationalHecke (primeDiagonal p) ρ f).val (symbol L M) =
      ∑ i : PrimeIndex p, ρ (primeRepresentative p i)
        (f.val (symbol (lineAction (primeRepresentative p i)⁻¹ L)
          (lineAction (primeRepresentative p i)⁻¹ M))) := by
  have he := congrArg (fun h : St →ₗ[ℚ] E => h (symbol L M)) (rationalHecke_prime p ρ f)
  simpa only [LinearMap.sum_apply,BinaryModularSymbol.homAction_apply,
    BinaryModularSymbol.action_symbol] using he

end TernaryPoly.BinaryRationalHeckePrime
