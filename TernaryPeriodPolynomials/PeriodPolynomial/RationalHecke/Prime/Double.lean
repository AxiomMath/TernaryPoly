module

public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Formula

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryRationalHeckePrime
open BinaryModularSymbol (GL2)
open BinaryRationalHeckeArithmetic OrdinaryHeckeTransfer
open OrdinaryHeckeCosets (rightCoset_eq_iff_factor)
open RationalCohomologyDescent

/-- Two of the literal lower triangular representatives cannot differ by a right integral unit. -/
theorem primeRepresentative_disjoint (p : ℕ) [Fact p.Prime] (i j : PrimeIndex p) (c : Gamma)
    (hc : primeRepresentative p i=primeRepresentative p j*c.val) : i=j := by
  have he : (integralEquiv (chartLift i)).val⁻¹*primeDiagonal p=
      (integralEquiv (chartLift j)).val⁻¹*primeDiagonal p*
        ((integralEquiv (chartPermutation j))*c*(integralEquiv (chartPermutation i))⁻¹).val := by
    calc
      _ = primeRepresentative p i*(integral (chartPermutation i))⁻¹ := inverse_coset_normalization p i
      _ = (primeRepresentative p j*c.val)*(integral (chartPermutation i))⁻¹ := by rw [hc]
      _ = _ := by
        change ((integral (chartLift j))⁻¹*primeDiagonal p*integral (chartPermutation j)*c.val)*
            (integral (chartPermutation i))⁻¹=
          (integral (chartLift j))⁻¹*primeDiagonal p*
            (integral (chartPermutation j)*c.val*(integral (chartPermutation i))⁻¹)
        group
  apply primeCoset_injective p
  exact (rightCoset_eq_iff_factor Gamma (primeDiagonal p) _ _).mpr ⟨_,he⟩

/-- Every element of the actual Gamma–prime–Gamma double coset belongs to exactly one of the displayed right cosets. -/
theorem primeRepresentative_complete (p : ℕ) [Fact p.Prime] (a b : Gamma) :
    ∃! i : PrimeIndex p, ∃ d : Gamma, a.val*primeDiagonal p*b.val=primeRepresentative p i*d.val := by
  obtain ⟨i,hi⟩ := primeCoset_surjective p
    (Quotient.mk (QuotientGroup.rightRel (intersection Gamma (primeDiagonal p))) a⁻¹)
  obtain ⟨c,hc⟩ := (rightCoset_eq_iff_factor Gamma (primeDiagonal p)
    a⁻¹ (integralEquiv (chartLift i))).mp hi.symm
  refine ⟨i,⟨(integralEquiv (chartPermutation i))⁻¹*c*b,?_⟩,?_⟩
  · change a.val*primeDiagonal p*b.val=
      primeRepresentative p i*((integral (chartPermutation i))⁻¹*c.val*b.val)
    change a.val*primeDiagonal p=(integralEquiv (chartLift i)).val⁻¹*primeDiagonal p*c.val at hc
    rw [hc,inverse_coset_normalization]
    group
  · intro j hj
    obtain ⟨d,hd⟩ := hj
    have hx : a.val*primeDiagonal p*b.val=
        primeRepresentative p i*((integralEquiv (chartPermutation i))⁻¹*c*b).val := by
      change a.val*primeDiagonal p*b.val=
        primeRepresentative p i*((integral (chartPermutation i))⁻¹*c.val*b.val)
      change a.val*primeDiagonal p=(integralEquiv (chartLift i)).val⁻¹*primeDiagonal p*c.val at hc
      rw [hc,inverse_coset_normalization]
      group
    apply primeRepresentative_disjoint p j i
      (((integralEquiv (chartPermutation i))⁻¹*c*b)*d⁻¹)
    have he := hd.symm.trans hx
    have hz := congrArg (fun x : GL2 => x*d.val⁻¹) he
    simpa only [mul_assoc,mul_inv_cancel,mul_one,Subgroup.coe_mul,Subgroup.coe_inv] using hz

end TernaryPoly.BinaryRationalHeckePrime
