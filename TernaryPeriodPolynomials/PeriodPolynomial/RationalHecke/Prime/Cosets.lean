module

public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Lifts

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryRationalHeckePrime
open BinaryModularSymbol (GL2)
open Matrix RankTwoAugmentedFrames BinaryRationalHeckeArithmetic OrdinaryHeckeTransfer
open RationalCohomologyDescent

/-- The actual right coset represented by the explicit integral covector lift. -/
def primeCoset (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    RightCosets (intersection Gamma (primeDiagonal p)) :=
  Quotient.mk _ (integralEquiv (chartLift i))

/-- Distinct normalized projective charts give distinct actual transfer cosets. -/
theorem primeCoset_injective (p : ℕ) [Fact p.Prime] : Function.Injective (primeCoset p) := by
  intro i j he
  have hm : integralEquiv (chartLift j*(chartLift i)⁻¹) ∈ intersection Gamma (primeDiagonal p) := by
    rw [map_mul,map_inv]
    exact QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  have hc := (chart_membership_iff p (chartLift j) i).mp hm
  obtain ⟨s,hs,he⟩ := (chartConditions_iff _ (firstRow_ne_zero p (chartLift j)) i).mp hc
  rw [firstRow_chart] at he
  exact (normalCovector_unique j i s hs he).symm

/-- Every actual right coset has a normalized projective-chart representative. -/
theorem primeCoset_surjective (p : ℕ) [Fact p.Prime] : Function.Surjective (primeCoset p) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro k
  let z := integralEquiv.symm k
  obtain ⟨i,s,hs,he⟩ := covector_normalization (firstRow p z) (firstRow_ne_zero p z)
  refine ⟨i,Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)⟩
  have hi : integralEquiv z=k := integralEquiv.apply_symm_apply k
  change k*(integralEquiv (chartLift i))⁻¹ ∈ intersection Gamma (primeDiagonal p)
  rw [←hi,←map_inv,←map_mul]
  apply (chart_membership_iff p z i).mpr
  exact (chartConditions_iff _ (firstRow_ne_zero p z) i).mpr ⟨s,hs,he⟩

/-- A genuine equivalence with the exact right cosets used in the transfer definition. -/
def prime_coset_equiv (p : ℕ) [Fact p.Prime] :
    PrimeIndex p ≃ RightCosets (intersection Gamma (primeDiagonal p)) :=
  Equiv.ofBijective (primeCoset p) ⟨primeCoset_injective p,primeCoset_surjective p⟩

/-- The actual prime double-coset degree, with the transfer's right-coset convention. -/
theorem prime_coset_count (p : ℕ) [Fact p.Prime] :
    Nat.card (RightCosets (intersection Gamma (primeDiagonal p)))=p+1 := by
  rw [←Nat.card_congr (prime_coset_equiv p),Nat.card_eq_fintype_card,primeIndex_card]

end TernaryPoly.BinaryRationalHeckePrime
