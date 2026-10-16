module

public import TernaryPeriodPolynomials.ModularForm.PeriodDetection.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BinaryHeckePeriods
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodRationalComparison

@[expose] public section

noncomputable section
namespace TernaryPoly.BinaryLiftableResidueDetection
open BinaryComplexPeriod OrdinaryFullCoefficient

/-- The two period-coordinate conventions carry exactly the same actual liftable subspace. -/
theorem mem_actualLiftable_iff (n : ℕ) (q : space ℚ (n+1)) :
    q∈actualLiftable n ↔ (rationalEquiv (n+1)).symm q∈OrdinaryResiduePeriod.liftable n := by
  constructor
  · rintro ⟨F,hF,rfl⟩
    refine ⟨F,hF,?_⟩
    change OrdinaryResiduePeriod.periodEquiv n F=
      (rationalEquiv (n+1)).symm (rationalEquiv (n+1) (OrdinaryResiduePeriod.periodEquiv n F))
    exact ((rationalEquiv (n+1)).symm_apply_apply _).symm
  · rintro ⟨F,hF,hFq⟩
    refine ⟨F,hF,?_⟩
    change rationalEquiv (n+1) (OrdinaryResiduePeriod.periodEquiv n F)=q
    change OrdinaryResiduePeriod.periodEquiv n F=(rationalEquiv (n+1)).symm q at hFq
    rw [hFq,LinearEquiv.apply_symm_apply]

/-- The actual rational liftable subspace is stable under the actual binary prime correspondence. -/
theorem actualLiftable_rational_stable (n p : ℕ) [Fact p.Prime]
    (q : space ℚ (n+1)) (hq : q∈actualLiftable n) :
    rationalSymbolHecke (n+1) (BinaryRationalHeckePrime.primeDiagonal p) q∈actualLiftable n := by
  apply (mem_actualLiftable_iff n _).mpr
  change (rationalEquiv (n+1)).symm (rationalEquiv (n+1)
    (BinaryRationalHecke.periodHecke (n+1) (BinaryRationalHeckePrime.primeDiagonal p)
      ((rationalEquiv (n+1)).symm q)))∈OrdinaryResiduePeriod.liftable n
  rw [LinearEquiv.symm_apply_apply]
  exact OrdinaryBinaryHecke.liftable_period_prime_stable n p _ ((mem_actualLiftable_iff n q).mp hq)

/-- The actual scalar-extended span remains stable under every actual prime period Hecke. -/
theorem actualLiftable_complex_stable (n : ℕ) (p : Nat.Primes) :
    ∀ q∈complexSpan (n+1) (actualLiftable n),
      BinaryCuspPeriodDetection.primePeriodHecke (n+1) p q∈complexSpan (n+1) (actualLiftable n) := by
  let : Fact p.val.Prime := ⟨(Nat.irreducible_iff_nat_prime _).mp p.property⟩
  exact complexHecke_span_stable (n+1) (BinaryRationalHeckePrime.primeDiagonal p.val)
    (actualLiftable n) (actualLiftable_rational_stable n p.val)

/-- Odd ternary degree gives the even binary period degree required by the analytic comparison. -/
theorem successor_even {n : ℕ} (hn : Odd n) : Even (n+1) := by
  obtain ⟨k,hk⟩ := hn
  exact ⟨k+1,by omega⟩

/-- The genuine complexified liftable residue space vanishes, with only the exact analytic
intertwining gate retained. Stability and the whole extreme-coefficient zero are actual theorems. -/
theorem actualLiftable_complex_eq_bot (n : ℕ) (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn)) :
    complexSpan (n+1) (actualLiftable n)=⊥ :=
  BinaryCuspPeriodDetection.actual_stable_extreme_kernel_eq_bot (n+1) (successor_even hn) h
    (complexSpan (n+1) (actualLiftable n)) (actualLiftable_complex_stable n)
    (actualLiftable_complex_extreme n)

/-- Faithful scalar extension detects zero for the actual rational liftable residue space. -/
theorem actualLiftable_eq_bot (n : ℕ) (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn)) :
    actualLiftable n=⊥ :=
  (complexSpan_eq_bot_iff (n+1) (actualLiftable n)).mp (actualLiftable_complex_eq_bot n hn h)

/-- Every actual liftable residue Hom is zero under the explicit analytic intertwining premise. -/
theorem liftable_residue_eq_zero (n : ℕ) (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn))
    (F : ResidueHom n (-1)) (hF : F∈liftableResidueHoms n (-1)) : F=0 :=
  liftable_residue_zero_of_complexSpan n (actualLiftable_complex_eq_bot n hn h) F hF

/-- The actual image of the residue map on full-level ordinary Hom spaces is the zero subspace. -/
theorem liftableResidueHoms_eq_bot (n : ℕ) (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn)) :
    liftableResidueHoms n (-1)=⊥ := by
  apply le_antisymm _ bot_le
  intro F hF
  exact (Submodule.mem_bot ℚ).mpr (liftable_residue_eq_zero n hn h F hF)

end TernaryPoly.BinaryLiftableResidueDetection
