module

public import TernaryPeriodPolynomials.PeriodPolynomial.LiftableResidue.BinaryLiftableResidueDetection
public import TernaryPeriodPolynomials.ModularForm.PeriodHecke.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryLiftableResidueDetection
open BinaryComplexPeriod OrdinaryFullCoefficient

/-- The exact actual intertwining premise is supplied by the proved analytic Hecke comparison. -/
theorem actualIntertwining (d : ℕ) (hd : Even d) :
    BinaryCuspPeriodDetection.ActualIntertwining d hd := by
  intro p f
  let : Fact p.val.Prime := ⟨(Nat.irreducible_iff_nat_prime _).mp p.property⟩
  exact BinaryCuspPeriod.periodMap_hecke hd f p.val

/-- The genuine complex liftable residue span is zero in every odd ternary degree. -/
theorem actualLiftable_complex_zero (n : ℕ) (hn : Odd n) :
    complexSpan (n+1) (actualLiftable n)=⊥ :=
  actualLiftable_complex_eq_bot n hn (actualIntertwining (n+1) (successor_even hn))

/-- The genuine rational liftable residue subspace is zero in every odd ternary degree. -/
theorem actualLiftable_zero (n : ℕ) (hn : Odd n) : actualLiftable n=⊥ :=
  actualLiftable_eq_bot n hn (actualIntertwining (n+1) (successor_even hn))

/-- Every genuine liftable residue Hom vanishes in every odd ternary degree. -/
theorem residue_zero (n : ℕ) (hn : Odd n)
    (F : ResidueHom n (-1)) (hF : F∈liftableResidueHoms n (-1)) : F=0 :=
  liftable_residue_eq_zero n hn (actualIntertwining (n+1) (successor_even hn)) F hF

/-- The actual image of the residue map on full ordinary Hom spaces is zero in odd degree. -/
theorem liftableResidueHoms_zero (n : ℕ) (hn : Odd n) :
    liftableResidueHoms n (-1)=⊥ :=
  liftableResidueHoms_eq_bot n hn (actualIntertwining (n+1) (successor_even hn))

end TernaryPoly.BinaryLiftableResidueDetection
