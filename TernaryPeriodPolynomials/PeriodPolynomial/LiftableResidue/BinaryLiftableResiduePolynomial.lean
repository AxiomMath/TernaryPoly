module

public import TernaryPeriodPolynomials.PeriodPolynomial.LiftableResidue.BinaryLiftableResidueDetection
public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Residue

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryLiftableResiduePolynomial
open OrdinaryFullCoefficient BinaryLiftableResidueDetection

/-- Every actual single-pole Hom has zero actual residue Hom under the exact analytic gate. -/
theorem residueHom_eq_zero (n : ℕ) (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn))
    (F : SinglePoleHom n (-1)) : residueHom n (-1) F=0 :=
  liftable_residue_eq_zero n hn h _ ⟨F,rfl⟩

/-- Vanishing of the actual residue Hom means zero actual residue at every actual ordinary cycle. -/
theorem residue_value_eq_zero (n : ℕ) (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn))
    (F : SinglePoleHom n (-1)) (c : OrdinaryIncidenceChains.Cycles) :
    SinglePole.residue n (F.val c)=0 := by
  have he := congrArg (fun G : ResidueHom n (-1) => G.val c) (residueHom_eq_zero n hn h F)
  exact he

/-- The exact residue sequence places every actual cycle value in the homogeneous polynomial range. -/
theorem value_mem_polynomial_range (n : ℕ) (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn))
    (F : SinglePoleHom n (-1)) (c : OrdinaryIncidenceChains.Cycles) :
    F.val c∈(SinglePole.polynomialInclusion n).range := by
  rw [←SinglePole.residue_exact]
  exact residue_value_eq_zero n hn h F c

/-- Every actual cycle value has an actual polynomial witness in its exact homogeneous degree. -/
theorem value_polynomial (n : ℕ) (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn))
    (F : SinglePoleHom n (-1)) (c : OrdinaryIncidenceChains.Cycles) :
    ∃ p : SinglePole.V n,F.val c=SinglePole.polynomialInclusion n p := by
  obtain ⟨p,hp⟩ := value_mem_polynomial_range n hn h F c
  exact ⟨p,hp.symm⟩

/-- In particular the genuine reference coefficient is a literal homogeneous polynomial. -/
theorem reference_polynomial (n : ℕ) (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn))
    (F : SinglePoleHom n (-1)) :
    ∃ p : SinglePole.V n,
      reference (SinglePole.singlePoleAction n (-1)) F=SinglePole.polynomialInclusion n p :=
  value_polynomial n hn h F (OrdinaryApartmentPresentation.frameCycle 1)

/-- Actual full-level single-pole apartment equations force a polynomial coefficient under the
same explicit analytic gate. This does not assume any boundary-support conclusion. -/
theorem relations_polynomial (n : ℕ) (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn))
    (x : SinglePole.singlePole n) (hx : Relations (SinglePole.singlePoleAction n (-1)) x) :
    ∃ p : SinglePole.V n,x=SinglePole.polynomialInclusion n p := by
  obtain ⟨F,hF⟩ := (exists_hom_iff (SinglePole.singlePoleAction n (-1)) x).mpr hx
  obtain ⟨p,hp⟩ := reference_polynomial n hn h F
  exact ⟨p,hF.symm.trans hp⟩

end TernaryPoly.BinaryLiftableResiduePolynomial
