module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.CoefficientParity
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.CanonicalOdd

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryFullCoefficient
open SinglePoleSupport OrdinaryResiduePolynomial OrdinaryResidueGeneral

/-- Every actual full-level single-pole apartment coefficient has zero extreme binary residues.
The full symmetry hypotheses are derived from the exact ordinary cycle relations. -/
theorem relations_extreme (n : ℕ) (x : SinglePole.singlePole n)
    (hx : Relations (SinglePole.singlePoleAction n (-1)) x) :
    ∃ q : SinglePoleCoordinate.BinaryV (n+1), ∃ p : SinglePole.V n,
      SymmetricBinaryPeriodRelations q.val ∧
      x.val=representative q.val (X 0) (X 1) (X 2)+embed p.val ∧
      bind₁ ![-X 0,X 1,X 2] p.val= -p.val ∧
      ∀ m : Fin 1 →₀ ℕ,q.val.coeff (Finsupp.cons 1 m)=0 := by
  apply exists_period_lift_extreme n (-1) x
  · exact symmetry_of_relations _ x hx
  · intro s
    rw [odd_scalar_neg_one,one_smul]
    exact sign_invariant_of_relations _ x hx s
  · exact hx.norm

/-- In particular the reference coefficient of every genuine full-level ordinary functional
in the actual single-pole module has the proved extreme-coefficient obstruction. -/
theorem hom_reference_extreme (n : ℕ) (Φ : SinglePoleHom n (-1)) :
    ∃ q : SinglePoleCoordinate.BinaryV (n+1), ∃ p : SinglePole.V n,
      SymmetricBinaryPeriodRelations q.val ∧
      (reference (SinglePole.singlePoleAction n (-1)) Φ).val=
        representative q.val (X 0) (X 1) (X 2)+embed p.val ∧
      bind₁ ![-X 0,X 1,X 2] p.val= -p.val ∧
      ∀ m : Fin 1 →₀ ℕ,q.val.coeff (Finsupp.cons 1 m)=0 :=
  relations_extreme n _ (hom_relations _ Φ)

end TernaryPoly.OrdinaryFullCoefficient
