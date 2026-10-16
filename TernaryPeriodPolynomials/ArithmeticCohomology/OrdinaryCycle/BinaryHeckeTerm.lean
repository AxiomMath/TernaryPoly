module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SymbolFactorization
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Plane.EdgeParabolicInverse

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBinaryHecke
open OrdinaryPlaneEdge OrdinaryResidueParabolic OrdinaryResidueSymbol SinglePole SinglePoleCoordinate

/-- Each genuine parabolic conjugation term restricts to the actual binary coefficient-and-symbol term. -/
theorem parabolic_term (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1))
    (g : OrdinaryFullAction.GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : BinaryModularSymbol.GL2)
    (hg : g.val = blockMatrix lam u C) (c : BinaryModularSymbol.St) :
    zeroCoordinate n (OrdinaryHomHecke.linearAction (residueAction n (-1)) g F.val (binaryCone c)) =
      BinaryModularSymbol.homAction (BinaryModularSymbolCoefficients.homogeneousAction (n+1) (-1)) C
        (toBinaryHom n F).val c := by
  change coordinateTuple n (residueAction n (-1) g
    (F.val (OrdinaryFullAction.cycleAction g⁻¹ (binaryCone c)))) 0 = _
  rw [coordinateTuple_action n g lam u C hg,coefficient_action,toBinaryHom_factorization,
    binaryProject_inverse_action_binaryCone g lam u C hg]
  rfl

end TernaryPoly.OrdinaryBinaryHecke
