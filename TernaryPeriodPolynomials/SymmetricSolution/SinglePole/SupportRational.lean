module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Support

@[expose] public section


noncomputable section
namespace TernaryPoly.SinglePoleSupport
open SinglePole PolynomialGLAction OrdinaryResidueSupport ModThreeGoodAction

/-- Integral action on actual single-pole rational functions. -/
def integralSinglePoleAction (n : ℕ) (e : ℤ) : Representation ℚ IntegralGL (singlePole n) :=
  (singlePoleAction n e).comp integralRational

/-- The actual residue intertwiner remains equivariant after restriction to integral matrices. -/
theorem residue_integral_equivariant (n : ℕ) (e : ℤ) (g : IntegralGL) (x : singlePole n) :
    integralResidueAction n e g (residue n x) =
      residue n (integralSinglePoleAction n e g x) :=
  residue_equivariant n e (integralRational g) x

/-- A genuine symmetric separately odd single-pole rational norm cycle has only coordinate residues. -/
theorem singlePole_residue_coordinate_support (n : ℕ) (e : ℤ) (x : singlePole n)
    (hsym : ∀ π, integralSinglePoleAction n e (permutationMatrix π) x =
      determinantCharacter e (integralRational (permutationMatrix π)) • x)
    (hodd : ∀ s, integralSinglePoleAction n e (signMatrix s) x =
      (determinantCharacter e (integralRational (signMatrix s)) * oddSign s) • x)
    (hnorm : x + integralSinglePoleAction n e ReferenceCoefficientMatrices.a x +
      integralSinglePoleAction n e (ReferenceCoefficientMatrices.a^2) x = 0) :
    ∀ H, ¬Coordinate H → residue n x H = 0 := by
  apply residue_coordinate_support n e (residue n x)
  · intro π
    rw [residue_integral_equivariant,hsym,map_smul]
  · intro s
    rw [residue_integral_equivariant,hodd,map_smul]
  · have he := congrArg (residue n) hnorm
    simpa only [map_add,map_zero,← residue_integral_equivariant] using he

/-- Inverse-determinant specialization with literal coordinate-sign invariance. -/
theorem singlePole_residue_coordinate_support_neg_one (n : ℕ) (x : singlePole n)
    (hsym : ∀ π, integralSinglePoleAction n (-1) (permutationMatrix π) x =
      determinantCharacter (-1) (integralRational (permutationMatrix π)) • x)
    (hsign : ∀ s, integralSinglePoleAction n (-1) (signMatrix s) x = x)
    (hnorm : x + integralSinglePoleAction n (-1) ReferenceCoefficientMatrices.a x +
      integralSinglePoleAction n (-1) (ReferenceCoefficientMatrices.a^2) x = 0) :
    ∀ H, ¬Coordinate H → residue n x H = 0 := by
  apply singlePole_residue_coordinate_support n (-1) x hsym _ hnorm
  intro s
  rw [odd_scalar_neg_one,one_smul]
  exact hsign s

end TernaryPoly.SinglePoleSupport
