module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.FiniteEvaluation
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullOrdinaryPairing
public import TernaryPeriodPolynomials.Polynomial.PolynomialSupport

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory HomologicalComplex SymmetricSpaceBoundaryFull OrdinaryParabolicGroups OrdinaryBoundaryCone
open ReferenceCoefficientMatrices

/-- Pairwise support of the literal distinguished coefficient among all 26 residue covectors. -/
def coefficientPairwise (n : ℕ) (F : OrdinaryBoundaryCommonRoot.Coefficients n) : Prop :=
  Pairwise (OrdinaryBoundaryCommonRoot.evaluation n F : PolynomialGLAction.Poly)

theorem coefficientPairwise_add {n : ℕ} {F H : OrdinaryBoundaryCommonRoot.Coefficients n}
    (hF : coefficientPairwise n F) (hH : coefficientPairwise n H) : coefficientPairwise n (F+H) := by
  unfold coefficientPairwise at *
  rw [map_add]
  exact hF.add hH

theorem coefficientPairwise_neg {n : ℕ} {F : OrdinaryBoundaryCommonRoot.Coefficients n}
    (hF : coefficientPairwise n F) : coefficientPairwise n (-F) := by
  unfold coefficientPairwise at *
  rw [map_neg]
  exact hF.neg

theorem coefficientPairwise_sub {n : ℕ} {F H : OrdinaryBoundaryCommonRoot.Coefficients n}
    (hF : coefficientPairwise n F) (hH : coefficientPairwise n H) : coefficientPairwise n (F-H) := by
  rw [sub_eq_add_neg]
  exact coefficientPairwise_add hF (coefficientPairwise_neg hH)

/-- The actual cyclic coefficient action preserves distinguished pairwise support. -/
theorem coefficientPairwise_c (n : ℕ) (e : ℤ) (F : OrdinaryBoundaryCommonRoot.Coefficients n)
    (hF : coefficientPairwise n F) : coefficientPairwise n ((actualCoefficients n e).ρ c F) := by
  change Pairwise (OrdinaryBoundaryCommonRoot.evaluation n
    (OrdinaryBoundaryCommonRoot.coefficientAction n e c F) : PolynomialGLAction.Poly)
  rw [OrdinaryBoundaryCommonRoot.evaluation_action n e c c_mem_K,
    PolynomialGLAction.integralAction_coe]
  change Pairwise (ReferenceCoefficientMatrices.coefficientAction e c
    (OrdinaryBoundaryCommonRoot.evaluation n F : PolynomialGLAction.Poly))
  rw [coefficientAction_c]
  exact (show Pairwise _ from hF).cyclic

/-- The actual swap action retains its exact determinant scalar and preserves pairwise support. -/
theorem coefficientPairwise_s (n : ℕ) (e : ℤ) (F : OrdinaryBoundaryCommonRoot.Coefficients n)
    (hF : coefficientPairwise n F) : coefficientPairwise n ((actualCoefficients n e).ρ s F) := by
  change Pairwise (OrdinaryBoundaryCommonRoot.evaluation n
    (OrdinaryBoundaryCommonRoot.coefficientAction n e s F) : PolynomialGLAction.Poly)
  rw [OrdinaryBoundaryCommonRoot.evaluation_action n e s s_mem_K,
    PolynomialGLAction.integralAction_coe]
  change Pairwise (ReferenceCoefficientMatrices.coefficientAction e s
    (OrdinaryBoundaryCommonRoot.evaluation n F : PolynomialGLAction.Poly))
  rw [coefficientAction_s]
  exact ((show Pairwise _ from hF).swap).smul _

theorem coefficientPairwise_cinv (n : ℕ) (e : ℤ) (F : OrdinaryBoundaryCommonRoot.Coefficients n)
    (hF : coefficientPairwise n F) : coefficientPairwise n ((actualCoefficients n e).ρ c⁻¹ F) := by
  rw [c_inv_eq_sq, pow_two, map_mul, Module.End.mul_apply]
  exact coefficientPairwise_c n e _ (coefficientPairwise_c n e F hF)

/-- All six corner terms have pairwise distinguished support whenever the identity value does. -/
theorem finiteApartmentCorner_pairwise (n : ℕ) (e : ℤ)
    (b : (inducedBarComplex B).X 0 ⟶ actualCoefficients n e)
    (hb : coefficientPairwise n (b.hom (inducedZero B 1))) :
    coefficientPairwise n (b.hom finiteApartmentCorner) := by
  rw [finiteApartmentCorner_cochain, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hs := coefficientPairwise_s n e _ hb
  exact coefficientPairwise_add
    (coefficientPairwise_add (coefficientPairwise_sub hb hs)
      (coefficientPairwise_sub (coefficientPairwise_c n e _ hb) (coefficientPairwise_c n e _ hs)))
    (coefficientPairwise_sub (coefficientPairwise_cinv n e _ hb) (coefficientPairwise_cinv n e _ hs))

theorem finiteApartmentLine_pairwise (n : ℕ) (e : ℤ)
    (b : (inducedBarComplex Q).X 1 ⟶ actualCoefficients n e)
    (hb : coefficientPairwise n (b.hom (inducedOne Q 1 finiteLineSwap))) :
    coefficientPairwise n (b.hom finiteApartmentLine) := by
  rw [finiteApartmentLine_cochain]
  exact coefficientPairwise_add (coefficientPairwise_add hb (coefficientPairwise_c n e _ hb))
    (coefficientPairwise_cinv n e _ hb)

theorem finiteApartmentPlane_pairwise (n : ℕ) (e : ℤ)
    (b : (inducedBarComplex P).X 1 ⟶ actualCoefficients n e)
    (hb : coefficientPairwise n (b.hom (inducedOne P 1 finitePlaneSwap))) :
    coefficientPairwise n (b.hom finiteApartmentPlane) := by
  rw [finiteApartmentPlane_cochain]
  exact coefficientPairwise_add (coefficientPairwise_add hb (coefficientPairwise_c n e _ hb))
    (coefficientPairwise_cinv n e _ hb)

/-- A normalized actual canonical cochain evaluates the finite apartment with pairwise support. -/
theorem finiteApartmentChain_pairwise (n : ℕ) (e : ℤ)
    (b : canonicalFaceCone.X 1 ⟶ actualCoefficients n e)
    (hp : ∀ g : P, coefficientPairwise n ((ordinaryCoordinates1 (actualCoefficients n e) b).1 g))
    (hq : ∀ g : Q, coefficientPairwise n ((ordinaryCoordinates1 (actualCoefficients n e) b).2.1 g))
    (hb : coefficientPairwise n (ordinaryCoordinates1 (actualCoefficients n e) b).2.2) :
    coefficientPairwise n (b.hom finiteApartmentChain) := by
  rw [ordinaryCoordinates1_apply] at hp hq hb
  have hb' := coefficientPairwise_neg hb
  change coefficientPairwise n (-(-(canonicalCornerCochain (actualCoefficients n e) 0 b).hom
    (inducedZero B 1))) at hb'
  rw [neg_neg] at hb'
  have hp' := hp finitePlaneSwap
  have hq' := hq finiteLineSwap
  change coefficientPairwise n ((canonicalPlaneCochain (actualCoefficients n e) 1 b).hom
    (inducedOne P 1 finitePlaneSwap)) at hp'
  change coefficientPairwise n ((canonicalLineCochain (actualCoefficients n e) 1 b).hom
    (inducedOne Q 1 finiteLineSwap)) at hq'
  rw [finiteApartmentChain_cochain]
  exact coefficientPairwise_neg (coefficientPairwise_sub
    (coefficientPairwise_add (finiteApartmentCorner_pairwise n e _ hb')
      (finiteApartmentLine_pairwise n e _ hq')) (finiteApartmentPlane_pairwise n e _ hp'))

end TernaryPoly.OrdinaryBoundaryActualEvaluation
