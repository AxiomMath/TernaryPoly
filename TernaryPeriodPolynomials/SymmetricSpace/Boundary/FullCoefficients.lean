module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.OrdinaryBoundaryConeActual
public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Consumer

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory IntegralGL3Congruence OrdinaryBoundaryCommonRoot OrdinaryCovectors
open PolynomialGLAction

/-- Exact restriction of the full 26-covector coefficient representation. -/
abbrev restrictedCoefficients (n : ℕ) (e : ℤ) : Rep ℚ principalSix :=
  Rep.res principalSix.subtype (OrdinaryBoundaryCone.actualCoefficients n e)

/-- Every one of the 26 residue coordinates survives restriction. -/
theorem coefficient_coordinate_count : Fintype.card NonzeroCovector = 26 := card_nonzeroCovector

/-- Principal level six fixes each residue covector individually. -/
theorem rowMove_principalSix (g : principalSix) (r : NonzeroCovector) :
    rowMove g.val r = r := by
  apply Subtype.ext
  change Matrix.vecMul r.val (ModThreeGoodAction.reduction g.val).val = r.val
  have hg : ModThreeGoodAction.reduction g.val = 1 := principalSix_le_three g.property
  rw [hg,Units.val_one,Matrix.vecMul_one]

/-- No coordinate is projected away: the restricted action is pointwise inverse substitution. -/
theorem restrictedCoefficients_apply (n : ℕ) (e : ℤ) (g : principalSix)
    (F : Coefficients n) (r : NonzeroCovector) :
    (restrictedCoefficients n e).ρ g F r = integralAction n e g.val (F r) := by
  change integralAction n e g.val (F (rowMove g.val r)) = _
  rw [rowMove_principalSix]

/-- Every individual coordinate evaluation is equivariant on the actual cover. -/
def coordinateEvaluation (n : ℕ) (e : ℤ) (r : NonzeroCovector) :
    restrictedCoefficients n e ⟶
      Rep.res principalSix.subtype (Rep.of (integralAction n e)) :=
  Rep.ofHom ⟨LinearMap.proj r,by
    intro g
    apply LinearMap.ext
    intro F
    exact restrictedCoefficients_apply n e g F r⟩

@[simp] theorem coordinateEvaluation_apply (n : ℕ) (e : ℤ) (r : NonzeroCovector)
    (F : Coefficients n) : (coordinateEvaluation n e r).hom F = F r := rfl

/-- The two prescribed determinant exponents coincide only after actual principal-six restriction. -/
theorem restricted_twist_value (n : ℕ) (e e' : ℤ) (g : principalSix)
    (F : Coefficients n) (r : NonzeroCovector) :
    (restrictedCoefficients n e).ρ g F r = (restrictedCoefficients n e').ρ g F r := by
  rw [restrictedCoefficients_apply,restrictedCoefficients_apply]
  apply Subtype.ext
  simp only [integralAction_coe,action_apply,
    principalSix_determinantCharacter _ _ g.property,one_smul]

end TernaryPoly.SymmetricSpaceBoundaryFull
