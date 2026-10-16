module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Stabilizers
public import TernaryPeriodPolynomials.GroupCohomology.Relative.ExtObstruction
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeEdgeCohomologyConjugacy
open CategoryTheory CategoryTheory.Limits
open ModThreeGoodAction RelativeOrbitStabilizers RelativeStabilizerConjugacy
open RelativeStabilizerCoordinates

/-- Restrict literal B-conjugation to any of the actual row-e3 stabilizers. -/
def conjugateEquiv (H : Subgroup IntegralGL) (hH : H ≤ K3) : H ≃* conjugateGroup H where
  toFun g := ⟨K3EquivK ⟨g.val,hH g.property⟩,
    (mem_conjugateGroup H ⟨g.val,hH g.property⟩).mpr g.property⟩
  invFun k := ⟨(K3EquivK.symm k.val).val,
    (mem_conjugateGroup H (K3EquivK.symm k.val)).mp (by simpa only [MulEquiv.apply_symm_apply] using k.property)⟩
  left_inv g := by apply Subtype.ext; simp
  right_inv k := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    change B * (g.val*h.val) * B⁻¹ = (B*g.val*B⁻¹) * (B*h.val*B⁻¹)
    simp only [mul_assoc, inv_mul_cancel_left]

@[simp] lemma conjugateEquiv_val (H : Subgroup IntegralGL) (hH : H ≤ K3) (g : H) :
    ((conjugateEquiv H hH g).val).val = B*g.val*B⁻¹ := rfl

/-- The literal coefficient action of the fixed integral change-of-basis matrix. -/
def coefficientChange (n : ℕ) : PolynomialGLAction.HomogeneousPoly n ≃ₗ[ℚ]
    PolynomialGLAction.HomogeneousPoly n :=
  LinearEquiv.ofLinearMap (PolynomialGLAction.integralAction n 0 B)
    (PolynomialGLAction.integralAction n 0 B⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

/-- Group and coefficient conjugacy, with the exact inverse-substitution convention. -/
def cohomologyConjugacy (H : Subgroup IntegralGL) (hH : H ≤ K3) (n j : ℕ) :
    groupCohomology (Rep.of ((PolynomialGLAction.integralAction n 0).comp H.subtype)) j ≅
      groupCohomology (Rep.res (conjugateGroup H).subtype
        (RelativeExtObstruction.coefficientRep n)) j :=
  groupCohomology.mapIso (conjugateEquiv H hH) (coefficientChange n) (fun g => by
    change (PolynomialGLAction.integralAction n 0 B).comp
      (PolynomialGLAction.integralAction n 0 g.val) =
        (PolynomialGLAction.integralAction n 0 (B*g.val*B⁻¹)).comp
          (PolynomialGLAction.integralAction n 0 B)
    simp only [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel_right]) j

/-- The BB vanishing transports into the exact subgroup used by Ext–Shapiro. -/
theorem bb_vanishing_transport (n : ℕ)
    (h : IsZero (groupCohomology (Rep.of ((PolynomialGLAction.integralAction n 0).comp
      RelativeStabilizerConsumer.HBBGroup.subtype)) 1)) :
    IsZero (groupCohomology (Rep.res HBB.subtype (RelativeExtObstruction.coefficientRep n)) 1) :=
  h.of_iso (cohomologyConjugacy RelativeStabilizerConsumer.HBBGroup inf_le_left n 1).symm

/-- The BG transport uses the same literal matrix and coefficient convention. -/
theorem bg_vanishing_transport (n : ℕ)
    (h : IsZero (groupCohomology (Rep.of ((PolynomialGLAction.integralAction n 0).comp
      RelativeStabilizerConsumer.HBGGroup.subtype)) 1)) :
    IsZero (groupCohomology (Rep.res HBG.subtype (RelativeExtObstruction.coefficientRep n)) 1) :=
  h.of_iso (cohomologyConjugacy RelativeStabilizerConsumer.HBGGroup inf_le_left n 1).symm

end TernaryPoly.RelativeEdgeCohomologyConjugacy
