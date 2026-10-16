module

public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.CoordinatesAction
public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.CoordinatesBlocks
public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.CoordinatesScale

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpaceParabolicCoordinates
open SymmetricSpacePositive

/-- The binary shape removes every nonzero real scalar, retaining scale separately. -/
theorem binaryNormalize_smul (r : ℝ) (hr : r≠0) (B : Mat2) :
    binaryNormalize (r • B)=binaryNormalize B := by
  rw [binaryNormalize,trace_smul,smul_smul,binaryNormalize,smul_eq_mul,_root_.mul_inv_rev]
  congr 1
  rw [mul_assoc,inv_mul_cancel₀ hr,mul_one]

/-- All three actual horospherical factors transform by their literal block-parabolic formulas.
The binary shape depends only on binary congruence; the complementary real sign occurs in v,
while the positive trace scale is multiplied by d⁻². -/
theorem fullHorospherical_action_coordinates (A : RealGL2) (u : Vec2) (d : ℝ) (hd : d≠0)
    (S : Space) :
    (fullHorosphericalHomeomorph (act (parabolicGL A u d hd) S)).1=
        d⁻¹ • (A.val *ᵥ unipotent S.val+u) ∧
    (fullHorosphericalHomeomorph (act (parabolicGL A u d hd) S)).2.1.val=
        binaryNormalize (A.val*schur S.val*star A.val) ∧
    (fullHorosphericalHomeomorph (act (parabolicGL A u d hd) S)).2.2.val=
        (d⁻¹)^2*(A.val*schur S.val*star A.val).trace := by
  refine ⟨unipotent_act_parabolic A u d hd S,?_,?_⟩
  · change binaryNormalize (schur (act (parabolicGL A u d hd) S).val)=_
    rw [schur_act_parabolic,transformedSchur,
      binaryNormalize_smul _ (pow_ne_zero 2 (inv_ne_zero hd))]
  · change (schur (act (parabolicGL A u d hd) S).val).trace=_
    rw [schur_act_parabolic,transformedSchur,trace_smul,smul_eq_mul]

end TernaryPoly.SymmetricSpaceParabolicCoordinates
