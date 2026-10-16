module

public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.CoordinatesHomeomorph
public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.CoordinatesActionAlgebra

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpaceParabolicCoordinates
open SymmetricSpacePositive

/-- The unnormalized matrix is recovered with its actual positive S22 scale. -/
theorem matrix_from_coordinates (S : Space) :
    S.val=height S.val • assemble (unipotent S.val) (schur S.val) := by
  rw [assemble_coordinates S.val
    (Matrix.isHermitian_iff_isSymm.mp S.property.1.isHermitian)
    (ne_of_gt (height_pos S.val S.property.1)),smul_smul,
    mul_inv_cancel₀ (ne_of_gt (height_pos S.val S.property.1)),one_smul]

/-- The binary Schur factor remains strictly positive under the full signed block action. -/
theorem transformedSchur_positive (A : RealGL2) (d : ℝ) (hd : d≠0)
    (B : Mat2) (hB : B.PosDef) : (transformedSchur A.val d B).PosDef := by
  have hp : (A.val*B*star A.val).PosDef :=
    (A.isUnit.posDef_star_right_conjugate_iff).mpr hB
  exact hp.smul (sq_pos_of_ne_zero (inv_ne_zero hd))

/-- The actual congruence transformation, with its full positive scalar factor preserved. -/
theorem conjugate_parabolic_coordinates (A : RealGL2) (u : Vec2) (d : ℝ) (hd : d≠0)
    (S : Space) :
    conjugate (parabolicGL A u d hd) S.val=
      (height S.val*d^2) • assemble
        (transformedUnipotent A.val u d (unipotent S.val))
        (transformedSchur A.val d (schur S.val)) := by
  calc
    _=conjugate (parabolicGL A u d hd)
        (height S.val • assemble (unipotent S.val) (schur S.val)) :=
      congrArg (conjugate (parabolicGL A u d hd)) (matrix_from_coordinates S)
    _=height S.val • (blockMatrix A.val u d*assemble (unipotent S.val) (schur S.val)*
        star (blockMatrix A.val u d)) := by rw [conjugate_smul]; rfl
    _=_ := by rw [blockMatrix_assemble _ _ _ hd,smul_smul]

/-- The normalized actual action sends v to (A v+u)/d, with no positivity restriction on d. -/
theorem unipotent_act_parabolic (A : RealGL2) (u : Vec2) (d : ℝ) (hd : d≠0)
    (S : Space) :
    unipotent (act (parabolicGL A u d hd) S).val=
      transformedUnipotent A.val u d (unipotent S.val) := by
  change unipotent (normalize (conjugate (parabolicGL A u d hd) S.val))=_
  rw [unipotent_normalize _ (conjugate_positive _ _ S.property.1),
    conjugate_parabolic_coordinates,
    unipotent_smul _ (mul_ne_zero (ne_of_gt (height_pos S.val S.property.1)) (pow_ne_zero 2 hd)),
    unipotent_assemble]

/-- The normalized Schur matrix transforms exactly as d⁻² A B Aᵀ. -/
theorem schur_act_parabolic (A : RealGL2) (u : Vec2) (d : ℝ) (hd : d≠0)
    (S : Space) :
    schur (act (parabolicGL A u d hd) S).val=
      transformedSchur A.val d (schur S.val) := by
  change schur (normalize (conjugate (parabolicGL A u d hd) S.val))=_
  rw [schur_normalize _ (conjugate_positive _ _ S.property.1),
    conjugate_parabolic_coordinates,
    schur_smul _ (mul_ne_zero (ne_of_gt (height_pos S.val S.property.1)) (pow_ne_zero 2 hd)),
    schur_assemble]

/-- The explicit action on the actual horospherical coordinate product. -/
def parabolicCoordinateAction (A : RealGL2) (u : Vec2) (d : ℝ) (hd : d≠0)
    (p : Vec2 × PosDef2) : Vec2 × PosDef2 :=
  (transformedUnipotent A.val u d p.1,
    ⟨transformedSchur A.val d p.2.val,transformedSchur_positive A d hd p.2.val p.2.property⟩)

theorem horosphericalHomeomorph_act_parabolic (A : RealGL2) (u : Vec2) (d : ℝ) (hd : d≠0)
    (S : Space) :
    horosphericalHomeomorph (act (parabolicGL A u d hd) S)=
      parabolicCoordinateAction A u d hd (horosphericalHomeomorph S) := by
  apply Prod.ext
  · exact unipotent_act_parabolic A u d hd S
  · apply Subtype.ext
    exact schur_act_parabolic A u d hd S

end TernaryPoly.SymmetricSpaceParabolicCoordinates
