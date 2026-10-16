module

public import TernaryPeriodPolynomials.SymmetricSpace.Plane.BordificationTopology
public import TernaryPeriodPolynomials.SymmetricSpace.Plane.BordificationGroup

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpacePlaneBordification
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates

def binaryCongruence (A : RealGL2) (T : BinarySpace) : Mat2 := A.val*T.val*star A.val

theorem binaryCongruence_positive (A : RealGL2) (T : BinarySpace) :
    (binaryCongruence A T).PosDef :=
  (A.isUnit.posDef_star_right_conjugate_iff).mpr T.property.1

def shapeAction (A : RealGL2) (T : BinarySpace) : BinarySpace :=
  ⟨binaryNormalize (binaryCongruence A T),
    binaryNormalize_mem _ (binaryCongruence_positive A T)⟩

/-- The strictly positive multiplier of the boundary coordinate, with the sign of d retained in v. -/
def coefficient (g : Parameters) (T : BinarySpace) : ℝ :=
  |g.d.val|/Real.sqrt (binaryCongruence g.A T).trace

theorem coefficient_pos (g : Parameters) (T : BinarySpace) : 0<coefficient g T :=
  div_pos (abs_pos.mpr g.d.ne_zero)
    (Real.sqrt_pos.mpr (binaryCongruence_positive g.A T).trace_pos)

/-- The literal real block-parabolic action extended to the closed radial half-line. -/
def extend (g : Parameters) (p : PlaneBordification) : PlaneBordification :=
  (transformedUnipotent g.A.val g.u g.d.val p.1,
    (shapeAction g.A p.2.1,⟨coefficient g p.2.1*p.2.2.val,by
      change 0≤coefficient g p.2.1*p.2.2.val
      exact mul_nonneg (coefficient_pos g p.2.1).le p.2.2.property⟩))

@[simp] theorem extend_parameter (g : Parameters) (p : PlaneBordification) :
    (extend g p).2.2.val=coefficient g p.2.1*p.2.2.val := rfl

theorem continuous_binaryCongruence (A : RealGL2) : Continuous (binaryCongruence A) := by
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem continuous_shapeAction (A : RealGL2) : Continuous (shapeAction A) := by
  apply Continuous.subtype_mk
  have hc := continuous_binaryCongruence A
  exact (hc.matrix_trace.inv₀ (fun T =>
    ne_of_gt (binaryCongruence_positive A T).trace_pos)).smul hc

theorem continuous_coefficient (g : Parameters) : Continuous (coefficient g) := by
  exact continuous_const.div₀ (continuous_binaryCongruence g.A).matrix_trace.sqrt
    (fun T => ne_of_gt (Real.sqrt_pos.mpr (binaryCongruence_positive g.A T).trace_pos))

/-- Each extended action is continuous all the way to the zero-radial-coordinate boundary. -/
theorem continuous_extend (g : Parameters) : Continuous (extend g) := by
  apply Continuous.prodMk
  · change Continuous (fun p : PlaneBordification =>
      (g.d.val)⁻¹ • (g.A.val *ᵥ p.1 + g.u))
    have hm : Continuous (fun p : PlaneBordification => g.A.val *ᵥ p.1) :=
      continuous_const.matrix_mulVec continuous_fst
    exact (continuous_const : Continuous (fun _ : PlaneBordification => (g.d.val)⁻¹)).smul
      (hm.add continuous_const)
  · apply Continuous.prodMk
    · exact (continuous_shapeAction g.A).comp (continuous_fst.comp continuous_snd)
    · apply Continuous.subtype_mk
      exact ((continuous_coefficient g).comp (continuous_fst.comp continuous_snd)).mul
        continuous_parameter

theorem extend_interior_iff (g : Parameters) (p : PlaneBordification) :
    extend g p∈interior ↔ p∈interior := by
  change 0<coefficient g p.2.1*p.2.2.val ↔ 0<p.2.2.val
  exact mul_pos_iff_of_pos_left (coefficient_pos g p.2.1)

theorem extend_boundary_iff (g : Parameters) (p : PlaneBordification) :
    extend g p∈boundary ↔ p∈boundary := by
  change coefficient g p.2.1*p.2.2.val=0 ↔ p.2.2.val=0
  simp [ne_of_gt (coefficient_pos g p.2.1)]

theorem schur_eq_trace_smul_shape (S : Space) :
    schur S.val=(schur S.val).trace • binaryNormalize (schur S.val) := by
  rw [binaryNormalize,smul_smul,
    mul_inv_cancel₀ (ne_of_gt (schur_positive S.val S.property.1).trace_pos),one_smul]

theorem congruence_schur_recompose (A : RealGL2) (S : Space) :
    A.val*schur S.val*star A.val=
      (schur S.val).trace • binaryCongruence A (embedding S).2.1 := by
  calc
    _=A.val*((schur S.val).trace • binaryNormalize (schur S.val))*star A.val :=
      congrArg (fun B : Mat2 => A.val*B*star A.val) (schur_eq_trace_smul_shape S)
    _=_ := by rw [Matrix.mul_smul,Matrix.smul_mul]; rfl

/-- The extension agrees with the genuine normalized congruence action on every interior point. -/
theorem extend_embedding (g : Parameters) (S : Space) :
    extend g (embedding S)=embedding (act (toRealGL g) S) := by
  obtain ⟨hu,hT,hr⟩ := fullHorospherical_action_coordinates g.A g.u g.d.val g.d.ne_zero S
  change binaryNormalize (schur (act (toRealGL g) S).val)=
    binaryNormalize (g.A.val*schur S.val*star g.A.val) at hT
  change (schur (act (toRealGL g) S).val).trace=
    (g.d.val⁻¹)^2*(g.A.val*schur S.val*star g.A.val).trace at hr
  apply Prod.ext
  · exact hu.symm
  · apply Prod.ext
    · apply Subtype.ext
      change binaryNormalize (binaryCongruence g.A (embedding S).2.1)=
        binaryNormalize (schur (act (toRealGL g) S).val)
      rw [hT,congruence_schur_recompose,
        binaryNormalize_smul _ (ne_of_gt (schur_positive S.val S.property.1).trace_pos)]
    · apply Subtype.ext
      change |g.d.val|/Real.sqrt (binaryCongruence g.A (embedding S).2.1).trace *
        (Real.sqrt (schur S.val).trace)⁻¹=
        (Real.sqrt (schur (act (toRealGL g) S).val).trace)⁻¹
      rw [hr,congruence_schur_recompose,Matrix.trace_smul,smul_eq_mul,←mul_assoc]
      exact (radial_transform g.d.val (schur S.val).trace
        (binaryCongruence g.A (embedding S).2.1).trace
        (schur_positive S.val S.property.1).trace_pos.le).symm

end TernaryPoly.SymmetricSpacePlaneBordification
