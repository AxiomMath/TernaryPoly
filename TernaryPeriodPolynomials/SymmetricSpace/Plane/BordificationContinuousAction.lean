module

public import TernaryPeriodPolynomials.SymmetricSpace.Plane.Bordification

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpacePlaneBordification
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates

/-- The normalized binary shape varies continuously with the actual GL2 parameter. -/
theorem continuous_binaryCongruence_joint :
    Continuous (fun z : RealGL2 × BinarySpace => binaryCongruence z.1 z.2) := by
  have hA : Continuous (fun z : RealGL2 × BinarySpace => z.1.val) :=
    Units.continuous_val.comp continuous_fst
  have hT : Continuous (fun z : RealGL2 × BinarySpace => z.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact (hA.mul hT).mul hA.star

theorem continuous_shapeAction_joint :
    Continuous (fun z : RealGL2 × BinarySpace => shapeAction z.1 z.2) := by
  apply Continuous.subtype_mk
  have hc := continuous_binaryCongruence_joint
  exact (hc.matrix_trace.inv₀ (fun z =>
    ne_of_gt (binaryCongruence_positive z.1 z.2).trace_pos)).smul hc

theorem continuous_coefficient_joint :
    Continuous (fun z : Parameters × BinarySpace => coefficient z.1 z.2) := by
  have hd : Continuous (fun z : Parameters × BinarySpace => z.1.d.val) :=
    Units.continuous_val.comp (continuous_d.comp continuous_fst)
  have hc : Continuous (fun z : Parameters × BinarySpace => binaryCongruence z.1.A z.2) :=
    continuous_binaryCongruence_joint.comp
      ((continuous_A.comp continuous_fst).prodMk continuous_snd)
  exact hd.abs.div₀ hc.matrix_trace.sqrt
    (fun z => ne_of_gt (Real.sqrt_pos.mpr (binaryCongruence_positive z.1.A z.2).trace_pos))

/-- Joint continuity of the signed affine unipotent coordinate. -/
theorem continuous_transformedUnipotent_joint :
    Continuous (fun z : Parameters × Vec2 =>
      transformedUnipotent z.1.A.val z.1.u z.1.d.val z.2) := by
  have hA : Continuous (fun z : Parameters × Vec2 => z.1.A.val) :=
    Units.continuous_val.comp (continuous_A.comp continuous_fst)
  have hu : Continuous (fun z : Parameters × Vec2 => z.1.u) :=
    continuous_u.comp continuous_fst
  have hd : Continuous (fun z : Parameters × Vec2 => (z.1.d.val)⁻¹) :=
    (Units.continuous_val.comp (continuous_d.comp continuous_fst)).inv₀
      (fun z => z.1.d.ne_zero)
  change Continuous (fun z : Parameters × Vec2 =>
    (z.1.d.val)⁻¹ • (z.1.A.val *ᵥ z.2 + z.1.u))
  exact hd.smul ((hA.matrix_mulVec continuous_snd).add hu)

theorem continuous_extend_unipotent :
    Continuous (fun z : Parameters × PlaneBordification => (extend z.1 z.2).1) := by
  have hv : Continuous (fun z : Parameters × PlaneBordification => (z.1,z.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  exact continuous_transformedUnipotent_joint.comp hv

theorem continuous_extend_shape :
    Continuous (fun z : Parameters × PlaneBordification => (extend z.1 z.2).2.1) := by
  have hAT : Continuous (fun z : Parameters × PlaneBordification => (z.1.A,z.2.2.1)) :=
    (continuous_A.comp continuous_fst).prodMk
      ((continuous_fst.comp continuous_snd).comp continuous_snd)
  have hh := continuous_shapeAction_joint.comp hAT
  exact hh

theorem continuous_extend_parameter :
    Continuous (fun z : Parameters × PlaneBordification => (extend z.1 z.2).2.2) := by
  have hgT : Continuous (fun z : Parameters × PlaneBordification => (z.1,z.2.2.1)) :=
    continuous_fst.prodMk ((continuous_fst.comp continuous_snd).comp continuous_snd)
  apply Continuous.subtype_mk
  exact (continuous_coefficient_joint.comp hgT).mul
    (continuous_parameter.comp continuous_snd)

/-- Joint continuity holds on the closed half-line, including at every boundary point. -/
theorem continuous_extend_joint :
    Continuous (fun z : Parameters × PlaneBordification => extend z.1 z.2) :=
  continuous_extend_unipotent.prodMk (continuous_extend_shape.prodMk continuous_extend_parameter)

instance planeContinuousSMul : ContinuousSMul Parameters PlaneBordification where
  continuous_smul := continuous_extend_joint

/-- The boundary action is jointly continuous in the same genuine real parameters. -/
theorem continuous_boundaryAction_joint :
    Continuous (fun z : Parameters × PlaneBoundary => boundaryAction z.1 z.2) := by
  apply Continuous.subtype_mk
  exact continuous_extend_joint.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

end TernaryPoly.SymmetricSpacePlaneBordification
