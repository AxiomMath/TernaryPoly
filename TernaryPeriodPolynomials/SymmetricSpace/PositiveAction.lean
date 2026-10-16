module

public import TernaryPeriodPolynomials.SymmetricSpace.Positive
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Instances.Matrix

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpacePositive
open Matrix
abbrev RealGL := GeneralLinearGroup (Fin 3) ℝ

/-- The genuine congruence action on symmetric matrices, before radial normalization. -/
def conjugate (g : RealGL) (S : Mat) : Mat := g.val*S*star g.val

theorem conjugate_positive (g : RealGL) (S : Mat) (hS : S.PosDef) :
    (conjugate g S).PosDef :=
  (g.isUnit.posDef_star_right_conjugate_iff).mpr hS

@[simp] theorem conjugate_one (S : Mat) : conjugate 1 S=S := by simp [conjugate]

theorem conjugate_mul (g h : RealGL) (S : Mat) :
    conjugate (g*h) S=conjugate g (conjugate h S) := by
  simp [conjugate,mul_assoc]

theorem conjugate_smul (g : RealGL) (r : ℝ) (S : Mat) :
    conjugate g (r • S)=r • conjugate g S := by
  simp only [conjugate,Matrix.mul_smul,Matrix.smul_mul]

/-- The actual action on positive-definite forms modulo positive homotheties. -/
def act (g : RealGL) (S : Space) : Space :=
  ⟨normalize (conjugate g S.val),normalize_mem _ (conjugate_positive g S.val S.property.1)⟩

@[simp] theorem act_one (S : Space) : act 1 S=S := by
  apply Subtype.ext
  change normalize (conjugate 1 S.val)=S.val
  rw [conjugate_one,normalize_of_trace_one _ S.property.2]

theorem act_mul (g h : RealGL) (S : Space) : act (g*h) S=act g (act h S) := by
  apply Subtype.ext
  change normalize (conjugate (g*h) S.val)=normalize (conjugate g (normalize (conjugate h S.val)))
  rw [conjugate_mul]
  change normalize (conjugate g (conjugate h S.val))=
    normalize (conjugate g ((conjugate h S.val).trace⁻¹ • conjugate h S.val))
  rw [conjugate_smul,normalize_smul _
    (inv_ne_zero (ne_of_gt (conjugate_positive h S.val S.property.1).trace_pos))]

instance : MulAction RealGL Space where
  smul := act
  one_smul := act_one
  mul_smul := act_mul

/-- Each rational/integral matrix later acts by this continuous normalized congruence map. -/
theorem continuous_act (g : RealGL) : Continuous (act g) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun S : Space => conjugate g S.val) := by
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  exact (hc.matrix_trace.inv₀ (fun S =>
    ne_of_gt (conjugate_positive g S.val S.property.1).trace_pos)).smul hc

/-- Invertible matrices give actual homeomorphisms of the contractible form model. -/
def actionHomeomorph (g : RealGL) : Space ≃ₜ Space where
  toFun := act g
  invFun := act g⁻¹
  left_inv S := by rw [←act_mul,inv_mul_cancel,act_one]
  right_inv S := by rw [←act_mul,mul_inv_cancel,act_one]
  continuous_toFun := continuous_act g
  continuous_invFun := continuous_act g⁻¹

end TernaryPoly.SymmetricSpacePositive
