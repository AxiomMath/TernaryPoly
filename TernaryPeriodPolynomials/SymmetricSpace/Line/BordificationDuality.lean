module

public import TernaryPeriodPolynomials.SymmetricSpace.PositiveAction
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceLineBordification
open Matrix
open SymmetricSpacePositive

/-- Inverse transpose on the actual real general linear group. -/
def contragredient (g : RealGL) : RealGL := star g⁻¹

@[simp] theorem contragredient_val (g : RealGL) :
    (contragredient g).val=(g.val⁻¹).transpose := by
  simp [contragredient,Matrix.coe_units_inv,Matrix.star_eq_conjTranspose]

@[simp] theorem contragredient_involutive (g : RealGL) :
    contragredient (contragredient g)=g := by simp [contragredient]

theorem contragredient_mul (g h : RealGL) :
    contragredient (g*h)=contragredient g*contragredient h := by
  simp [contragredient]

def contragredientEquiv : RealGL ≃* RealGL where
  toFun := contragredient
  invFun := contragredient
  left_inv := contragredient_involutive
  right_inv := contragredient_involutive
  map_mul' := contragredient_mul

/-- Literal normalized inverse-form duality on the existing trace-one positive space. -/
def inverseForm (S : Space) : Space :=
  ⟨normalize S.val⁻¹,normalize_mem _ S.property.1.inv⟩

theorem inv_normalize (S : Mat) (hS : S.PosDef) :
    (normalize S)⁻¹=S.trace • S⁻¹ := by
  apply Matrix.inv_eq_right_inv
  change (S.trace⁻¹ • S)*(S.trace • S⁻¹)=1
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    inv_mul_cancel₀ (ne_of_gt hS.trace_pos),one_smul]
  exact Matrix.mul_nonsing_inv S (isUnit_iff_ne_zero.mpr (ne_of_gt hS.det_pos))

@[simp] theorem inverseForm_involutive (S : Space) : inverseForm (inverseForm S)=S := by
  apply Subtype.ext
  change normalize (normalize S.val⁻¹)⁻¹=S.val
  rw [inv_normalize _ S.property.1.inv,normalize_smul _
    (ne_of_gt S.property.1.inv.trace_pos),Matrix.nonsing_inv_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (ne_of_gt S.property.1.det_pos)),normalize_of_trace_one _ S.property.2]

theorem continuous_inverse_matrix : Continuous (fun S : Space => S.val⁻¹) := by
  simp only [Matrix.inv_def,Ring.inverse_eq_inv]
  exact (continuous_subtype_val.matrix_det.inv₀ (fun S => ne_of_gt S.property.1.det_pos)).smul
    continuous_subtype_val.matrix_adjugate

theorem continuous_inverseForm : Continuous inverseForm := by
  apply Continuous.subtype_mk
  exact (continuous_inverse_matrix.matrix_trace.inv₀
    (fun S => ne_of_gt S.property.1.inv.trace_pos)).smul continuous_inverse_matrix

/-- Inverse-form duality exchanges the standard e0,e1-plane with its annihilator e2-line. -/
def inverseFormHomeomorph : Space ≃ₜ Space where
  toFun := inverseForm
  invFun := inverseForm
  left_inv := inverseForm_involutive
  right_inv := inverseForm_involutive
  continuous_toFun := continuous_inverseForm
  continuous_invFun := continuous_inverseForm

theorem inverse_conjugate (g : RealGL) (S : Mat) :
    (conjugate g S)⁻¹=conjugate (contragredient g) S⁻¹ := by
  simp only [conjugate,Matrix.mul_inv_rev,contragredient,Units.coe_star,
    Matrix.coe_units_inv,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc]

/-- The actual normalized action intertwines with inverse transpose, with no determinant sign restriction. -/
theorem inverseForm_act (g : RealGL) (S : Space) :
    inverseForm (act g S)=act (contragredient g) (inverseForm S) := by
  apply Subtype.ext
  change normalize (normalize (conjugate g S.val))⁻¹=
    normalize (conjugate (contragredient g) (normalize S.val⁻¹))
  rw [inv_normalize _ (conjugate_positive g _ S.property.1),
    normalize_smul _ (ne_of_gt (conjugate_positive g _ S.property.1).trace_pos),inverse_conjugate]
  change normalize (conjugate (contragredient g) S.val⁻¹)=
    normalize (conjugate (contragredient g) ((S.val⁻¹).trace⁻¹ • S.val⁻¹))
  rw [conjugate_smul,normalize_smul _ (inv_ne_zero (ne_of_gt S.property.1.inv.trace_pos))]

end TernaryPoly.SymmetricSpaceLineBordification
