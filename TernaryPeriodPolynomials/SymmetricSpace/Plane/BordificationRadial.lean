module

public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.Coordinates
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpacePlaneBordification
open SymmetricSpaceParabolicCoordinates

/-- The positive radial change r↦1/sqrt(r), with inverse t↦1/t². -/
def radialHomeomorph : PositiveScale ≃ₜ PositiveScale where
  toFun r := ⟨(Real.sqrt r.val)⁻¹,inv_pos.mpr (Real.sqrt_pos.mpr r.property)⟩
  invFun t := ⟨(t.val⁻¹)^2,by
    change 0<(t.val⁻¹)^2
    exact sq_pos_of_pos (inv_pos.mpr t.property)⟩
  left_inv r := by
    apply Subtype.ext
    change (((Real.sqrt r.val)⁻¹)⁻¹)^2=r.val
    rw [inv_inv,Real.sq_sqrt r.property.le]
  right_inv t := by
    apply Subtype.ext
    change (Real.sqrt ((t.val⁻¹)^2))⁻¹=t.val
    rw [Real.sqrt_sq (inv_nonneg.mpr t.property.le),inv_inv]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sqrt.inv₀ (fun r => ne_of_gt (Real.sqrt_pos.mpr r.property))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.inv₀ (fun t => ne_of_gt t.property)).pow 2

@[simp] theorem radialHomeomorph_apply (r : PositiveScale) :
    (radialHomeomorph r).val=(Real.sqrt r.val)⁻¹ := rfl

@[simp] theorem radialHomeomorph_symm_apply (t : PositiveScale) :
    (radialHomeomorph.symm t).val=(t.val⁻¹)^2 := rfl

/-- The signed block action gives the exact positive multiplier of the boundary parameter. -/
theorem radial_transform (d r c : ℝ) (hr : 0≤r) :
    (Real.sqrt ((d⁻¹)^2*r*c))⁻¹=
      |d|/Real.sqrt c*(Real.sqrt r)⁻¹ := by
  rw [Real.sqrt_mul (mul_nonneg (sq_nonneg _) hr),Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs,abs_inv]
  simp only [_root_.mul_inv_rev,inv_inv,div_eq_mul_inv]
  ring

end TernaryPoly.SymmetricSpacePlaneBordification
