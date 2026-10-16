module

public import TernaryPeriodPolynomials.SymmetricSpace.Flag.Coordinates
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceFlagCoordinates
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates

abbrev PositivePair := PositiveScale × PositiveScale
abbrev RootParameters := Vec3 × PositivePair

/-- The simple-root coordinates of the two actual diagonal pivots. -/
def positiveRootHomeomorph : PositivePair ≃ₜ PositivePair where
  toFun p := (⟨Real.sqrt (p.2.val/p.1.val),Real.sqrt_pos.mpr (div_pos p.2.property p.1.property)⟩,
    ⟨(Real.sqrt p.2.val)⁻¹,inv_pos.mpr (Real.sqrt_pos.mpr p.2.property)⟩)
  invFun p := (⟨(p.1.val^2*p.2.val^2)⁻¹,by
      change 0<(p.1.val^2*p.2.val^2)⁻¹
      exact inv_pos.mpr (mul_pos (pow_pos (show 0<p.1.val from p.1.property) 2)
        (pow_pos (show 0<p.2.val from p.2.property) 2))⟩,
    ⟨(p.2.val^2)⁻¹,by
      change 0<(p.2.val^2)⁻¹
      exact inv_pos.mpr (pow_pos (show 0<p.2.val from p.2.property) 2)⟩)
  left_inv p := by
    have h1 : 0<p.1.val := p.1.property
    have h2 : 0<p.2.val := p.2.property
    apply Prod.ext
    · apply Subtype.ext
      change ((Real.sqrt (p.2.val/p.1.val))^2*((Real.sqrt p.2.val)⁻¹)^2)⁻¹=p.1.val
      rw [inv_pow,Real.sq_sqrt (div_pos p.2.property p.1.property).le,
        Real.sq_sqrt p.2.property.le]
      field_simp [ne_of_gt h1,ne_of_gt h2]
    · apply Subtype.ext
      change (((Real.sqrt p.2.val)⁻¹)^2)⁻¹=p.2.val
      rw [inv_pow,Real.sq_sqrt p.2.property.le,inv_inv]
  right_inv p := by
    have h1 : 0<p.1.val := p.1.property
    have h2 : 0<p.2.val := p.2.property
    apply Prod.ext
    · apply Subtype.ext
      change Real.sqrt ((p.2.val^2)⁻¹/((p.1.val^2*p.2.val^2)⁻¹))=p.1.val
      have heq : (p.2.val^2)⁻¹/((p.1.val^2*p.2.val^2)⁻¹)=p.1.val^2 := by
        field_simp [ne_of_gt h1,ne_of_gt h2]
      rw [heq,Real.sqrt_sq p.1.property.le]
    · apply Subtype.ext
      change (Real.sqrt ((p.2.val^2)⁻¹))⁻¹=p.2.val
      rw [Real.sqrt_inv,Real.sqrt_sq p.2.property.le,inv_inv]
  continuous_toFun := by
    have h1 : Continuous (fun p : PositivePair => p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : PositivePair => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    apply Continuous.prodMk
    · exact Continuous.subtype_mk ((h2.div₀ h1 (fun p => ne_of_gt p.1.property)).sqrt) _
    · exact Continuous.subtype_mk (h2.sqrt.inv₀
        (fun p => ne_of_gt (Real.sqrt_pos.mpr p.2.property))) _
  continuous_invFun := by
    have h1 : Continuous (fun p : PositivePair => p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : PositivePair => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    apply Continuous.prodMk
    · exact Continuous.subtype_mk (((h1.pow 2).mul (h2.pow 2)).inv₀
        (fun p => ne_of_gt (mul_pos (pow_pos p.1.property 2) (pow_pos p.2.property 2)))) _
    · exact Continuous.subtype_mk ((h2.pow 2).inv₀
        (fun p => ne_of_gt (pow_pos p.2.property 2))) _

/-- The actual positive form space in positive simple-root coordinates. -/
def rootHomeomorph : Space ≃ₜ RootParameters :=
  ldlHomeomorph.trans ((Homeomorph.refl Vec3).prodCongr positiveRootHomeomorph)

@[simp] theorem rootHomeomorph_unipotent (S : Space) :
    (rootHomeomorph S).1=(ldlHomeomorph S).1 := rfl

@[simp] theorem rootHomeomorph_t1 (S : Space) :
    (rootHomeomorph S).2.1.val=
      Real.sqrt ((ldlHomeomorph S).2.2.val/(ldlHomeomorph S).2.1.val) := rfl

@[simp] theorem rootHomeomorph_t2 (S : Space) :
    (rootHomeomorph S).2.2.val=(Real.sqrt (ldlHomeomorph S).2.2.val)⁻¹ := rfl

/-- Exact inverse pivot formulas in the normalized upper-triangular matrix model. -/
@[simp] theorem rootHomeomorph_symm (p : RootParameters) :
    (rootHomeomorph.symm p).val=normalize
      (flagMatrix (p.1 0) (p.1 1) (p.1 2) (p.2.1.val^2*p.2.2.val^2)⁻¹ (p.2.2.val^2)⁻¹) :=
  ldlHomeomorph_symm _

end TernaryPoly.SymmetricSpaceFlagCoordinates
