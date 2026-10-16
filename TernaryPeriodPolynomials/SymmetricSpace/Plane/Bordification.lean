module

public import TernaryPeriodPolynomials.SymmetricSpace.Plane.BordificationExtension
public import TernaryPeriodPolynomials.SymmetricSpace.Plane.BordificationParameterTopology

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpacePlaneBordification
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates

/-- The identity law holds on the dense actual interior and hence on the partial bordification. -/
@[simp] theorem extend_one (p : PlaneBordification) : extend 1 p=p := by
  have h : extend 1=id := denseRange_embedding.equalizer
    (continuous_extend 1) continuous_id (by
      funext S
      simp only [Function.comp_apply,extend_embedding,toRealGL_one,act_one,id_eq])
  exact congrFun h p

/-- The composition law follows from actual matrix multiplication on the dense interior. -/
theorem extend_mul (g h : Parameters) (p : PlaneBordification) :
    extend (g*h) p=extend g (extend h p) := by
  have he : extend (g*h)=extend g ∘ extend h := denseRange_embedding.equalizer
    (continuous_extend (g*h)) ((continuous_extend g).comp (continuous_extend h)) (by
      funext S
      simp only [Function.comp_apply,extend_embedding,toRealGL_mul,act_mul])
  exact congrFun he p

instance planeMulAction : MulAction Parameters PlaneBordification where
  smul := extend
  one_smul := extend_one
  mul_smul := extend_mul

/-- Each actual signed parabolic parameter gives a homeomorphism, inverted by its group inverse. -/
def extendedHomeomorph (g : Parameters) : PlaneBordification ≃ₜ PlaneBordification where
  toFun := extend g
  invFun := extend g⁻¹
  left_inv p := by rw [←extend_mul,inv_mul_cancel,extend_one]
  right_inv p := by rw [←extend_mul,mul_inv_cancel,extend_one]
  continuous_toFun := continuous_extend g
  continuous_invFun := continuous_extend g⁻¹

@[simp] theorem extendedHomeomorph_apply (g : Parameters) (p : PlaneBordification) :
    extendedHomeomorph g p=extend g p := rfl

@[simp] theorem extendedHomeomorph_symm_apply (g : Parameters) (p : PlaneBordification) :
    (extendedHomeomorph g).symm p=extend g⁻¹ p := rfl

/-- The actual parabolic action restricts to the full boundary stratum. -/
def boundaryAction (g : Parameters) (p : PlaneBoundary) : PlaneBoundary :=
  ⟨extend g p.val,(extend_boundary_iff g p.val).mpr p.property⟩

def boundaryActionHomeomorph (g : Parameters) : PlaneBoundary ≃ₜ PlaneBoundary where
  toFun := boundaryAction g
  invFun := boundaryAction g⁻¹
  left_inv p := by apply Subtype.ext; exact (extendedHomeomorph g).left_inv p.val
  right_inv p := by apply Subtype.ext; exact (extendedHomeomorph g).right_inv p.val
  continuous_toFun := ((continuous_extend g).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_extend g⁻¹).comp continuous_subtype_val).subtype_mk _

theorem boundaryAction_coordinates (g : Parameters) (p : PlaneBoundary) :
    boundaryHomeomorph (boundaryAction g p)=
      (transformedUnipotent g.A.val g.u g.d.val p.val.1,shapeAction g.A p.val.2.1) := rfl

end TernaryPoly.SymmetricSpacePlaneBordification
