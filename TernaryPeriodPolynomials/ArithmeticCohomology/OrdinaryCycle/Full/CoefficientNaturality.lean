module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.Coefficient

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryFullCoefficient
open OrdinaryFullAction OrdinaryApartmentPresentation

variable {E F : Type*} [AddCommGroup E] [Module ℚ E] [AddCommGroup F] [Module ℚ F]
variable (ρ : Representation ℚ GL3 E) (τ : Representation ℚ GL3 F)
variable (T : E →ₗ[ℚ] F) (hT : ∀ g x, T (ρ g x) = τ g (T x))
include hT

/-- Equivariant maps between actual rational representations preserve the exact apartment equations. -/
theorem relations_map (v : E) (hv : Relations ρ v) : Relations τ (T v) where
  signs s := by rw [←hT,hv.signs]
  cyclic := by rw [←hT,hv.cyclic]
  swap := by rw [←hT,hv.swap,map_neg]
  norm := by rw [←hT,←hT,←map_add,←map_add,hv.norm,map_zero]

/-- Postcomposition on genuine full-level equivariant cycle functionals. -/
def homMap : Hom ρ →ₗ[ℚ] Hom τ where
  toFun f := ⟨T.comp f.val,by
    intro g c
    change T (f.val (cycleAction (integral g) c)) = τ (integral g) (T (f.val c))
    rw [f.property,hT]⟩
  map_add' f h := by apply Subtype.ext; ext c; exact T.map_add _ _
  map_smul' q f := by apply Subtype.ext; ext c; exact T.map_smul q _

@[simp] theorem homMap_apply (f : Hom ρ) (c : OrdinaryIncidenceChains.Cycles) :
    (homMap ρ τ T hT f).val c = T (f.val c) := rfl

/-- The presentation-built functional commutes with every actual equivariant coefficient map. -/
theorem functional_natural (v : E) (hv : Relations ρ v) :
    functional τ (T v) (relations_map ρ τ T hT v hv) = T.comp (functional ρ v hv) := by
  apply cycle_functional_ext
  intro g
  rw [LinearMap.comp_apply,functional_frame,functional_frame,hT]

/-- Reference evaluation commutes literally with coefficient postcomposition. -/
theorem reference_natural (f : Hom ρ) :
    (coefficientEquiv τ (homMap ρ τ T hT f)).val = T (coefficientEquiv ρ f).val := rfl

end TernaryPoly.OrdinaryFullCoefficient
