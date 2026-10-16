module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hom.HeckeLinear
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.Arithmetic

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryHomHecke
open OrdinaryFullAction OrdinaryFullCoefficient OrdinaryHeckeArithmetic

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- The actual Gamma-invariant subspace of the rational conjugation representation. -/
def fixed (ρ : Representation ℚ GL3 E) :
    Submodule ℚ (OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E) :=
  (Rep.res Gamma.subtype (linearRep ρ)).ρ.invariants

/-- The actual integral-group isomorphism identifies equivariance with rational-image invariance. -/
theorem mem_hom_iff_fixed (ρ : Representation ℚ GL3 E)
    (f : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E) : f ∈ Hom ρ ↔ f ∈ fixed ρ := by
  constructor
  · intro hf
    change ∀ g : Gamma, linearAction ρ g.val f = f
    intro g
    obtain ⟨h,rfl⟩ := integralEquiv.surjective g
    apply (linearAction_fixed_iff ρ (OrdinaryFullAction.integral h) f).mpr
    exact hf h
  · intro hf g
    have he : linearAction ρ (integralEquiv g).val f = f := hf (integralEquiv g)
    exact (linearAction_fixed_iff ρ (OrdinaryFullAction.integral g) f).mp he

/-- A literal identity-on-functions linear equivalence, with no change of coefficient module. -/
def homEquiv (ρ : Representation ℚ GL3 E) : Hom ρ ≃ₗ[ℚ] fixed ρ where
  toFun f := ⟨f.val,(mem_hom_iff_fixed ρ f.val).mp f.property⟩
  invFun f := ⟨f.val,(mem_hom_iff_fixed ρ f.val).mpr f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem homEquiv_val (ρ : Representation ℚ GL3 E) (f : Hom ρ) :
    (homEquiv ρ f).val = f.val := rfl
@[simp] theorem homEquiv_symm_val (ρ : Representation ℚ GL3 E) (f : fixed ρ) :
    ((homEquiv ρ).symm f).val = f.val := rfl

end TernaryPoly.OrdinaryHomHecke
