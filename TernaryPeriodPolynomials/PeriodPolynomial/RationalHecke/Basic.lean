module

public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Hom
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Arithmetic.FiniteIndex

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryRationalHecke
open BinaryModularSymbol BinaryRationalHeckeArithmetic

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- The actual Gamma-invariant subspace of the rational conjugation representation. -/
def fixed (ρ : Representation ℚ GL2 E) :
    Submodule ℚ (St →ₗ[ℚ] E) :=
  (Rep.res Gamma.subtype (Rep.of (homAction ρ))).ρ.invariants

/-- The actual integral-group isomorphism identifies equivariance with rational-image invariance. -/
theorem mem_hom_iff_fixed (ρ : Representation ℚ GL2 E)
    (f : St →ₗ[ℚ] E) : f ∈ Hom ρ ↔ f ∈ fixed ρ := by
  constructor
  · intro hf
    change ∀ g : Gamma, homAction ρ g.val f = f
    intro g
    obtain ⟨h,rfl⟩ := integralEquiv.surjective g
    apply (homAction_fixed_iff ρ (BinaryModularSymbol.integral h) f).mpr
    exact hf h
  · intro hf g
    have he : homAction ρ (integralEquiv g).val f = f := hf (integralEquiv g)
    exact (homAction_fixed_iff ρ (BinaryModularSymbol.integral g) f).mp he

/-- A literal identity-on-functions linear equivalence, with no change of coefficient module. -/
def homEquiv (ρ : Representation ℚ GL2 E) : Hom ρ ≃ₗ[ℚ] fixed ρ where
  toFun f := ⟨f.val,(mem_hom_iff_fixed ρ f.val).mp f.property⟩
  invFun f := ⟨f.val,(mem_hom_iff_fixed ρ f.val).mpr f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem homEquiv_val (ρ : Representation ℚ GL2 E) (f : Hom ρ) :
    (homEquiv ρ f).val = f.val := rfl
@[simp] theorem homEquiv_symm_val (ρ : Representation ℚ GL2 E) (f : fixed ρ) :
    ((homEquiv ρ).symm f).val = f.val := rfl


open OrdinaryHeckeTransfer RationalCohomologyDescent
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The actual full rational Hecke correspondence, without any finite-index assumption. -/
def rationalHecke (g : GL2) (ρ : Representation ℚ GL2 E) : Module.End ℚ (Hom ρ) := by
  letI := intersection_finiteIndex g
  exact (homEquiv ρ).symm.toLinearMap.comp
    ((hecke Gamma g (Rep.of (homAction ρ))).comp (homEquiv ρ).toLinearMap)

/-- Literal coset sum on actual binary modular-symbol functionals. -/
theorem rationalHecke_apply (g : GL2) (ρ : Representation ℚ GL2 E) (f : Hom ρ) :
    (rationalHecke g ρ f).val =
      letI := intersection_finiteIndex g
      ∑ q : RightCosets (intersection Gamma g), homAction ρ (q.out.val⁻¹*g) f.val := by
  let := intersection_finiteIndex g
  exact hecke_apply Gamma g (Rep.of (homAction ρ)) (homEquiv ρ f)

/-- The coefficient-and-cycle convention is retained literally at every rational matrix. -/
theorem rationalHecke_apply_symbol (g : GL2) (ρ : Representation ℚ GL2 E) (f : Hom ρ)
    (L M : Line) :
    (rationalHecke g ρ f).val (symbol L M) =
      letI := intersection_finiteIndex g
      ∑ q : RightCosets (intersection Gamma g),
        ρ (q.out.val⁻¹*g) (f.val (symbol (lineAction (q.out.val⁻¹*g)⁻¹ L)
          (lineAction (q.out.val⁻¹*g)⁻¹ M))) := by
  let := intersection_finiteIndex g
  have he := congrArg (fun h : St →ₗ[ℚ] E => h (symbol L M)) (rationalHecke_apply g ρ f)
  simpa only [LinearMap.sum_apply,homAction_apply,action_symbol] using he

end TernaryPoly.BinaryRationalHecke
