module

public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Generation
public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Coefficients
public import Mathlib.RepresentationTheory.Invariants

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryModularSymbol
open RankTwoAugmentedFrames

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- Genuine equivariant linear maps for the full integral general linear group. -/
def Hom (ρ : Representation ℚ GL2 E) : Submodule ℚ (St →ₗ[ℚ] E) where
  carrier := {f | ∀ g : IntegralGL, ∀ c, f (action (integral g) c) = ρ (integral g) (f c)}
  zero_mem' := by intro g c; simp
  add_mem' := by intro f h hf hh g c; simp [hf g c,hh g c]
  smul_mem' := by intro q f hf g c; simp [hf g c]

@[simp] theorem hom_equivariant (ρ : Representation ℚ GL2 E) (f : Hom ρ)
    (g : IntegralGL) (c : St) :
    f.val (action (integral g) c) = ρ (integral g) (f.val c) := f.property g c

/-- Evaluation is literally the value on the coordinate-line symbol. -/
def evaluation (ρ : Representation ℚ GL2 E) : Hom ρ →ₗ[ℚ] E where
  toFun f := f.val reference
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evaluation_apply (ρ : Representation ℚ GL2 E) (f : Hom ρ) :
    evaluation ρ f = f.val reference := rfl

/-- Actual integral generation makes reference evaluation faithful for every coefficient action. -/
theorem evaluation_injective (ρ : Representation ℚ GL2 E) : Function.Injective (evaluation ρ) := by
  intro f h he
  apply Subtype.ext
  apply LinearMap.ext
  intro c
  have hc : c ∈ integralSpan := by rw [integralSpan_eq_top]; trivial
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨g,rfl⟩ := hc
    rw [hom_equivariant,hom_equivariant]
    exact congrArg (ρ (integral g)) he
  | zero => simp
  | add c d _ _ hc hd => simp only [map_add,hc,hd]
  | smul q c _ hc => simp only [map_smul,hc]

/-- The full rational conjugation action on actual linear maps of modular symbols. -/
def homAction (ρ : Representation ℚ GL2 E) : Representation ℚ GL2 (St →ₗ[ℚ] E) :=
  Representation.linHom action ρ

@[simp] theorem homAction_apply (ρ : Representation ℚ GL2 E) (g : GL2)
    (f : St →ₗ[ℚ] E) (c : St) : homAction ρ g f c = ρ g (f (action g⁻¹ c)) := rfl

theorem homAction_fixed_iff (ρ : Representation ℚ GL2 E) (g : GL2) (f : St →ₗ[ℚ] E) :
    homAction ρ g f = f ↔ ∀ c, f (action g c) = ρ g (f c) := by
  constructor
  · intro hf c
    have he := LinearMap.congr_fun hf (action g c)
    rw [homAction_apply,Representation.inv_self_apply] at he
    exact he.symm
  · intro hf
    apply LinearMap.ext
    intro c
    rw [homAction_apply,←hf,Representation.self_inv_apply]

/-- The requested degree-d, determinant-inverse binary polynomial coefficient model. -/
abbrev PeriodHom (d : ℕ) := Hom (BinaryModularSymbolCoefficients.homogeneousAction d (-1))

end TernaryPoly.BinaryModularSymbol
