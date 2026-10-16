module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.CoefficientNaturality
public import Mathlib.RepresentationTheory.Invariants

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHomHecke
open OrdinaryFullAction OrdinaryFullCoefficient CategoryTheory

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- The actual rational conjugation representation on linear functionals on ordinary cycles. -/
def linearAction (ρ : Representation ℚ GL3 E) :
    Representation ℚ GL3 (OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E) :=
  Representation.linHom cycleAction ρ

abbrev linearRep (ρ : Representation ℚ GL3 E) : Rep ℚ GL3 := Rep.of (linearAction ρ)

@[simp] theorem linearAction_apply (ρ : Representation ℚ GL3 E) (g : GL3)
    (f : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E) (c : OrdinaryIncidenceChains.Cycles) :
    linearAction ρ g f c = ρ g (f (cycleAction g⁻¹ c)) := rfl

/-- Fixed linear maps are precisely genuine equivariant maps for the displayed group element. -/
theorem linearAction_fixed_iff (ρ : Representation ℚ GL3 E) (g : GL3)
    (f : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E) :
    linearAction ρ g f = f ↔ ∀ c, f (cycleAction g c) = ρ g (f c) := by
  constructor
  · intro hf c
    have he := LinearMap.congr_fun hf (cycleAction g c)
    rw [linearAction_apply,Representation.inv_self_apply] at he
    exact he.symm
  · intro hf
    apply LinearMap.ext
    intro c
    rw [linearAction_apply,←hf,Representation.self_inv_apply]

variable {F : Type*} [AddCommGroup F] [Module ℚ F]

/-- Actual coefficient postcomposition on the ambient linear-map representation. -/
def postcompose (T : E →ₗ[ℚ] F) :
    (OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E) →ₗ[ℚ]
      (OrdinaryIncidenceChains.Cycles →ₗ[ℚ] F) where
  toFun f := T.comp f
  map_add' _ _ := by ext c; exact T.map_add _ _
  map_smul' q _ := by ext c; exact T.map_smul q _

@[simp] theorem postcompose_apply (T : E →ₗ[ℚ] F)
    (f : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E) (c : OrdinaryIncidenceChains.Cycles) :
    postcompose T f c = T (f c) := rfl

theorem postcompose_equivariant (ρ : Representation ℚ GL3 E) (τ : Representation ℚ GL3 F)
    (T : E →ₗ[ℚ] F) (hT : ∀ g x, T (ρ g x) = τ g (T x))
    (g : GL3) (f : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E) :
    postcompose T (linearAction ρ g f) = linearAction τ g (postcompose T f) := by
  ext c
  exact hT g (f (cycleAction g⁻¹ c))

end TernaryPoly.OrdinaryHomHecke
