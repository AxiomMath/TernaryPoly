module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hom.HeckeInvariants
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.Transfer

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHomHecke
open OrdinaryFullAction OrdinaryFullCoefficient OrdinaryHeckeArithmetic OrdinaryHeckeTransfer
open RationalCohomologyDescent CategoryTheory

variable {E : Type*} [AddCommGroup E] [Module ℚ E]
variable (g : OrdinaryFullAction.GL3) [(intersection Gamma g).FiniteIndex]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The genuine conjugation-transfer Hecke operator on full ordinary cycle functionals. -/
def heckeHom (ρ : Representation ℚ OrdinaryFullAction.GL3 E) : Module.End ℚ (Hom ρ) :=
  (homEquiv ρ).symm.toLinearMap.comp
    ((hecke Gamma g (linearRep ρ)).comp (homEquiv ρ).toLinearMap)

/-- The exact unnormalized sum of conjugated actual functionals, over inverse right-coset representatives. -/
theorem heckeHom_apply (ρ : Representation ℚ OrdinaryFullAction.GL3 E) (f : Hom ρ) :
    (heckeHom g ρ f).val =
      ∑ q : RightCosets (intersection Gamma g),
        linearAction ρ (q.out.val⁻¹*g) f.val :=
  hecke_apply Gamma g (linearRep ρ) (homEquiv ρ f)

/-- Literal coefficient-and-cycle action formula for the genuine Hecke correspondence. -/
theorem heckeHom_apply_cycle (ρ : Representation ℚ OrdinaryFullAction.GL3 E) (f : Hom ρ)
    (c : OrdinaryIncidenceChains.Cycles) :
    (heckeHom g ρ f).val c =
      ∑ q : RightCosets (intersection Gamma g),
        ρ (q.out.val⁻¹*g) (f.val (cycleAction (q.out.val⁻¹*g)⁻¹ c)) := by
  have he := congrArg (fun h : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E => h c)
    (heckeHom_apply g ρ f)
  simpa only [LinearMap.sum_apply,linearAction_apply] using he

variable {F : Type*} [AddCommGroup F] [Module ℚ F]

/-- Actual coefficient intertwiners commute with the actual Hecke sum on full ordinary Hom spaces. -/
theorem heckeHom_natural (ρ : Representation ℚ OrdinaryFullAction.GL3 E)
    (τ : Representation ℚ OrdinaryFullAction.GL3 F) (T : E →ₗ[ℚ] F)
    (hT : ∀ h x, T (ρ h x) = τ h (T x)) (f : Hom ρ) :
    homMap ρ τ T hT (heckeHom g ρ f) = heckeHom g τ (homMap ρ τ T hT f) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro c
  change T ((heckeHom g ρ f).val c) = _
  rw [heckeHom_apply_cycle,heckeHom_apply_cycle,map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact hT _ _

end TernaryPoly.OrdinaryHomHecke
