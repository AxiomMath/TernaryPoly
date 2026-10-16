module

public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Space

@[expose] public section


/-!
# The span of finite translates of adelic lifts and its level subspaces

`liftSpan S` is the span of the right translates `x ↦ adelicLift f (x · atFinite u)` of the adelic
lifts of the cusp forms `f ∈ S` on `Γ₁(3)` by elements `u` of `GL₂(𝔸_f)`, and
`levelSubmodule S U` its subspace of functions invariant under right translation by a subgroup
`U` of `GL₂(𝔸_f)`. `LiftLevelFinite k S` asserts that these level subspaces are finite
dimensional for open compact `U`; it is the finite-dimensionality input of the finite-adelic model
of the lifts.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
open TernaryPeriodPolynomials.CuspIntegral

namespace TernaryPeriodPolynomials.Regularity

/-- The span of the right `GL₂(𝔸_f)`-translates of the adelic lifts of the cusp forms in `S`. -/
def liftSpan {k : ℤ} (S : Set (CuspForm binaryRealGammaOneThree k)) :
    Submodule ℂ (BinaryAdelicGL → ℂ) :=
  Submodule.span ℂ {φ | ∃ f ∈ S, ∃ u : BinaryFiniteGL, φ = fun x => adelicLift f (x * atFinite u)}

/-- The functions of `liftSpan S` invariant under right translation by `U`. -/
def levelSubmodule {k : ℤ} (S : Set (CuspForm binaryRealGammaOneThree k))
    (U : Subgroup BinaryFiniteGL) : Submodule ℂ (BinaryAdelicGL → ℂ) where
  carrier := {φ | φ ∈ liftSpan S ∧ ∀ u ∈ U, (fun x => φ (x * atFinite u)) = φ}
  add_mem' := by
    rintro φ ψ ⟨hφ, hφU⟩ ⟨hψ, hψU⟩
    refine ⟨Submodule.add_mem _ hφ hψ, fun u hu => ?_⟩
    funext x
    simp only [Pi.add_apply]
    exact congrArg₂ (· + ·) (congrFun (hφU u hu) x) (congrFun (hψU u hu) x)
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c φ ⟨hφ, hφU⟩
    refine ⟨Submodule.smul_mem _ c hφ, fun u hu => ?_⟩
    funext x
    simp only [Pi.smul_apply]
    exact congrArg (c • ·) (congrFun (hφU u hu) x)

/-- Finite dimensionality of the level subspaces of `liftSpan S` for open compact levels. -/
def LiftLevelFinite {k : ℤ} (S : Set (CuspForm binaryRealGammaOneThree k)) : Prop :=
  ∀ U : Subgroup BinaryFiniteGL, IsOpen (U : Set BinaryFiniteGL) →
    IsCompact (U : Set BinaryFiniteGL) → FiniteDimensional ℂ (levelSubmodule S U)

end TernaryPeriodPolynomials.Regularity

end
