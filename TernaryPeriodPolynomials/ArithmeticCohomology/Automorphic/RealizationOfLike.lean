module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.SubRepresentation
public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Space

@[expose] public section


/-!
# Realizations from cuspidal-like function spaces

A linear, injective, right-equivariant map from the smooth vectors of a unitary representation
`π` of `GL₂(𝔸)` into functions satisfying N4's four scalar fields `IsCuspidalLike χ` (left
rationality, central character, boundedness, cuspidality) and the archimedean analyticity
`scalarSmooth` is a `SubRepresentation.Realization`.  What remains for the automorphic
construction is therefore exactly: the map itself, injectivity, equivariance, the
archimedean analyticity of its values, and membership of its values in `IsCuspidalLike χ`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic.SmoothVectors
open TernaryPeriodPolynomials.Automorphic.SubRepresentation
open TernaryPeriodPolynomials.CuspIntegral

namespace TernaryPeriodPolynomials.Automorphic.RealizationOfLike

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : Representation ℂ BinaryAdelicGL H}

/-- Assemble a `Realization` from a map into `IsCuspidalLike χ` functions. -/
def ofLike {hu : ∀ g v, ‖π g v‖ = ‖v‖} (χ : Adelesˣ →* ℂ) (hχ : ∀ t, ‖χ t‖ = 1)
    (R : smoothSubmodule π →ₗ[ℂ] (BinaryAdelicGL → ℂ))
    (injective : Function.Injective R)
    (equivariant : ∀ g (v : smoothSubmodule π) x,
      R ⟨π g v.val, smooth_stable hu g v.property⟩ x = R v (x * g))
    (like : ∀ v, IsCuspidalLike χ (R v))
    (scalarSmooth : ∀ v g, Smooth (fun x : Fin 1 → BinaryRealGL => R v (g * atInfinity (x 0)))) :
    Realization π hu where
  realize := R
  injective := injective
  equivariant := equivariant
  centralCharacter := χ
  centralUnitary := hχ
  central t v x := (like v).central t x
  leftRational γ v x := (like v).leftRational γ x
  scalarSmooth := scalarSmooth
  bounded v := (like v).bounded
  cuspidal v g := (like v).cuspidal g

end TernaryPeriodPolynomials.Automorphic.RealizationOfLike
