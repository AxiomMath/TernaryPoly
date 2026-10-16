module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.CosetSum
public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.HolAnti

@[expose] public section


/-!
# Green's formula with `DifferentiableOn` hypotheses

`stokes_ha`: `stokes_holAnti` for families holomorphic on the upper half plane, with `deriv` as derivatives.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

/-- The upper half plane as a subset of `ℂ`. -/
abbrev Uset : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_Uset : IsOpen Uset := isOpen_upperHalfPlaneSet

section Stokes

variable {ι : Type} [Fintype ι] {u w : ι → ℂ → ℂ}

theorem hasDerivAt_of_diffOn {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Uset) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt f (deriv f z) z :=
  ((hf z hz).differentiableAt (isOpen_Uset.mem_nhds hz)).hasDerivAt

theorem continuousOn_deriv_of_diffOn {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Uset) :
    ContinuousOn (deriv f) Uset :=
  ((DifferentiableOn.analyticOnNhd hf isOpen_Uset).deriv).continuousOn

/-- Green's formula for `Σ uᵢ · conj wᵢ` with holomorphic `uᵢ, wᵢ`, using `deriv` for the derivatives. -/
theorem stokes_ha (hu : ∀ i, DifferentiableOn ℂ (u i) Uset) (hw : ∀ i, DifferentiableOn ℂ (w i) Uset)
    (hper : ∀ z : ℂ, 0 < z.im → holAnti u w (z + 1) = holAnti u w z)
    (hS : ∀ z : ℂ, 0 < z.im → holAnti u w (-1 / z) = conj z ^ 2 * holAnti u w z)
    {T : ℝ} (hT : 1 ≤ T) :
    ∫ x in (-1 / 2 : ℝ)..(1 / 2), ∫ y in arcY x..T,
        holAntiD w (fun i => deriv (u i)) ((x : ℂ) + (y : ℂ) * Complex.I) =
      -(Complex.I / 2) * ∫ x in (-1 / 2 : ℝ)..(1 / 2), holAnti u w ((x : ℂ) + (T : ℂ) * Complex.I) :=
  stokes_holAnti (du := fun i => deriv (u i)) (dw := fun i => deriv (w i))
    (fun i _ hz => hasDerivAt_of_diffOn (hu i) hz) (fun i _ hz => hasDerivAt_of_diffOn (hw i) hz)
    (fun i => continuousOn_deriv_of_diffOn (hu i)) (fun i => continuousOn_deriv_of_diffOn (hw i))
    hper hS hT

end Stokes

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
