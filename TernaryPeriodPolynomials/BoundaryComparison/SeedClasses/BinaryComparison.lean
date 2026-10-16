module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RadicalLieClass
public import TernaryPeriodPolynomials.ModularForm.Eichler.Basic

@[expose] public section


/-!
# Lemma C.3: the radical class of the seed is the binary cusp-form class

Paper: Lemma C.3 (`ar:lem:seed`): "Its radical class is the binary degree-`n+1` cusp-form
class, up to a nonzero scalar." With `RadicalLieClass` (the class of the radical cochain
`h(τ)𝓑ⁿ(1, -τ)` is the binary form `-(h(τ)/(n+1))(τY - X)^{n+1}`), this file compares with the
library's binary Eichler--Shimura objects `TernaryPoly.BinaryCuspPeriod.periodIntegrand` and
`eichlerIntegral` (level one, `Forms d = CuspForm SL₂(ℤ) (d+2)`): the binary form is
`-(n+1)⁻¹` times the library's period integrand `f(z)(zy - x)^{n+1}`, and `-(n+1)⁻¹` times the
library's Eichler integral is a primitive of it.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial UpperHalfPlane
open scoped UpperHalfPlane

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

open TernaryPeriodPolynomials.Argument TernaryPoly.BinaryCuspPeriod

/-- **Radical class = binary cusp-form class (level one).** For `f ∈ S_{n+3}(SL₂(ℤ))` and
`h = f ∘ ofComplex`, evaluating the radical class of the seed `ω_h` (`radicalContraction`) at
`(X, Y, Z) = (x, y, 0)` gives `-(n+1)⁻¹` times the library's binary period integrand
`f(τ)(τy - x)^{n+1}` of the Eichler–Shimura class. -/
theorem seedRadical_eval_eq_periodIntegrand (n : ℕ) (f : Forms (n + 1)) (p : Fin 5 → ℝ)
    (x y : ℂ) :
    eval ![x, y, 0] (radicalContraction n (seedForm n (fun z => f (ofComplex z)) p 0 2)
        (seedForm n (fun z => f (ofComplex z)) p 1 2)) =
      -(((n : ℂ) + 1)⁻¹ * periodIntegrand f x y (seedTau p)) := by
  rw [seedRadical_contraction]
  simp [periodIntegrand]
  ring

/-- The Eichler integral `-(n+1)⁻¹ ∫ f(z)(zy - x)^{n+1} dz` is a primitive, on the upper half-plane,
of the radical binary form of the seed; hence the radical class and the binary period class have
the same period cocycle up to the scalar `-(n+1)⁻¹` (`eichlerIntegral_translate`,
`eichlerIntegral_neg_inv`). -/
theorem seedRadical_primitive (n : ℕ) (f : Forms (n + 1)) (p : Fin 5 → ℝ) (hp : 0 < p 3)
    (x y : ℂ) :
    HasDerivAt (fun z => -(((n : ℂ) + 1)⁻¹ * eichlerIntegral f x y z))
      (eval ![x, y, 0] (radicalContraction n (seedForm n (fun z => f (ofComplex z)) p 0 2)
        (seedForm n (fun z => f (ofComplex z)) p 1 2))) (seedTau p) := by
  rw [seedRadical_eval_eq_periodIntegrand]
  exact ((eichlerIntegral_hasDerivAt f x y (seedTau p) (by simpa [seedTau] using hp)).const_mul
    (((n : ℂ) + 1)⁻¹)).neg

end TernaryPeriodPolynomials.Argument.SeedC3
