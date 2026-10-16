module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeInterface

@[expose] public section


/-!
# The real good-line transfer on the radical: the objects

On pairs of radical elements the real good-line transfer `t` of the Eichler normal form is a
two-cocycle of `ℝ²` with values in scalar tests. A primitive with `δa = t` on the radical exists
by the radial van Est lemma once the coinvariant (`X₂ⁿ`-coefficient) part of the antisymmetrised
mixed second derivative of `t` at the origin vanishes. This file fixes the pointwise radical
section of the transfer, its mixed derivative at the origin and the coinvariant functional.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The coefficient of `X₂ⁿ`, the coinvariant functional of the real lower radical. -/
def topCoefficient (n : ℕ) : HomogeneousPoly n →ₗ[ℂ] ℂ where
  toFun v := v.val.coeff (Finsupp.single 2 n)
  map_add' _ _ := rfl
  map_smul' _ _ := MvPolynomial.coeff_smul _ _ _

/-- The integrand of the transfer at the radical pair `(e^{Y₁}, e^{Y₂})`. -/
def radicalSection (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (u : ℝ × ℝ) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (Y₁ Y₂ : Fin 2 → ℝ) : ℂ :=
  functional (relativeIntegrand N u (lineRadicalElement Y₁) (lineRadicalElement (Y₁ + Y₂)) h)

/-- The mixed derivative `∂_{Y₁ = eᵢ} ∂_{Y₂ = eⱼ}` at the origin of the radical section. -/
def radicalMixed (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (u : ℝ × ℝ) (i j : Fin 2) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) : ℂ :=
  deriv (fun s : ℝ => deriv (fun r : ℝ =>
    radicalSection N u h functional (s • Pi.single i 1) (r • Pi.single j 1)) 0) 0

/-- The coinvariant part of the antisymmetrised mixed derivative, as an integrand. -/
def radicalObstruction (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (u : ℝ × ℝ) (h : BinaryAdelicGL) : ℂ :=
  radicalMixed N u 0 1 h (topCoefficient n) - radicalMixed N u 1 0 h (topCoefficient n)

end TernaryPeriodPolynomials.AnalyticClasses
