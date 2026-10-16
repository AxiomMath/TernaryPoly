module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.EndpointPeriodRealize

@[expose] public section


/-!
# The pointwise Eichler normal form of a binary cocycle

For a family `F h z` of functions on the upper half plane indexed by adelic points (in the
application `F = cuspScalarWeightedRealization` of a classical endpoint vector, holomorphic in
`z`), the pointwise Eichler period is the straight-line integral
`Per_F(z)(h) = ∫_i^z F h w (X₀ - w X₁)^{n+1} dw` and the pointwise normal form is
`N_F(A)(h) = ½ (Per_F(A·i)(h) + J · Per_F(-conj(A·i))(h))`, with `J` acting by the cohomological
action. This is the pointwise version of the Hilbert normal form
`½ (Per(A·i) + J Per(refl(A·i)))` of Codexiom's binary detection chain.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The straight path from `i` to `z`. -/
def eichlerPath (z : ℂ) (t : ℝ) : ℂ := Complex.I + t • (z - Complex.I)

/-- The scalar Eichler integrand in the weight-basis coordinate `j`. -/
def eichlerIntegrand (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (z : ℂ) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) (t : ℝ) : ℂ :=
  (z - Complex.I) * F h (eichlerPath z t) *
    (binaryWeightBasis (n + 1)).coord j (binaryPointPower (n + 1) (eichlerPath z t))

/-- **The pointwise Eichler period** `∫_i^z F h w (X₀ - w X₁)^{n+1} dw`. -/
def eichlerPeriod (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (z : ℂ) (h : BinaryAdelicGL) :
    Binary.HomogeneousPoly (n + 1) :=
  ∑ j, (∫ t in (0 : ℝ)..1, eichlerIntegrand n F z h j t) • binaryWeightBasis (n + 1) j

/-- The point `A · i` of the upper half plane. -/
def basePoint (A : BinaryRealGL) : ℂ := ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)

/-- **The pointwise Eichler normal form.** -/
def eichlerNormal (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (A : BinaryRealGL)
    (h : BinaryAdelicGL) : Binary.HomogeneousPoly (n + 1) :=
  (2 : ℂ)⁻¹ • (eichlerPeriod n F (basePoint A) h +
    binaryAmbientRepresentation n UpperHalfPlane.J
      (eichlerPeriod n F (binaryComplexReflection (basePoint A))) h)

theorem eichlerNormal_def (F : BinaryAdelicGL → ℂ → ℂ) (A : BinaryRealGL) (h : BinaryAdelicGL) :
    eichlerNormal n F A h = (2 : ℂ)⁻¹ • (eichlerPeriod n F (basePoint A) h +
      binaryAmbientRepresentation n UpperHalfPlane.J
        (eichlerPeriod n F (binaryComplexReflection (basePoint A))) h) := rfl

end TernaryPeriodPolynomials.AnalyticClasses
