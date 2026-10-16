module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Main
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceBridge

@[expose] public section


/-!
# Levi cocycle data with nonzero arithmetic period class

The Eichler cocycle packaged as the Levi cocycle data of the plane source construction
(`LeviCocycleData.ofEichler`) restricts, on `GL₂(ℤ)` and at the identity adele, to a one-cocycle `φ` of
`arithmeticBinaryRep (n + 1) (-1)` with nonzero cohomology class.  This is the hypothesis of the
detection of the identity plane coordinate.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- **Levi cocycle data with a nonzero arithmetic period class.** For an inducing datum with spherical
cuspidal part and `n` odd there are Levi cocycle data `E` and a one-cocycle `φ` of `GL₂(ℤ)` in
`arithmeticBinaryRep (n + 1) (-1)` with `φ γ = E.α γ_∞ 1` and `[φ] ≠ 0`. -/
theorem exists_leviCocycleData_period_ne_zero {n : ℕ} (D : InducingData n)
    (spherical : SphericalCusp D.cusp) (odd : Odd n) :
    ∃ (E : LeviCocycleData D.cusp n)
      (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1))),
      (∀ m : GeneralLinearGroup (Fin 2) ℤ,
        φ m = E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1) ∧
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0 := by
  obtain ⟨α, hα, φ, hφ, nonzero⟩ :=
    exists_isEichlerCocycle_period_ne_zero_of_inducing D spherical odd
  exact ⟨LeviCocycleData.ofEichler hα, φ, hφ, nonzero⟩

end TernaryPeriodPolynomials.SourceConstruction

end
