module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Sign
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerClassicalTw

@[expose] public section


/-!
# The sign-twisted Eichler cocycle has nonzero arithmetic period class

The sign-twisted Eichler cocycle `D.signEichlerCocycle` (a wrapper over `AxiomCodeTwistedSource`)
evaluated at the identity adele on `GL₂(ℤ)` is the parity-zero, twist-zero arithmetic period cocycle
of the level one cusp form of the Eichler input, whose class in
`H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) 0)` is nonzero
(`TwistedSource.eichlerCocycleTw_class_ne_zero`, valid for every Eichler input).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace EichlerInput

variable {σ : CuspidalRepresentation} {n : ℕ} (D : EichlerInput σ n)

/-- **The sign-twisted period class of an Eichler input is nonzero**: the evaluation of the
sign-twisted Eichler cocycle at the identity adele is a one-cocycle `φ` of `GL₂(ℤ)` in
`arithmeticBinaryRep (n + 1) 0` with nonzero class. -/
theorem signEichlerCocycle_period_class_ne_zero (stages : AnalyticScalar.ContinuousStages σ)
    (odd : Odd n) :
    ∃ φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0),
      (∀ γ : GeneralLinearGroup (Fin 2) ℤ,
        φ γ = D.signEichlerCocycle (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) 1) ∧
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0 := by
  obtain ⟨φ, hφ, nonzero⟩ := TwistedSource.eichlerCocycleTw_class_ne_zero D stages odd
  exact ⟨φ, hφ, nonzero⟩

end EichlerInput

/-- **A sign-twisted Eichler cocycle with nonzero arithmetic period class.** -/
theorem exists_isSignEichlerCocycle_period_ne_zero (σ : CuspidalRepresentation)
    (spherical : SphericalCusp σ) {n : ℕ} (odd : Odd n) (cohomological : Cohomological σ n)
    (stages : AnalyticScalar.ContinuousStages σ) :
    ∃ α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      IsSignEichlerCocycle σ n α ∧
      ∃ φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0),
        (∀ γ : GeneralLinearGroup (Fin 2) ℤ,
          φ γ = α (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) 1) ∧
        groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0 := by
  obtain ⟨D⟩ := EichlerInput.nonempty_of_cohomological σ spherical odd cohomological
  obtain ⟨φ, hφ, nonzero⟩ := D.signEichlerCocycle_period_class_ne_zero stages odd
  exact ⟨D.signEichlerCocycle, D.signEichlerCocycle_spec stages, φ, hφ, nonzero⟩

/-- **The same for an inducing datum.** -/
theorem exists_isSignEichlerCocycle_period_ne_zero_of_inducing {n : ℕ} (D : InducingData n)
    (spherical : SphericalCusp D.cusp) (odd : Odd n) :
    ∃ α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      IsSignEichlerCocycle D.cusp n α ∧
      ∃ φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0),
        (∀ γ : GeneralLinearGroup (Fin 2) ℤ,
          φ γ = α (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) 1) ∧
        groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0 :=
  exists_isSignEichlerCocycle_period_ne_zero D.cusp spherical odd D.cohomological
    (AnalyticClasses.continuousStages D)

end TernaryPeriodPolynomials.SourceConstruction

end
