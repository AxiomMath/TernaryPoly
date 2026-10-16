module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Classical
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Eigen
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineUniformDecay
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.ParityBoundary

@[expose] public section


/-!
# Nonvanishing of the arithmetic period class of the Eichler cocycle

For a spherical cohomological cuspidal datum there is an Eichler input `I` (a Hecke eigenvector) such
that the class of the arithmetic period cocycle `γ ↦ I.eichlerCocycle γ_∞ 1` in
`H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) (-1))` is nonzero: the cocycle is the classical
Eichler–Shimura cocycle of a nonzero level one Hecke eigenform of weight `n + 3`
(`arithmeticPeriodCocycle_eq_classical`), whose class is nonzero by the classical period theory.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

/-- **The arithmetic period class of a suitable Eichler input is nonzero.** -/
theorem exists_eichlerInput_period_ne_zero (σ : CuspidalRepresentation) (spherical : SphericalCusp σ)
    {n : ℕ} (odd : Odd n) (cohomological : Cohomological σ n)
    (stages : AnalyticScalar.ContinuousStages σ) :
    ∃ I : EichlerInput σ n,
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) (I.arithmeticPeriodCocycle stages) ≠ 0 := by
  obtain ⟨I, form, eigenvalues, form_ne, hform, relations⟩ :=
    exists_eichlerInput_eigenform σ spherical odd cohomological
  refine ⟨I, ?_⟩
  have weight_eq : -2 * I.halfWeight = ((n + 1 : ℕ) : ℤ) + 2 := by
    have := I.weight
    omega
  have even : Even (n + 1) := by
    obtain ⟨half, equality⟩ := odd
    exact ⟨half + 1, by omega⟩
  rw [I.arithmeticPeriodCocycle_eq_classical stages hform weight_eq even]
  exact classicalArithmeticCocycle_H1_ne_zero form form_ne eigenvalues relations (n + 1) weight_eq even
    (-1) 1 periodSign_eq

/-- **The arithmetic period class for an inducing datum.**  For `D` with spherical cuspidal part and
`n` odd, there is an Eichler input on `D.cusp` whose arithmetic period cocycle
`γ ↦ I.eichlerCocycle γ_∞ 1` represents a nonzero class of
`H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) (-1))`. -/
theorem exists_eichlerInput_period_ne_zero_of_inducing {n : ℕ} (D : InducingData n)
    (spherical : SphericalCusp D.cusp) (odd : Odd n) :
    ∃ (I : EichlerInput D.cusp n) (stages : AnalyticScalar.ContinuousStages D.cusp),
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) (I.arithmeticPeriodCocycle stages) ≠ 0 := by
  obtain ⟨I, nonzero⟩ := exists_eichlerInput_period_ne_zero D.cusp spherical odd D.cohomological
    (AnalyticClasses.continuousStages D)
  exact ⟨I, AnalyticClasses.continuousStages D, nonzero⟩

/-- **An Eichler cocycle with nonzero arithmetic period class.**  The cocycle `α` is in the format of
`IsEichlerCocycle` (hence packages as the Levi cocycle data of the plane source construction), and its
evaluation `γ ↦ α γ_∞ 1` on `GL₂(ℤ)` is a one-cocycle `φ` of `arithmeticBinaryRep (n + 1) (-1)` with
nonzero class. -/
theorem exists_isEichlerCocycle_period_ne_zero (σ : CuspidalRepresentation)
    (spherical : SphericalCusp σ) {n : ℕ} (odd : Odd n) (cohomological : Cohomological σ n)
    (stages : AnalyticScalar.ContinuousStages σ) :
    ∃ α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      IsEichlerCocycle σ n α ∧
      ∃ φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)),
        (∀ γ : GeneralLinearGroup (Fin 2) ℤ,
          φ γ = α (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) 1) ∧
        groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0 := by
  obtain ⟨I, nonzero⟩ := exists_eichlerInput_period_ne_zero σ spherical odd cohomological stages
  exact ⟨I.eichlerCocycle, I.eichlerCocycle_spec stages, I.arithmeticPeriodCocycle stages,
    fun γ => rfl, nonzero⟩

/-- **The same for an inducing datum.** -/
theorem exists_isEichlerCocycle_period_ne_zero_of_inducing {n : ℕ} (D : InducingData n)
    (spherical : SphericalCusp D.cusp) (odd : Odd n) :
    ∃ α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      IsEichlerCocycle D.cusp n α ∧
      ∃ φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)),
        (∀ γ : GeneralLinearGroup (Fin 2) ℤ,
          φ γ = α (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) 1) ∧
        groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0 :=
  exists_isEichlerCocycle_period_ne_zero D.cusp spherical odd D.cohomological
    (AnalyticClasses.continuousStages D)

end TernaryPeriodPolynomials.SourceConstruction

end
