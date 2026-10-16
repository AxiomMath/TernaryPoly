module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Regular

@[expose] public section


/-!
# The Eichler cocycle of a holomorphic lowest-weight vector

Headline statement of the Eichler construction: for a spherical cuspidal representation `σ`
carrying a nonzero holomorphic lowest-weight vector of weight `-(n + 3)` (as supplied by
`cohomological_exists_spherical_holomorphic`), there is a `GL₂(ℝ)`-cocycle with values in the
`Sym^{n+1}`-valued cusp functions, in the format of `GeneralEisenstein.Cohomological`, which

* vanishes on the orthogonal group,
* has explicit smooth lifts into the smooth vectors of `σ` (all spherical),
* has real-analytic scalar coefficients at every adelic point,
* is right invariant under `GL₂(Ẑ)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

/-- The properties of an Eichler cocycle `α`: the cocycle identity for the twisted action, the
vanishing on orthogonal matrices, cuspidal values with explicit smooth spherical lifts, scalar
real-analyticity, and right `GL₂(Ẑ)`-invariance. -/
def IsEichlerCocycle (σ : CuspidalRepresentation) (n : ℕ)
    (α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) : Prop :=
  (∀ g h x, α (g * h) x = α g x + binaryCohomologicalAction n g (α h) x) ∧
  (∀ k : BinaryRealGL, k.val.transpose * k.val = 1 → ∀ x, α k x = 0) ∧
  (∀ g, BinaryValues σ n (α g)) ∧
  (∀ m : Fin 2 →₀ ℕ, ∃ v : BinaryRealGL → σ.smooth,
    Smooth (fun x : Fin 1 → BinaryRealGL => (v (x 0)).val) ∧
    (∀ g A, σ.realize (v g) A = (α g A).val.coeff m) ∧
    (∀ g, (v g).val ∈ cuspSphericalValues σ)) ∧
  (∀ (A : BinaryAdelicGL) (m : Fin 2 →₀ ℕ),
    Smooth (fun x : Fin 1 → BinaryRealGL => (α (x 0) A).val.coeff m)) ∧
  (∀ (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (g : BinaryRealGL) (x : BinaryAdelicGL),
    α g (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) = α g x)

/-- **The Eichler cocycle exists** for every Eichler input. -/
theorem exists_eichlerCocycle {σ : CuspidalRepresentation} {n : ℕ}
    (stages : AnalyticScalar.ContinuousStages σ) (D : EichlerInput σ n) :
    ∃ α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      IsEichlerCocycle σ n α :=
  ⟨D.eichlerCocycle, D.eichlerCocycle_spec stages⟩

/-- **The Eichler cocycle exists** for every spherical cuspidal representation with a nonzero
cohomology class of odd degree. -/
theorem exists_eichlerCocycle_of_cohomological (σ : CuspidalRepresentation)
    (spherical : SphericalCusp σ) {n : ℕ} (odd : Odd n) (cohomological : Cohomological σ n)
    (stages : AnalyticScalar.ContinuousStages σ) :
    ∃ α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      IsEichlerCocycle σ n α := by
  obtain ⟨D⟩ := EichlerInput.nonempty_of_cohomological σ spherical odd cohomological
  exact exists_eichlerCocycle stages D

end TernaryPeriodPolynomials.SourceConstruction

end
