module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Cocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineUniformDecay
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelOneParity.Helpers

@[expose] public section


/-!
# The plane source cocycle of a spherical cuspidal representation

An Eichler cocycle (`IsEichlerCocycle`) is exactly a `LeviCocycleData`: the abstract `O(2)`-normalized
analytic Levi cocycle consumed by the plane source construction. Hence every spherical cuspidal
datum, for a character trivial on the integral units, carries an actual source cocycle
`planeSource D E` for the plane, which is an element of the space `sourceCocycles D .plane`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.SourceConstruction

/-- An Eichler cocycle, packaged as Levi cocycle data. -/
def LeviCocycleData.ofEichler {σ : CuspidalRepresentation} {n : ℕ}
    {α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (h : IsEichlerCocycle σ n α) : LeviCocycleData σ n where
  α := α
  cocycle := h.1
  orth := h.2.1
  lift μ g := Classical.choose (h.2.2.2.1 μ) g
  lift_realize μ g A := (Classical.choose_spec (h.2.2.2.1 μ)).2.1 g A
  lift_smooth μ := (Classical.choose_spec (h.2.2.2.1 μ)).1
  scalar_smooth μ A := h.2.2.2.2.1 A μ
  spherical μ g := (Classical.choose_spec (h.2.2.2.1 μ)).2.2 g

/-- **A plane source cocycle exists** for every spherical cuspidal datum whose character is trivial
on the integral units. -/
theorem exists_planeSource_isSourceCocycle {n : ℕ} (D : InducingData n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (spherical : SphericalCusp D.cusp) :
    ∃ E : LeviCocycleData D.cusp n, IsSourceCocycle D .plane (planeSource D E) := by
  have odd : Odd n :=
    TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers.cohomological_spherical_odd
      n D.cusp D.cohomological spherical
  obtain ⟨α, hα⟩ := exists_eichlerCocycle_of_cohomological D.cusp spherical odd D.cohomological
    (TernaryPeriodPolynomials.AnalyticClasses.continuousStages D)
  exact ⟨LeviCocycleData.ofEichler hα, planeSource_isSourceCocycle D _ hχ⟩

/-- **A plane source cocycle exists in the space of source cocycles.** -/
theorem exists_planeSource_mem_sourceCocycles {n : ℕ} (D : InducingData n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (spherical : SphericalCusp D.cusp) :
    ∃ E : LeviCocycleData D.cusp n,
      ∃ c ∈ TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace.sourceCocycles
          D .plane, c = planeSource D E := by
  obtain ⟨E, hE⟩ := exists_planeSource_isSourceCocycle D hχ spherical
  exact ⟨E, planeSource D E, hE, rfl⟩

end TernaryPeriodPolynomials.SourceConstruction
