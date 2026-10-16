module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SpectralSeparation.Simultaneous
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AlgebraProjector
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.AwayThreeStability
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.BoundaryDimension

@[expose] public section


/-!
# Spectral projectors onto associate pairs from eigencharacter separation

The away-from-three Hecke algebra is commutative (`awayThreeHeckeAlgebra_commute`).
It preserves `associatePair D` (`associatePair_stable_of_mem_awayThreeHeckeAlgebra`),
and `BoundaryCoordinates` is finite dimensional (`boundary_finiteDimensional`).
Hence eigencharacter separation of `associatePair D` gives a spectral projector
inside the algebra. That projector is then the unique isotypical projection.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.SpectralSeparation

theorem spectral_of_eigenSeparated {n : ℕ} (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hsep : EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D)) :
    ∃ e ∈ awayThreeHeckeAlgebra D hecke,
      LinearMap.range e = associatePair D ∧ ∀ x ∈ associatePair D, e x = x := by
  have := TernaryPeriodPolynomials.BoundaryFiniteness.BoundaryDimension.boundary_finiteDimensional
    n D.chi
  exact exists_spectral_of_separated (awayThreeHeckeAlgebra D hecke)
    (fun f hf g hg =>
      (TernaryPeriodPolynomials.HeckeCommutativity.awayThreeHeckeAlgebra_commute
        D hecke hhecke hf hg).eq)
    (associatePair D)
    (fun f hf => TernaryPeriodPolynomials.HeckeStability.associatePair_stable_of_mem_awayThreeHeckeAlgebra
      hecke hhecke hf)
    hsep

/-- Eigencharacter separation gives the unique isotypical projection. -/
theorem existsUnique_isotypical_of_eigenSeparated {n : ℕ} (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hsep : EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D)) :
    ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
      IsIsotypicalProjection D hecke p ∧ ∀ p', IsIsotypicalProjection D hecke p' → p' = p := by
  obtain ⟨e, he, hrange, hid⟩ := spectral_of_eigenSeparated D hecke hhecke hsep
  exact TernaryPeriodPolynomials.HeckeCommutativity.existsUnique_isotypical_of_mem_awayThree
    D hecke hhecke he hrange hid

/-- Eigencharacter separation puts every isotypical projection in the algebra. -/
theorem mem_awayThree_of_eigenSeparated {n : ℕ} (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hsep : EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D))
    (p : Module.End ℂ (BoundaryCoordinates n D.chi)) (hp : IsIsotypicalProjection D hecke p) :
    p ∈ awayThreeHeckeAlgebra D hecke := by
  have key := spectral_of_eigenSeparated D hecke hhecke hsep
  have he := key.choose_spec.1
  have heiso := TernaryPeriodPolynomials.HeckeCommutativity.isIsotypicalProjection_of_mem_awayThree
    D hecke hhecke he key.choose_spec.2.1 key.choose_spec.2.2
  have hpe : p = key.choose :=
    TernaryPeriodPolynomials.HeckeStability.isotypicalProjection_unique_of_mem heiso he hp
  rw [hpe]
  exact he

end TernaryPeriodPolynomials.SpectralSeparation
