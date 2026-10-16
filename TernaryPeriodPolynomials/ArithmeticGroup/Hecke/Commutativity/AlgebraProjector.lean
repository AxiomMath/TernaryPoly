module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AllCorrespondences
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.IsotypicalUnique

@[expose] public section


/-!
# Projectors in the away-from-three Hecke algebra are isotypical

Since every element of `awayThreeHeckeAlgebra D hecke` commutes with every pair
Hecke operator (`awayThreeHeckeAlgebra_commute_pairHecke`), an element of that
algebra which is a projection onto `associatePair D` is *the* isotypical
projection: it is isotypical, and every isotypical projection equals it.

Thus the existence-and-uniqueness statement of `cuspidal_associate_projector`
follows from the existence of a spectral projector onto the associate pair inside
the away-from-three Hecke algebra.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.HeckeCommutativity

theorem isIsotypicalProjection_of_mem_awayThree {n : ℕ} (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    {e : Module.End ℂ (BoundaryCoordinates n D.chi)} (he : e ∈ awayThreeHeckeAlgebra D hecke)
    (hrange : LinearMap.range e = associatePair D) (hid : ∀ x ∈ associatePair D, e x = x) :
    IsIsotypicalProjection D hecke e :=
  ⟨hrange, hid, fun t => (awayThreeHeckeAlgebra_commute_pairHecke D hecke hhecke he t).eq⟩

/-- A spectral projector in the away-from-three algebra is the unique isotypical
projection. -/
theorem existsUnique_isotypical_of_mem_awayThree {n : ℕ} (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    {e : Module.End ℂ (BoundaryCoordinates n D.chi)} (he : e ∈ awayThreeHeckeAlgebra D hecke)
    (hrange : LinearMap.range e = associatePair D) (hid : ∀ x ∈ associatePair D, e x = x) :
    ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
      IsIsotypicalProjection D hecke p ∧ ∀ p', IsIsotypicalProjection D hecke p' → p' = p := by
  have hiso := isIsotypicalProjection_of_mem_awayThree D hecke hhecke he hrange hid
  exact ⟨e, hiso, fun p' hp' =>
    TernaryPeriodPolynomials.HeckeStability.isotypicalProjection_unique_of_mem hiso he hp'⟩

end TernaryPeriodPolynomials.HeckeCommutativity
