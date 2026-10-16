/-
  Unconditional reduction of the exact conclusion to the three
  Harder--Raghuram inputs:

  * Hecke-stability of the associate pair `A = boundarySummand D .plane ×
    boundarySummand D .line` under every `pairHecke D hecke t`;
  * existence of a Hecke-invariant complement of `A`;
  * vanishing of the Hecke-equivariant endomorphisms with range in `A` that kill
    `A` (multiplicity one).

  No level-normaliser hypothesis is used: the equivalence is stated for the
  literal `IsIsotypicalProjection`, and the forward direction derives the
  stability from a solution itself.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.AssociatePairExistence
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.Insufficiency

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic


noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.TargetReduction

variable {n : ℕ} {D : InducingData n}

/-- **Forward: a unique isotypical projection yields the three splitting
inputs.** -/
theorem split_of_existsUnique
    (hecke : BoundaryHecke n D.chi) (_hhecke : ActualBoundaryHecke n D.chi hecke)
    (h : ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
      IsIsotypicalProjection D hecke p ∧
      ∀ p', IsIsotypicalProjection D hecke p' → p' = p) :
    (∀ t, ∀ x ∈ associatePair D, pairHecke D hecke t x ∈ associatePair D) ∧
    (∃ S' : Submodule ℂ (BoundaryCoordinates n D.chi),
      IsCompl (associatePair D) S' ∧
      ∀ t, ∀ x ∈ S', pairHecke D hecke t x ∈ S') ∧
    (∀ q : Module.End ℂ (BoundaryCoordinates n D.chi),
      LinearMap.range q ≤ associatePair D →
      (∀ x ∈ associatePair D, q x = 0) →
      (∀ t, q.comp (pairHecke D hecke t) = (pairHecke D hecke t).comp q) → q = 0) := by
  obtain ⟨p, hp, huniq⟩ := h
  have hex : ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D hecke p :=
    ⟨p, hp⟩
  have h1 := (AssociatePairExistence.exists_isotypicalProjection_iff_stable_complement hecke).1 hex
  have h2 := (TernaryPeriodPolynomials.HeckeTranslate.isotypical_unique_iff
    (T := hecke) hex).1 ⟨p, hp, huniq⟩
  exact ⟨h1.1, h1.2, h2⟩

/-- **Backward: the three splitting inputs yield the exact conclusion.** -/
theorem existsUnique_of_split
    (hecke : BoundaryHecke n D.chi) (_hhecke : ActualBoundaryHecke n D.chi hecke)
    (hstable : ∀ t, ∀ x ∈ associatePair D, pairHecke D hecke t x ∈ associatePair D)
    (hcompl : ∃ S' : Submodule ℂ (BoundaryCoordinates n D.chi),
      IsCompl (associatePair D) S' ∧
      ∀ t, ∀ x ∈ S', pairHecke D hecke t x ∈ S')
    (hQ : ∀ q : Module.End ℂ (BoundaryCoordinates n D.chi),
      LinearMap.range q ≤ associatePair D →
      (∀ x ∈ associatePair D, q x = 0) →
      (∀ t, q.comp (pairHecke D hecke t) = (pairHecke D hecke t).comp q) → q = 0) :
    ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
      IsIsotypicalProjection D hecke p ∧
      ∀ p', IsIsotypicalProjection D hecke p' → p' = p := by
  exact (TernaryPeriodPolynomials.HeckeTranslate.isotypical_unique_iff (T := hecke)
    (AssociatePairExistence.exists_isotypicalProjection_of_stable_complement
      hecke hstable hcompl)).2 hQ

/-- **The exact equivalence.**  The conclusion (existence and
uniqueness of the isotypical projection) holds if and only if the associate pair
is Hecke-stable, has a Hecke-invariant complement, and carries no nonzero
Hecke-equivariant endomorphism through it. -/
theorem existsUnique_iff_split
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) :
    (∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
      IsIsotypicalProjection D hecke p ∧
      ∀ p', IsIsotypicalProjection D hecke p' → p' = p) ↔
    (∀ t, ∀ x ∈ associatePair D, pairHecke D hecke t x ∈ associatePair D) ∧
    (∃ S' : Submodule ℂ (BoundaryCoordinates n D.chi),
      IsCompl (associatePair D) S' ∧
      ∀ t, ∀ x ∈ S', pairHecke D hecke t x ∈ S') ∧
    (∀ q : Module.End ℂ (BoundaryCoordinates n D.chi),
      LinearMap.range q ≤ associatePair D →
      (∀ x ∈ associatePair D, q x = 0) →
      (∀ t, q.comp (pairHecke D hecke t) = (pairHecke D hecke t).comp q) → q = 0) :=
  ⟨split_of_existsUnique hecke hhecke, fun h => existsUnique_of_split hecke hhecke h.1 h.2.1 h.2.2⟩



end TernaryPeriodPolynomials.HeckeTranslate.TargetReduction

end
