/-
  Consequence of the completed source-cocycle closure: Hecke-stability of the
  associate pair, and the resulting reduction of the existence clause of the
  target to the Hecke-stable complement, with the source-closure hypothesis
  replaced by the level-normalizer condition.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SourceClosureAssembly
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HeckeStability
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.AssociatePairExistence
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.StableComplement
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.StabilizerAdjoin

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.HeckeStabilityAssembly

variable {n : ℕ} {D : InducingData n}


/-- **Per-side Hecke-stability of the boundary summand** from the completed
source closure. -/
theorem boundarySummand_hecke_stable
    (t : HeckeCorrespondence) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hnorm : ∀ r ∈ t.representatives, ∀ k : finiteLevel,
      (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel)
    (side : Side) :
    ∀ a ∈ boundarySummand D side, hecke side t a ∈ boundarySummand D side :=
  HeckeStability.boundarySummand_hecke_stable t hecke hhecke
    (fun _ _ hc => SourceClosureAssembly.translateSource_isSourceCocycle t hc hnorm) side

/-- **Hecke-stability of the associate pair** from the completed source closure. -/
theorem associatePair_hecke_stable
    (t : HeckeCorrespondence) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hnorm : ∀ r ∈ t.representatives, ∀ k : finiteLevel,
      (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel) :
    ∀ y ∈ associatePair D, pairHecke D hecke t y ∈ associatePair D :=
  HeckeStability.associatePair_hecke_stable t hecke hhecke
    (fun _ _ hc => SourceClosureAssembly.translateSource_isSourceCocycle t hc hnorm)

/-- **Existence reduction without a source-closure hypothesis.**  If every Hecke
correspondence's representatives normalize the level and the associate pair has
a Hecke-stable complement, then an isotypical projection exists. -/
theorem exists_isotypicalProjection_of_complement
    (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hnorm : ∀ t : HeckeCorrespondence, ∀ r ∈ t.representatives, ∀ k : finiteLevel,
      (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel)
    (hcompl : ∃ S' : Submodule ℂ (BoundaryCoordinates n D.chi),
      IsCompl (associatePair D) S' ∧
      ∀ t, ∀ x ∈ S', pairHecke D hecke t x ∈ S') :
    ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D hecke p :=
  AssociatePairExistence.exists_isotypicalProjection_of_stable_complement hecke
    (fun t => associatePair_hecke_stable t hecke hhecke (hnorm t)) hcompl


/-- **Existence is equivalent to the Hecke-stable complement.**  With the
associate pair's Hecke-stability automatic, the existence of an isotypical
projection is equivalent to the existence of a Hecke-stable complement of the
associate pair. -/
theorem exists_isotypicalProjection_iff_complement
    (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hnorm : ∀ t : HeckeCorrespondence, ∀ r ∈ t.representatives, ∀ k : finiteLevel,
      (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel) :
    (∃ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D hecke p) ↔
      (∃ S' : Submodule ℂ (BoundaryCoordinates n D.chi),
        IsCompl (associatePair D) S' ∧
        ∀ t, ∀ x ∈ S', pairHecke D hecke t x ∈ S') := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨S', hcompl, hstab⟩ :=
      StableComplement.exists_stable_complement_of_invariant_projection
        (associatePair D) (Set.range (fun t => pairHecke D hecke t)) p
        hp.1 hp.2.1 (fun A hA => by obtain ⟨t, rfl⟩ := hA; exact hp.2.2 t)
    exact ⟨S', hcompl, fun t x hx => hstab (pairHecke D hecke t) ⟨t, rfl⟩ x hx⟩
  · rintro ⟨S', hcompl, hstab⟩
    exact exists_isotypicalProjection_of_complement hecke hhecke hnorm ⟨S', hcompl, hstab⟩


/-- **Invariance under the generated Hecke algebra.**  Every element of
`Algebra.adjoin ℂ (Set.range (pairHecke D hecke ·))` preserves the associate pair
(for a level-normalizing Hecke action). -/
theorem associatePair_adjoin_invariant
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hnorm : ∀ t : HeckeCorrespondence, ∀ r ∈ t.representatives, ∀ k : finiteLevel,
      (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel)
    (h : Module.End ℂ (BoundaryCoordinates n D.chi))
    (hh : h ∈ Algebra.adjoin ℂ (Set.range (fun t : HeckeCorrespondence => pairHecke D hecke t)))
    {x : BoundaryCoordinates n D.chi} (hx : x ∈ associatePair D) :
    h x ∈ associatePair D :=
  StabilizerAdjoin.mem_adjoin_invariant (associatePair D)
    (Set.range (fun t : HeckeCorrespondence => pairHecke D hecke t))
    (fun f hf x hx => by
      obtain ⟨t, rfl⟩ := hf
      exact associatePair_hecke_stable t hecke hhecke (hnorm t) x hx)
    h hh hx

end TernaryPeriodPolynomials.HeckeTranslate.HeckeStabilityAssembly

end
