/-
  Hecke-stability of a boundary summand: the algebraic reduction.

  The only missing input for the existence of the associate-pair projection is
  that the Hecke action preserve `boundarySummand`.  This reduces that to a
  single closure property of the *source* cochains: that the adelic finite-coset
  translate `translateSource D t c` of a source cocycle is again a source
  cocycle.  Given that, the exact evaluation comparison
  `HeckeInvariance.evaluates_translate` places the Hecke image of every span
  generator back inside the span.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.AveragedHecke

@[expose] public section



open GeneralEisenstein
open Homogeneous Adelic

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.HeckeStability

variable {n : ℕ} {D : InducingData n}

/-- The generating classes of `boundarySummand`, named so that later rewriting
does not repeatedly unfold the large source-cocycle predicate. -/
def sourceGenerators (n : ℕ) (D : InducingData n) (side : Side) :
    Set (StratumH2 n D.chi side) :=
  {a | ∃ c, IsSourceCocycle D side c ∧ ∃ z, Evaluates D side c z ∧
    a = classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) side) z}

/-- `boundarySummand` is the span of the named generators. -/
theorem boundarySummand_eq_span (D : InducingData n) (side : Side) :
    boundarySummand D side = Submodule.span ℂ (sourceGenerators n D side) := rfl

/-- If the finite-coset translate sends source cocycles to source cocycles, then
the actual Hecke action preserves the boundary summand on every side. -/
theorem boundarySummand_hecke_stable (t : HeckeCorrespondence)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hclosed : ∀ side c, IsSourceCocycle D side c →
      IsSourceCocycle D side (HeckeInvariance.translateSource D t c))
    (side : Side) :
    ∀ a ∈ boundarySummand D side, hecke side t a ∈ boundarySummand D side := by
  intro a ha
  have hmain : Submodule.span ℂ (sourceGenerators n D side) ≤
      (Submodule.span ℂ (sourceGenerators n D side)).comap (hecke side t) := by
    rw [Submodule.span_le]
    rintro b ⟨c, hc, z, heval, rfl⟩
    change (hecke side t) ((classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) side)) z)
        ∈ Submodule.span ℂ (sourceGenerators n D side)
    obtain ⟨z', hz', hclass⟩ := hhecke side t z
    rw [hclass]
    exact Submodule.subset_span
      ⟨HeckeInvariance.translateSource D t c, hclosed side c hc, z',
        HeckeInvariance.evaluates_translate D side t heval hz', rfl⟩
  rw [boundarySummand_eq_span] at ha ⊢
  exact hmain ha

/-- **Closure of the associate pair.**  The same source-closure hypothesis makes
the whole associate pair invariant under every Hecke operator. -/
theorem associatePair_hecke_stable (t : HeckeCorrespondence)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hclosed : ∀ side c, IsSourceCocycle D side c →
      IsSourceCocycle D side (HeckeInvariance.translateSource D t c)) :
    ∀ y ∈ associatePair D, pairHecke D hecke t y ∈ associatePair D := by
  rintro ⟨y1, y2⟩ hy
  rw [associatePair, Submodule.mem_prod] at hy ⊢
  exact ⟨boundarySummand_hecke_stable t hecke hhecke hclosed .plane y1 hy.1,
    boundarySummand_hecke_stable t hecke hhecke hclosed .line y2 hy.2⟩

end TernaryPeriodPolynomials.HeckeTranslate.HeckeStability

end
