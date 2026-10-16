/-
  Source-cocycle closure of the finite-coset Hecke translate.

  All four clauses of `IsSourceCocycle (translateSource D t c)` are proved
  outright (under the level-normalizer condition): clause (a) via
  `TranslateIsInduced`, clause (b) via `TranslateHasSmoothCuspLift`, clause (c)
  via `RepresentativeInvariance`, and clause (d) via `HeckeInvariance`.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.IsInduced
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HasSmoothCuspLift
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.RepresentativeInvariance
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HeckeInvariance

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Homogeneous MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.SourceClosureAssembly

variable {n : ℕ} {D : InducingData n}

/-- **Source-cocycle closure of `translateSource`.**  If the representatives
normalize the congruence level, the finite-coset Hecke translate of a source
cocycle is again a source cocycle. -/
theorem translateSource_isSourceCocycle {side : Side}
    (t : HeckeCorrespondence) {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (hnorm : ∀ r ∈ t.representatives, ∀ k : finiteLevel,
      (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel) :
    IsSourceCocycle D side (HeckeInvariance.translateSource D t c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x m
    exact TranslateIsInduced.translateSource_isInduced_coeff hc t hnorm x m
  · intro m
    exact TranslateHasSmoothCuspLift.translateSource_hasSmoothCuspLift hc t m
  · intro h x g
    exact RepresentativeInvariance.translateSource_real_equivariant D side t hc h x g
  · intro x g
    exact HeckeInvariance.translateSource_closed D t c (fun x g => hc.2.2.2 x g) x g

end TernaryPeriodPolynomials.HeckeTranslate.SourceClosureAssembly

end
