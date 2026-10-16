module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.StandardConv.Related
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.HalfPlaneContinuation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.Uniqueness

@[expose] public section


/-!
# Uniqueness of the standard line cocycle along `RelatedConv`

`RelatedConv data plane line` gives some flat extension `F` of `plane` and some half-plane standard family `J` with
`J(s₀) = line`, analytic at `s₀ = -3/2`.  Then:

* `standardConvergent_eq_at`: two half-plane standard families of the same family `F` which are analytic at `s₀` agree
  at `s₀` (identity theorem for meromorphic functions on the connected half plane `-d/2 < Re s`, on which both are
  meromorphic and where both equal the absolutely convergent standard integral for `Re s` large;
  `HalfPlaneContinuation.meromorphic_eq_at_in_halfPlane`);
* `relatedConv_line_eq_sourceStandard`: the line cocycle of `RelatedConv` is the convergent `sourceStandard`: the flat
  extension is determined by its value at `s₀` (`polynomialFlatSection_eq_of_endpoint`) and the previous item applies
  to each coefficient;
* `realizesStandardConv_apply_eq_sourceStandard`: for any linear map `standard` with `RealizesStandardConv`, the image
  of the class of a plane source `c` is the class of `sourceStandard c`.

No continuation theorem for Eisenstein series is used: only the identity theorem on a half plane.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.StandardConv

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

/-- **Two half-plane standard families of the same family agree at the cohomological point** whenever both are analytic
there (degree `d ≥ 4`, so that `s₀ = -3/2` lies in `-d/2 < Re s`). -/
theorem standardConvergent_eq_at {d : ℕ} (hd : 4 ≤ d) {F J₁ J₂ : ℂ → AdelicGL → ℂ}
    (h₁ : IsStandardConvergent d F J₁) (h₂ : IsStandardConvergent d F J₂) (g : AdelicGL)
    (a₁ : AnalyticAt ℂ (fun s => J₁ s g) cohomologicalPoint)
    (a₂ : AnalyticAt ℂ (fun s => J₂ s g) cohomologicalPoint) :
    J₁ cohomologicalPoint g = J₂ cohomologicalPoint g := by
  obtain ⟨m₁, R₁, i₁⟩ := h₁
  obtain ⟨m₂, R₂, i₂⟩ := h₂
  have inside : -(d : ℝ) / 2 < cohomologicalPoint.re := by
    have : (4 : ℝ) ≤ d := by exact_mod_cast hd
    norm_num [cohomologicalPoint]
    linarith
  exact TernaryPeriodPolynomials.SphericalDetection.Helpers.meromorphic_eq_at_in_halfPlane
    (first := fun s => J₁ s g) (second := fun s => J₂ s g) (-(d : ℝ) / 2) (m₁ g) (m₂ g) (max R₁ R₂)
    (fun s hs _ => by
      rw [(i₁ s (lt_of_le_of_lt (le_max_left _ _) hs) g).2, (i₂ s (lt_of_le_of_lt (le_max_right _ _) hs) g).2])
    cohomologicalPoint inside a₁ a₂

/-- **The line cocycle of a `RelatedConv` pair is the convergent standard cocycle.** -/
theorem relatedConv_line_eq_sourceStandard {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data) (plane : SourceSpace.sourceCocycles data .plane)
    (line : SourceSpace.sourceCocycles data .line) (h : RelatedConv data plane line) :
    line = EndpointSourceStandard.sourceStandard data large holomorphic plane := by
  obtain ⟨F, J, hflat, hend, hconv, hreg, hline⟩ := h
  obtain ⟨F₀, J₀, hflat₀, hend₀, hconv₀, hreg₀, hline₀⟩ :=
    sourceStandard_relatedConv data large holomorphic plane
  have hF : F = F₀ := TernaryPeriodPolynomials.SphericalDetection.Helpers.polynomialFlatSection_eq_of_endpoint
    data F F₀ hflat hflat₀ (hend.trans hend₀.symm)
  subst hF
  apply Subtype.ext
  rw [← hline, ← hline₀]
  funext vertices argument
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact standardConvergent_eq_at large (hconv vertices monomial) (hconv₀ vertices monomial) argument
    (hreg vertices argument monomial) (hreg₀ vertices argument monomial)

/-- The classes agree (the form requested by P2). -/
theorem relatedConv_sourceClass_line_eq {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data) (plane : SourceSpace.sourceCocycles data .plane)
    (line : SourceSpace.sourceCocycles data .line) (h : RelatedConv data plane line) :
    SourceSpace.sourceClass data .line line =
      SourceSpace.sourceClass data .line (EndpointSourceStandard.sourceStandard data large holomorphic plane) :=
  congrArg _ (relatedConv_line_eq_sourceStandard data large holomorphic plane line h)

/-- **Any `T` realizing the standard operator is `sourceStandard` on classes of plane sources.** -/
theorem realizesStandardConv_apply_eq_sourceStandard {degree : ℕ} (data : InducingData degree)
    (large : 4 ≤ degree) (holomorphic : PlaneEisensteinConvergent data)
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (hstd : RealizesStandardConv data standard) (plane : SourceSpace.sourceCocycles data .plane) :
    standard (SourceQuotient.sourceToSummand data .plane plane) =
      SourceQuotient.sourceToSummand data .line
        (EndpointSourceStandard.sourceStandard data large holomorphic plane) := by
  obtain ⟨line, related, value⟩ := (realizesStandardConv_iff data standard).mp hstd plane
  exact value.trans (congrArg (SourceQuotient.sourceToSummand data .line)
    (relatedConv_line_eq_sourceStandard data large holomorphic plane line related))

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.StandardConv
