module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Iwasawa.Reduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.MixedEndpointIntegral

@[expose] public section


/-!
# The projected part of the target is a good-line coboundary coordinate

Combining the literal integral at `s = -3/2` (`mixedReal_endpoint_eq_integral`), the Iwasawa reduction
(`integral_mixedFiniteFamily_iwasawa`) and a comparison of the target's mixed coordinate with a
two-coboundary on the good-line stabilizer (as supplied by the codexiom target chain), the integral of
the finite average of the source on the Gram–Schmidt plane-parabolic simplices is the good-line mixed
coordinate of an explicit two-coboundary. This is the form in which the remaining archimedean comparison
has to be carried out: it involves the source only on plane-parabolic simplices.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

theorem goodLineMixedCoordinate_twoBoundary_sub (γ : GeneralLinearGroup (Fin 2) ℤ)
    (first second : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) →
      goodLineCoefficientRep n) :
    goodLineMixedCoordinate n γ (fun pair => twoBoundaryCycle (goodLineCoefficientRep n) (first - second) pair) =
      goodLineMixedCoordinate n γ (fun pair => twoBoundaryCycle (goodLineCoefficientRep n) first pair) -
        goodLineMixedCoordinate n γ (fun pair => twoBoundaryCycle (goodLineCoefficientRep n) second pair) := by
  rw [← map_sub]
  congr 1
  funext pair
  obtain ⟨g, h⟩ := pair
  change twoBoundaryCycle (goodLineCoefficientRep n) (first - second) (g, h) =
    twoBoundaryCycle (goodLineCoefficientRep n) first (g, h) - twoBoundaryCycle (goodLineCoefficientRep n) second (g, h)
  rw [twoBoundaryCycle_apply, twoBoundaryCycle_apply, twoBoundaryCycle_apply, Pi.sub_apply, Pi.sub_apply,
    Pi.sub_apply, map_sub]
  abel

/-- **The projected part of the good-line target is a coboundary coordinate.** -/
theorem projectedAverage_integral_coboundary (large : 9 ≤ n) (local_entry : LocalBadPlaneEntry)
    (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (flat standard : ℂ → SourceCochain n)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (source vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (standard parameter vertices argument).val.coeff monomial))
    (analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (standard parameter vertices argument).val.coeff monomial)
        cohomologicalPoint)
    (primitive : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep n)
    (comparison : ∀ γ : GeneralLinearGroup (Fin 2) ℤ,
      goodLineMixedRealCoordinate n γ (goodLineComplementFamily standard cohomologicalPoint) =
        goodLineMixedCoordinate n γ (fun pair => twoBoundaryCycle (goodLineCoefficientRep n) primitive pair))
    (γ : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    ∫ u, projectedAverage data source cocycle γ functional u ∂((volume : Measure ℝ).prod volume) =
      functional (goodLineMixedCoordinate n γ (fun pair => twoBoundaryCycle (goodLineCoefficientRep n)
        (primitive - prismStabilizerCochain data source cocycle) pair)) := by
  have literal := mixedReal_endpoint_eq_integral large local_entry data trivial source cocycle flat standard
    sections endpoint support continuations analytic γ functional
  have reduction := integral_mixedFiniteFamily_iwasawa large data trivial source cocycle γ functional
  rw [comparison] at literal
  have literal' : ∫ u, mixedFiniteFamily data source cocycle γ functional cohomologicalPoint u
      ∂((volume : Measure ℝ).prod volume) =
      functional (goodLineMixedCoordinate n γ (fun pair => twoBoundaryCycle (goodLineCoefficientRep n) primitive pair)) :=
    literal.symm
  rw [goodLineMixedCoordinate_twoBoundary_sub, map_sub, ← literal', reduction]
  ring

end TernaryPeriodPolynomials.AnalyticClasses
