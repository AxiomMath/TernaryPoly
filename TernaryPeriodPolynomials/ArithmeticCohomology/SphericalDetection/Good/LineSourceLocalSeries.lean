module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteLocalSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineMixedSourceVector {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) (real : ℝ × ℝ) : data.cusp.smooth :=
  cuspidalTensorFunctional data.cusp functional
    (goodLineMixedCuspidalValues data source cocycle matrix (atInfinity (standardGoodLineRealArgument real)))

theorem goodLineMixedSourceVector_spherical {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) (real : ℝ × ℝ) :
    (goodLineMixedSourceVector data source cocycle matrix functional real).val ∈ cuspSphericalValues data.cusp :=
  goodLineMixedCuspidalValues_functional_spherical data source cocycle matrix (standardGoodLineRealArgument real) functional

theorem goodLineMixedSourceVector_finite_integrable {degree : ℕ}
    (local_entry : LocalBadPlaneEntry) (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (flat standard : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (source vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (standard parameter vertices argument).val.coeff monomial))
    (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      ∀ᵐ real : ℝ × ℝ ∂((volume : Measure ℝ).prod volume),
        Integrable (fun finite => standardGoodLineFiniteCuspWeight degree parameter finite *
          data.cusp.realize (goodLineMixedSourceVector data source cocycle matrix functional real)
            (atFinite (standardGoodLineFiniteCoordinates finite).block))
          (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  have endpoint_support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (flat cohomologicalPoint vertices argument).val.coeff monomial) := by
    rw [endpoint]
    exact support
  obtain ⟨_, threshold, formula⟩ := goodLineMixedRealCoordinate_continuation local_entry data flat standard
    sections endpoint_support continuations matrix functional
  refine ⟨threshold, ?_⟩
  intro parameter beyond
  have slices := (goodLineMixedAway_cuspidalFinite_fubini data trivial source cocycle flat sections endpoint
    parameter matrix functional (formula parameter beyond).1).2.1
  simpa only [goodLineMixedSourceVector, cuspidalTensorFunctional_realize] using slices

theorem goodLineFiniteExponent_convergent (degree : ℕ) (parameter : ℂ) (positive : 0 < parameter.re) :
    2 < ((degree : ℂ) / 2 + 3 + parameter).re := by
  have degree_nonnegative : (0 : ℝ) ≤ degree := Nat.cast_nonneg degree
  have real_exponent : ((degree : ℂ) / 2 + 3 + parameter).re = (degree : ℝ) / 2 + 3 + parameter.re := by
    norm_num [Complex.add_re, Complex.div_re]
  rw [real_exponent]
  linarith

theorem goodLineMixedSource_local_series {degree : ℕ}
    (local_entry : LocalBadPlaneEntry) (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (flat standard : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (source vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (standard parameter vertices argument).val.coeff monomial))
    (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) (place : FinitePlace) (distinct : place ≠ placeThree) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      ∀ᵐ real : ℝ × ℝ ∂((volume : Measure ℝ).prod volume),
        goodLineFiniteVectorIntegral degree data.cusp parameter
          (goodLineMixedSourceVector data source cocycle matrix functional real) =
          ∫ awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place,
            let vector := goodLineMixedSourceVector data source cocycle matrix functional real
            let base := (standardGoodLineFinitePadicCoordinates (awayPair.1.val, awayPair.2.val)).block
            normPower (GeneralLinearGroup.det (atFinite base)) ((degree : ℂ) / 2 + 3 + parameter) *
              (data.cusp.realize vector (atFinite base) + ∑' power,
                padicPrimitiveSeriesTerm (padicNormPowerWeight ((degree : ℂ) / 2 + 3 + parameter))
                  (cuspLocalPadicValue data.cusp vector base place) power)
            ∂((finiteAwayThreePlaceMeasure place).prod (finiteAwayThreePlaceMeasure place)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  obtain ⟨threshold, integrable⟩ := goodLineMixedSourceVector_finite_integrable local_entry data trivial source cocycle
    flat standard sections endpoint support continuations matrix functional
  refine ⟨max threshold 0, ?_⟩
  intro parameter beyond
  have positive : 0 < parameter.re := (le_max_right threshold 0).trans_lt beyond
  filter_upwards [integrable parameter ((le_max_left threshold 0).trans_lt beyond)] with real slice
  exact goodLineFiniteVectorIntegral_local_series degree data.cusp parameter _
    (goodLineMixedSourceVector_spherical data source cocycle matrix functional real)
    (goodLineFiniteExponent_convergent degree parameter positive) place distinct slice

end TernaryPeriodPolynomials.SphericalDetection.Helpers
