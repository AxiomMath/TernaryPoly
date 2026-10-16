module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteTruncatedProduct

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspLocalPadicEulerFactorAwayThree_hasProd (cusp : CuspidalRepresentation)
    (eigenvalues : FinitePlace → ℂ) (exponent value : ℂ)
    (product : HasProd (fun place : {place : FinitePlace // place ≠ placeThree} =>
      cuspLocalPadicEulerFactor cusp place.val (eigenvalues place.val) exponent) value) :
    HasProd (cuspLocalPadicEulerFactorAwayThree cusp eigenvalues exponent) value := by
  have extended := (hasProd_subtype_iff_mulIndicator
    (s := {place : FinitePlace | place ≠ placeThree})
    (f := fun place => cuspLocalPadicEulerFactor cusp place (eigenvalues place) exponent)).mp product
  apply extended.congr_fun
  intro place
  by_cases same : place = placeThree <;>
    simp [cuspLocalPadicEulerFactorAwayThree, Set.mulIndicator, same]

theorem goodLineFiniteVectorIntegral_eq_eulerProduct (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (convergent : 2 < ((degree : ℂ) / 2 + 3 + parameter).re) (eigenvalues : FinitePlace → ℂ)
    (eigen : ∀ place, place ≠ placeThree → cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalues place • vector)
    (integrable : Integrable (fun finite => standardGoodLineFiniteCuspWeight degree parameter finite *
      cusp.realize vector (atFinite (standardGoodLineFiniteCoordinates finite).block))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))
    (value : ℂ) (product : HasProd (fun place : {place : FinitePlace // place ≠ placeThree} =>
      cuspLocalPadicEulerFactor cusp place.val (eigenvalues place.val) ((degree : ℂ) / 2 + 3 + parameter)) value) :
    goodLineFiniteVectorIntegral degree cusp parameter vector = value * cusp.realize vector 1 := by
  have limit := goodLineFinitePadicTruncatedIntegral_tendsto degree cusp parameter vector spherical integrable
  have extended := cuspLocalPadicEulerFactorAwayThree_hasProd cusp eigenvalues _ value product
  have product_limit : Tendsto (fun places : Finset FinitePlace =>
      ∏ place ∈ places, cuspLocalPadicEulerFactorAwayThree cusp eigenvalues ((degree : ℂ) / 2 + 3 + parameter) place)
      atTop (nhds value) := extended
  have weighted_limit : Tendsto (goodLineFinitePadicTruncatedIntegral cusp vector ((degree : ℂ) / 2 + 3 + parameter))
      atTop (nhds (value * cusp.realize vector 1)) := by
    convert product_limit.mul_const (cusp.realize vector 1) using 1
    funext places
    exact goodLineFinitePadicTruncatedIntegral_product cusp vector nonzero spherical _ convergent eigenvalues eigen
      (goodLineFinitePadicIntegrand_integrable degree cusp parameter vector spherical integrable) places
  exact tendsto_nhds_unique limit weighted_limit

end TernaryPeriodPolynomials.SphericalDetection.Helpers
