module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineMixedCuspidalValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineFiniteCuspIntegral (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (values : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)))
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) : ℂ :=
  ∫ finite : FiniteAwayThree × FiniteAwayThree, standardGoodLineFiniteCuspWeight degree parameter finite *
    functional (values.val (atFinite (standardGoodLineFiniteCoordinates finite).block))
    ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)

def goodLineFiniteVectorIntegral (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) : ℂ :=
  ∫ finite : FiniteAwayThree × FiniteAwayThree, standardGoodLineFiniteCuspWeight degree parameter finite *
    cusp.realize vector (atFinite (standardGoodLineFiniteCoordinates finite).block)
    ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)

theorem goodLineFiniteCuspIntegral_eq_vector (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (values : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)))
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    goodLineFiniteCuspIntegral degree cusp parameter values functional =
      goodLineFiniteVectorIntegral degree cusp parameter (cuspidalTensorFunctional cusp functional values) := by
  apply integral_congr_ae
  filter_upwards [] with finite
  rw [cuspidalTensorFunctional_realize]

def goodLineCuspidalProductIntegrand {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree)) : ℂ :=
  standardGoodLineRealKernel parameter pair.1 *
    (standardGoodLineFiniteCuspWeight degree parameter pair.2 *
      functional ((goodLineMixedCuspidalValues data source cocycle matrix
        (atInfinity (standardGoodLineRealArgument pair.1))).val
          (atFinite (standardGoodLineFiniteCoordinates pair.2).block)))

theorem goodLineMixedAway_cuspidalProduct {degree : ℕ} (data : InducingData degree)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree)) :
    functional (goodLineMixedRealCoordinate degree matrix (fun vertices =>
      standardGoodLineAwayPolynomial flat parameter vertices (awayRadicalJoin pair))) =
      goodLineCuspidalProductIntegrand data source cocycle parameter matrix functional pair := by
  have values : (fun vertices => standardGoodLineAwayPolynomial flat parameter vertices (awayRadicalJoin pair)) =
      (standardGoodLineRealKernel parameter pair.1 * standardGoodLineFiniteCuspWeight degree parameter pair.2) •
        (fun vertices => (sourcePlaneCuspidalValues data source cocycle vertices
          (atInfinity (standardGoodLineRealArgument pair.1))).val
            (atFinite (standardGoodLineFiniteCoordinates pair.2).block)) := by
    funext vertices
    change flat parameter vertices (weyl⁻¹ *
      lineUnipotent (adeleAwayThreeScalar (awayRadicalJoin pair).1) (adeleAwayThreeScalar (awayRadicalJoin pair).2) *
        rationalGroup rationalGoodLine) = _
    exact (congrArg (flat parameter vertices) (standardGoodLineArgument_combine pair.1 pair.2)).trans
      (polynomialFlatSection_standardGoodLine_cuspidal data trivial source cocycle flat sections endpoint
        parameter vertices pair.1 pair.2)
  rw [values, map_smul, map_smul, smul_eq_mul]
  rw [goodLineCuspidalProductIntegrand, goodLineMixedCuspidalValues_apply, mul_assoc]

theorem goodLineMixedAway_cuspidalFinite_fubini {degree : ℕ} (data : InducingData degree)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (integrable : Integrable (fun away => functional (goodLineMixedRealCoordinate degree matrix
      (fun vertices => standardGoodLineAwayPolynomial flat parameter vertices away))) radicalAwayThreeMeasure) :
    Integrable (fun real => standardGoodLineRealKernel parameter real *
      goodLineFiniteCuspIntegral degree data.cusp parameter
        (goodLineMixedCuspidalValues data source cocycle matrix (atInfinity (standardGoodLineRealArgument real))) functional)
      ((volume : Measure ℝ).prod volume) ∧
    (∀ᵐ real : ℝ × ℝ ∂((volume : Measure ℝ).prod volume),
      Integrable (fun finite => standardGoodLineFiniteCuspWeight degree parameter finite *
        functional ((goodLineMixedCuspidalValues data source cocycle matrix
          (atInfinity (standardGoodLineRealArgument real))).val
            (atFinite (standardGoodLineFiniteCoordinates finite).block)))
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) ∧
    (∫ away, functional (goodLineMixedRealCoordinate degree matrix
      (fun vertices => standardGoodLineAwayPolynomial flat parameter vertices away)) ∂radicalAwayThreeMeasure) =
      ∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter real *
        goodLineFiniteCuspIntegral degree data.cusp parameter
          (goodLineMixedCuspidalValues data source cocycle matrix (atInfinity (standardGoodLineRealArgument real))) functional
        ∂((volume : Measure ℝ).prod volume) := by
  have lifted := awayRadicalJoin_measurePreserving.integrable_comp_of_integrable integrable
  have equality : ((fun away => functional (goodLineMixedRealCoordinate degree matrix
      (fun vertices => standardGoodLineAwayPolynomial flat parameter vertices away))) ∘ awayRadicalJoin) =
      goodLineCuspidalProductIntegrand data source cocycle parameter matrix functional := by
    funext pair
    exact goodLineMixedAway_cuspidalProduct data trivial source cocycle flat sections endpoint parameter matrix functional pair
  rw [equality] at lifted
  have inner : (fun real : ℝ × ℝ => ∫ finite,
      goodLineCuspidalProductIntegrand data source cocycle parameter matrix functional (real, finite)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) =
      fun real => standardGoodLineRealKernel parameter real *
        goodLineFiniteCuspIntegral degree data.cusp parameter
          (goodLineMixedCuspidalValues data source cocycle matrix (atInfinity (standardGoodLineRealArgument real))) functional := by
    funext real
    simp only [goodLineCuspidalProductIntegrand, goodLineFiniteCuspIntegral]
    rw [integral_const_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [← inner]
    exact lifted.integral_prod_left
  · filter_upwards [lifted.prod_right_ae] with real slice
    exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (standardGoodLineRealKernel_ne_zero parameter real)) _).mp slice
  · rw [← awayRadicalJoin_measurePreserving.integral_comp awayRadicalJoin.measurableEmbedding]
    change (∫ pair, (((fun away => functional (goodLineMixedRealCoordinate degree matrix
      (fun vertices => standardGoodLineAwayPolynomial flat parameter vertices away))) ∘ awayRadicalJoin) pair)
      ∂(((volume : Measure ℝ).prod volume).prod (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))) = _
    rw [equality, integral_prod _ lifted]
    exact congrArg (fun function : (ℝ × ℝ) → ℂ => ∫ real, function real ∂((volume : Measure ℝ).prod volume)) inner

/-- The standard continuation is the real kernel applied to finite averages of actual spherical cusp vectors. -/
theorem goodLineMixedRealCoordinate_finite_vector_continuation {degree : ℕ}
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
      Integrable (fun real => standardGoodLineRealKernel parameter real *
        goodLineFiniteVectorIntegral degree data.cusp parameter
          (cuspidalTensorFunctional data.cusp functional
            (goodLineMixedCuspidalValues data source cocycle matrix (atInfinity (standardGoodLineRealArgument real)))))
        ((volume : Measure ℝ).prod volume) ∧
      functional (goodLineMixedRealCoordinate degree matrix (goodLineComplementFamily standard parameter)) =
        ∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter real *
          goodLineFiniteVectorIntegral degree data.cusp parameter
            (cuspidalTensorFunctional data.cusp functional
              (goodLineMixedCuspidalValues data source cocycle matrix (atInfinity (standardGoodLineRealArgument real))))
          ∂((volume : Measure ℝ).prod volume) := by
  have endpoint_support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (flat cohomologicalPoint vertices argument).val.coeff monomial) := by
    rw [endpoint]
    exact support
  obtain ⟨_, threshold, formula⟩ := goodLineMixedRealCoordinate_continuation local_entry data flat standard
    sections endpoint_support continuations matrix functional
  refine ⟨threshold, ?_⟩
  intro parameter beyond
  obtain ⟨integrable, value⟩ := formula parameter beyond
  obtain ⟨real_integrable, _, iterated⟩ := goodLineMixedAway_cuspidalFinite_fubini data trivial source cocycle flat
    sections endpoint parameter matrix functional integrable
  rw [iterated] at value
  simpa only [goodLineFiniteCuspIntegral_eq_vector] using And.intro real_integrable value

end TernaryPeriodPolynomials.SphericalDetection.Helpers
