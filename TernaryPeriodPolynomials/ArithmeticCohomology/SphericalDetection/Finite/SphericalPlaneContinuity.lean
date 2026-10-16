module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFinitePadicSplitting

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finitePlaneInductionCoordinates_right {matrix : FiniteGL} (coordinates : FinitePlaneInductionCoordinates matrix)
    (compact : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    FinitePlaneInductionCoordinates (matrix * GeneralLinearGroup.map integralEmbedding compact) where
  first := coordinates.first
  second := coordinates.second
  scalar := coordinates.scalar
  block := coordinates.block
  compact := coordinates.compact * compact
  factorization := by
    conv_lhs => rw [coordinates.factorization]
    rw [map_mul]
    simp only [mul_assoc]

def finiteSphericalPlaneFunction (cusp : CuspidalRepresentation) (vector : cusp.smooth) (exponent : ℂ)
    (matrix : FiniteGL) : ℂ :=
  finiteSphericalPlaneValue cusp vector exponent (finitePlaneInductionCoordinates matrix)

theorem finiteSphericalPlaneFunction_right (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (exponent : ℂ) (matrix : FiniteGL)
    (compact : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    finiteSphericalPlaneFunction cusp vector exponent (matrix * GeneralLinearGroup.map integralEmbedding compact) =
      finiteSphericalPlaneFunction cusp vector exponent matrix := by
  exact finiteSphericalPlaneValue_independent cusp vector spherical exponent _
    (finitePlaneInductionCoordinates _) (finitePlaneInductionCoordinates_right (finitePlaneInductionCoordinates matrix) compact)

theorem finiteSphericalPlaneFunction_continuous (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (exponent : ℂ) :
    Continuous (finiteSphericalPlaneFunction cusp vector exponent) := by
  apply continuous_iff_continuousAt.mpr
  intro matrix
  apply Filter.EventuallyEq.continuousAt
  have near : ∀ᶠ other in nhds matrix, matrix⁻¹ * other ∈ finiteIntegralGLLevel 3 :=
    (continuous_const.mul continuous_id).continuousAt.eventually
      ((finiteIntegralGLLevel_isOpen 3).mem_nhds (by
        change matrix⁻¹ * matrix ∈ finiteIntegralGLLevel 3
        rw [inv_mul_cancel]
        exact (finiteIntegralGLLevel 3).one_mem))
  filter_upwards [near] with other member
  obtain ⟨compact, equality⟩ := member
  have factors : other = matrix * GeneralLinearGroup.map integralEmbedding compact := by
    rw [equality, mul_inv_cancel_left]
  rw [factors, finiteSphericalPlaneFunction_right cusp vector spherical]

theorem planeOppositeStandardMatrix_continuous :
    Continuous (fun pair : FiniteAdeles × FiniteAdeles => planeOppositeStandardMatrix pair.1 pair.2) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro row column
    fin_cases row <;> fin_cases column <;>
      first | exact continuous_const | exact continuous_fst | exact continuous_snd
  · apply continuous_matrix
    intro row column
    fin_cases row <;> fin_cases column <;>
      first | exact continuous_const | exact continuous_fst.neg | exact continuous_snd.neg

theorem standardGoodLineFiniteArgument_continuous :
    Continuous standardGoodLineFiniteArgument := by
  have equality : standardGoodLineFiniteArgument = fun pair : FiniteAwayThree × FiniteAwayThree =>
      planeOppositeStandardMatrix pair.1.val pair.2.val := funext standardGoodLineFiniteArgument_pivot
  rw [equality]
  exact planeOppositeStandardMatrix_continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))

theorem goodLineFinitePadicIntegrand_continuous (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (exponent : ℂ) :
    Continuous (goodLineFinitePadicIntegrand cusp vector exponent) := by
  have equality : goodLineFinitePadicIntegrand cusp vector exponent =
      (finiteSphericalPlaneFunction cusp vector exponent) ∘ standardGoodLineFiniteArgument := by
    funext pair
    have independent := finiteSphericalPlaneValue_independent cusp vector spherical exponent _
      (standardGoodLineFinitePadicCoordinates pair) (finitePlaneInductionCoordinates _)
    change normPower (GeneralLinearGroup.det (atFinite (standardGoodLineFinitePadicCoordinates pair).block)) exponent *
      cusp.realize vector (atFinite (standardGoodLineFinitePadicCoordinates pair).block) = _
    rw [binary_det_atFinite]
    exact independent
  rw [equality]
  exact (finiteSphericalPlaneFunction_continuous cusp vector spherical exponent).comp
    standardGoodLineFiniteArgument_continuous

end TernaryPeriodPolynomials.SphericalDetection.Helpers
