module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.UnipotentAveragingAction
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MatrixOrbitIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixStabilizerDomain TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularStabilizer TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularSliceDomain
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentAveragingAction
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentAveragingAction

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularOrbitCancellation

def sliceTerm {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ) : BinaryAdelicGL → ℂ :=
  IdeleSlice.determinantSlice.indicator (term data test vector parameter point matrix)

theorem sliceTerm_measurable {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (continuousTest : Continuous test) (vector : data.cusp.smooth) (parameter : ℂ)
    (point : AdelicGL) (matrix : Rectangular ℚ) : Measurable (sliceTerm data test vector parameter point matrix) :=
  (MatrixOrbitIntegrability.term_measurable data test continuousTest vector parameter point matrix).indicator
    IdeleSlice.determinantSlice_measurable

theorem sliceTerm_invariant {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ)
    (element : unipotents matrix) (binary : BinaryAdelicGL) :
    sliceTerm data test vector parameter point matrix (element • binary) = sliceTerm data test vector parameter point matrix binary := by
  have determinant : GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele element.val.val) = 1 := by
    rw [GeneralLinearGroup.map_det]
    have equality : GeneralLinearGroup.det element.val.val = 1 := element.property
    rw [equality, map_one]
  have sliceEq : element • binary ∈ IdeleSlice.determinantSlice ↔ binary ∈ IdeleSlice.determinantSlice :=
    IdeleSlice.determinantSlice_mul _ _ determinant
  by_cases membership : binary ∈ IdeleSlice.determinantSlice
  · simp only [sliceTerm, Set.indicator_of_mem membership, Set.indicator_of_mem (sliceEq.mpr membership)]
    exact term_invariant data test vector parameter point matrix element.val binary
  · simp only [sliceTerm, Set.indicator_of_notMem membership, Set.indicator_of_notMem (fun h => membership (sliceEq.mp h))]

theorem sliceTerm_average_zero {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ)
    (basis : BinaryRationalGL) (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (binary : BinaryAdelicGL) :
    (∫ value in additiveDomain, sliceTerm data test vector parameter point matrix
      (ofAdele basis value • binary) ∂adeleMeasure) = 0 := by
  by_cases membership : binary ∈ IdeleSlice.determinantSlice
  · have equation : (fun value : Adeles => sliceTerm data test vector parameter point matrix (ofAdele basis value • binary)) =
        fun value => term data test vector parameter point matrix (SingularFrames.stabilizer basis value * binary) := by
      funext value
      exact Set.indicator_of_mem ((slice_invariant basis value binary).mpr membership) _
    rw [equation]
    exact SingularCuspidality.weighted_stabilizer_integral_zero data.cusp vector test
      (GodementIntegral.innerCharacter data parameter) point matrix basis zeroFirst binary
  · have equation : (fun value : Adeles => sliceTerm data test vector parameter point matrix (ofAdele basis value • binary)) = 0 := by
      funext value
      exact Set.indicator_of_notMem (fun h => membership ((slice_invariant basis value binary).mp h)) _
    rw [equation]
    exact MeasureTheory.integral_zero _ _

theorem sliceTerm_integrable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) :
    IntegrableOn (sliceTerm data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix)
      (unipotentDomain matrix) BinaryHaar.measure := by
  apply (integrableOn_indicator_iff IdeleSlice.determinantSlice_measurable).mpr
  rw [Set.inter_comm]
  exact (SingularSliceDomain.integrable_iff matrix basis zeroFirst _
    (term_invariant data _ vector parameter point matrix)).mp
      (MatrixOrbitIntegrability.integrable_domain data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane matrix nonzero)

theorem integral_zero {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) (singular : ¬ FullRank matrix) :
    (∫ binary in domain matrix,
      term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix binary ∂BinaryHaar.measure) = 0 := by
  obtain ⟨basis, zeroFirst⟩ := SingularFrames.exists_zero_first_column matrix singular
  let := measurableAction basis
  let := invariantAction basis
  let := commutingAction basis matrix nonzero zeroFirst
  let : IsProbabilityMeasure (adeleMeasure.restrict additiveDomain) :=
    ⟨by rw [Measure.restrict_apply_univ, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleMeasure_additiveDomain]⟩
  have jointContinuous : Continuous (fun pair : Adeles × BinaryAdelicGL => SingularFrames.stabilizer basis pair.1 * pair.2) :=
    ((stabilizer_continuous basis).comp continuous_fst).mul continuous_snd
  have vanishing := FundamentalAveraging.integral_zero (unipotentDomain_fundamental matrix)
    (sliceTerm data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix)
    (sliceTerm_invariant data _ vector parameter point matrix) (adeleMeasure.restrict additiveDomain)
    (ofAdele basis)
    (sliceTerm_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane matrix nonzero basis zeroFirst)
    ((sliceTerm_measurable data _ (AdelicSchwartzTheta.tensorTest_continuous realTest finiteTest finiteContinuous)
      vector parameter point matrix).comp jointContinuous.measurable).aestronglyMeasurable
    (sliceTerm_average_zero data _ vector parameter point matrix basis zeroFirst)
  rw [sliceTerm, integral_indicator IdeleSlice.determinantSlice_measurable,
    Measure.restrict_restrict IdeleSlice.determinantSlice_measurable, Set.inter_comm] at vanishing
  rw [SingularSliceDomain.integral_eq matrix basis zeroFirst _ (term_invariant data _ vector parameter point matrix)]
  exact vanishing

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularOrbitCancellation
