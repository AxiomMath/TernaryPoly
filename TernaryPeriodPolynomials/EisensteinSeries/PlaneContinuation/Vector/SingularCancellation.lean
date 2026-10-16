module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Singular.OrbitCancellation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.Godement

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixStabilizerDomain
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularStabilizer TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularSliceDomain TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentAveragingAction
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentAveragingAction

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorSingularCancellation

def term {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ) (binary : BinaryAdelicGL) : ℂ :=
  GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary) *
    data.cusp.realize (test (point⁻¹.val * matrix.map rationalAdele * binary.val)) binary

theorem term_translate {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ)
    (rational : BinaryRationalGL) (binary : BinaryAdelicGL) :
    term data test parameter point matrix (rational • binary) =
      term data test parameter point (matrix * rational.val) binary := by
  have argument : point⁻¹.val * matrix.map rationalAdele * (GeneralLinearGroup.map rationalAdele rational * binary).val =
      point⁻¹.val * (matrix * rational.val).map rationalAdele * binary.val := by
    rw [Units.val_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rfl
  have characterValue : GodementIntegral.innerCharacter data parameter
      (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele rational)) = 1 := by
    rw [GeneralLinearGroup.map_det]
    exact ThetaInvariance.innerCharacter_rational data parameter (GeneralLinearGroup.det rational)
  simp only [term, GodementUnfolding.rational_smul, argument, map_mul, characterValue,
    one_mul, data.cusp.leftRational]

theorem term_invariant {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ)
    (element : MatrixStabilizerDomain.stabilizer matrix) (binary : BinaryAdelicGL) :
    term data test parameter point matrix (element • binary) = term data test parameter point matrix binary := by
  change term data test parameter point matrix (element.val • binary) = _
  rw [term_translate, element.property]

theorem term_stabilizer {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (binary : BinaryAdelicGL) (value : Adeles) :
    term data test parameter point matrix (SingularFrames.stabilizer basis value * binary) =
      GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary) *
        data.cusp.realize (test (point⁻¹.val * matrix.map rationalAdele * binary.val))
          (SingularFrames.stabilizer basis value * binary) := by
  unfold term
  rw [map_mul, SingularFrames.stabilizer_det, one_mul, Units.val_mul, ← Matrix.mul_assoc,
    Matrix.mul_assoc point⁻¹.val, SingularFrames.stabilizer_fixed matrix basis zeroFirst]

theorem average_zero {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (binary : BinaryAdelicGL) :
    (∫ value in additiveDomain, term data test parameter point matrix
      (SingularFrames.stabilizer basis value * binary) ∂adeleMeasure) = 0 := by
  simp only [term_stabilizer data test parameter point matrix basis zeroFirst,
    integral_const_mul, SingularCuspidality.stabilizer_integral_zero, mul_zero]

def sliceTerm {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ) : BinaryAdelicGL → ℂ :=
  IdeleSlice.determinantSlice.indicator (term data test parameter point matrix)

theorem sliceTerm_invariant {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ)
    (element : unipotents matrix) (binary : BinaryAdelicGL) :
    sliceTerm data test parameter point matrix (element • binary) = sliceTerm data test parameter point matrix binary := by
  have determinant : GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele element.val.val) = 1 := by
    rw [GeneralLinearGroup.map_det]
    have equality : GeneralLinearGroup.det element.val.val = 1 := element.property
    rw [equality, map_one]
  have sliceEq : element • binary ∈ IdeleSlice.determinantSlice ↔ binary ∈ IdeleSlice.determinantSlice :=
    IdeleSlice.determinantSlice_mul _ _ determinant
  by_cases membership : binary ∈ IdeleSlice.determinantSlice
  · simp only [sliceTerm, Set.indicator_of_mem membership, Set.indicator_of_mem (sliceEq.mpr membership)]
    exact term_invariant data test parameter point matrix element.val binary
  · simp only [sliceTerm, Set.indicator_of_notMem membership, Set.indicator_of_notMem (fun h => membership (sliceEq.mp h))]

theorem sliceTerm_average_zero {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ)
    (basis : BinaryRationalGL) (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (binary : BinaryAdelicGL) :
    (∫ value in additiveDomain, sliceTerm data test parameter point matrix
      (ofAdele basis value • binary) ∂adeleMeasure) = 0 := by
  by_cases membership : binary ∈ IdeleSlice.determinantSlice
  · have equation : (fun value : Adeles => sliceTerm data test parameter point matrix (ofAdele basis value • binary)) =
        fun value => term data test parameter point matrix (SingularFrames.stabilizer basis value * binary) := by
      funext value
      exact Set.indicator_of_mem ((slice_invariant basis value binary).mpr membership) _
    rw [equation]
    exact average_zero data test parameter point matrix basis zeroFirst binary
  · have equation : (fun value : Adeles => sliceTerm data test parameter point matrix (ofAdele basis value • binary)) = 0 := by
      funext value
      exact Set.indicator_of_notMem (fun h => membership ((slice_invariant basis value binary).mp h)) _
    rw [equation]
    exact MeasureTheory.integral_zero _ _

theorem integral_zero {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) (singular : ¬ FullRank matrix)
    (measurable : Measurable (term data test parameter point matrix))
    (integrable : IntegrableOn (term data test parameter point matrix) (domain matrix) BinaryHaar.measure) :
    (∫ binary in domain matrix, term data test parameter point matrix binary ∂BinaryHaar.measure) = 0 := by
  obtain ⟨basis, zeroFirst⟩ := SingularFrames.exists_zero_first_column matrix singular
  let := measurableAction basis
  let := invariantAction basis
  let := commutingAction basis matrix nonzero zeroFirst
  let : IsProbabilityMeasure (adeleMeasure.restrict additiveDomain) :=
    ⟨by rw [Measure.restrict_apply_univ, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleMeasure_additiveDomain]⟩
  have sliceIntegrable : IntegrableOn (sliceTerm data test parameter point matrix)
      (unipotentDomain matrix) BinaryHaar.measure := by
    apply (integrableOn_indicator_iff IdeleSlice.determinantSlice_measurable).mpr
    rw [Set.inter_comm]
    exact (SingularSliceDomain.integrable_iff matrix basis zeroFirst _
      (term_invariant data test parameter point matrix)).mp integrable
  have sliceMeasurable : Measurable (sliceTerm data test parameter point matrix) :=
    measurable.indicator IdeleSlice.determinantSlice_measurable
  have jointContinuous : Continuous (fun pair : Adeles × BinaryAdelicGL => SingularFrames.stabilizer basis pair.1 * pair.2) :=
    ((stabilizer_continuous basis).comp continuous_fst).mul continuous_snd
  have vanishing := FundamentalAveraging.integral_zero (unipotentDomain_fundamental matrix)
    (sliceTerm data test parameter point matrix) (sliceTerm_invariant data test parameter point matrix)
    (adeleMeasure.restrict additiveDomain) (ofAdele basis) sliceIntegrable
    (sliceMeasurable.comp jointContinuous.measurable).aestronglyMeasurable
    (sliceTerm_average_zero data test parameter point matrix basis zeroFirst)
  rw [sliceTerm, integral_indicator IdeleSlice.determinantSlice_measurable,
    Measure.restrict_restrict IdeleSlice.determinantSlice_measurable, Set.inter_comm] at vanishing
  rw [SingularSliceDomain.integral_eq matrix basis zeroFirst _ (term_invariant data test parameter point matrix)]
  exact vanishing

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorSingularCancellation
