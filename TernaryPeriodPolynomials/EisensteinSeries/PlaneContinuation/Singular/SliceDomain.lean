module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Singular.Stabilizer
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.SliceFundamentalDomain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixStabilizerDomain TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularStabilizer
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularSliceDomain

def unipotentDomain (matrix : Rectangular ℚ) : Set BinaryAdelicGL :=
  SubgroupFundamentalDomain.domain (unipotents matrix) (domain matrix)

theorem unipotentDomain_measurable (matrix : Rectangular ℚ) : MeasurableSet (unipotentDomain matrix) :=
  SubgroupFundamentalDomain.measurable _ _ (domain_measurable matrix)

theorem matrixDomain_unique (matrix : Rectangular ℚ) (point : BinaryAdelicGL) :
    ∃! element : stabilizer matrix, element • point ∈ domain matrix :=
  SubgroupFundamentalDomain.unique _ _ BinaryFundamentalDomain.domain_unique point

theorem unipotentDomain_unique (matrix : Rectangular ℚ) (point : BinaryAdelicGL) :
    ∃! element : unipotents matrix, element • point ∈ unipotentDomain matrix :=
  SubgroupFundamentalDomain.unique _ _ (matrixDomain_unique matrix) point

theorem unipotentDomain_fundamental (matrix : Rectangular ℚ) :
    IsFundamentalDomain (unipotents matrix) (unipotentDomain matrix) BinaryHaar.measure :=
  IsFundamentalDomain.mk' (unipotentDomain_measurable matrix).nullMeasurableSet (unipotentDomain_unique matrix)

def sliceDomain (matrix : Rectangular ℚ) : Set BinaryAdelicGL :=
  unipotentDomain matrix ∩ IdeleSlice.determinantSlice

theorem sliceDomain_measurable (matrix : Rectangular ℚ) : MeasurableSet (sliceDomain matrix) :=
  (unipotentDomain_measurable matrix).inter IdeleSlice.determinantSlice_measurable

theorem det_smul (matrix : Rectangular ℚ) (element : stabilizer matrix) (point : BinaryAdelicGL) :
    GeneralLinearGroup.det (element • point) = IdeleSlice.rational (determinant matrix element) * GeneralLinearGroup.det point := by
  change GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele element.val * point) = _
  rw [map_mul, GeneralLinearGroup.map_det]
  rfl

theorem slice_exists (matrix : Rectangular ℚ) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (point : BinaryAdelicGL) :
    ∃ element : stabilizer matrix, element • point ∈ IdeleSlice.determinantSlice := by
  obtain ⟨scalar, membership⟩ := IdeleSlice.exists_representative (GeneralLinearGroup.det point)
  refine ⟨scalingElement matrix basis zeroFirst scalar, ?_⟩
  change GeneralLinearGroup.det (_ • point) ∈ IdeleSlice.slice
  rwa [det_smul, scalingElement_det]

theorem slice_return (matrix : Rectangular ℚ) (point : BinaryAdelicGL) (membership : point ∈ IdeleSlice.determinantSlice)
    (element : stabilizer matrix) : element • point ∈ IdeleSlice.determinantSlice ↔ element ∈ unipotents matrix := by
  change GeneralLinearGroup.det (element • point) ∈ IdeleSlice.slice ↔ determinant matrix element = 1
  rw [det_smul]
  exact IdeleSlice.rational_mul_mem_iff _ membership _

theorem sliceDomain_fundamental (matrix : Rectangular ℚ) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) :
    IsFundamentalDomain (stabilizer matrix) (sliceDomain matrix) BinaryHaar.measure :=
  SliceFundamentalDomain.fundamental (unipotents matrix) (unipotentDomain matrix) IdeleSlice.determinantSlice
    (unipotentDomain_measurable matrix) IdeleSlice.determinantSlice_measurable (unipotentDomain_unique matrix)
    (slice_exists matrix basis zeroFirst) (slice_return matrix) BinaryHaar.measure

theorem integral_eq {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (matrix : Rectangular ℚ) (basis : BinaryRationalGL) (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0)
    (function : BinaryAdelicGL → Target)
    (invariant : ∀ (element : stabilizer matrix) (point : BinaryAdelicGL), function (element • point) = function point) :
    (∫ point in domain matrix, function point ∂BinaryHaar.measure) =
      ∫ point in sliceDomain matrix, function point ∂BinaryHaar.measure :=
  (domain_fundamental matrix).setIntegral_eq (sliceDomain_fundamental matrix basis zeroFirst) invariant

theorem integrable_iff {Target : Type*} [NormedAddCommGroup Target]
    (matrix : Rectangular ℚ) (basis : BinaryRationalGL) (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0)
    (function : BinaryAdelicGL → Target)
    (invariant : ∀ (element : stabilizer matrix) (point : BinaryAdelicGL), function (element • point) = function point) :
    IntegrableOn function (domain matrix) BinaryHaar.measure ↔ IntegrableOn function (sliceDomain matrix) BinaryHaar.measure :=
  (domain_fundamental matrix).integrableOn_iff (sliceDomain_fundamental matrix basis zeroFirst) invariant

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularSliceDomain
