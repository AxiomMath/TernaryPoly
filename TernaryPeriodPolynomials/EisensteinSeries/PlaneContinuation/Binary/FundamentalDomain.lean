module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.DiscreteSlices

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryFundamentalDomain

theorem exists_slices : ∃ slices : ℕ → Set BinaryAdelicGL,
    (∀ index, IsOpen (slices index)) ∧ (∀ point, ∃ index, point ∈ slices index) ∧
      ∀ index, ∀ point ∈ slices index, ∀ element : BinaryRationalGL, element • point ∈ slices index → element = 1 :=
  DiscreteSlices.exists_countable_slices (GeneralLinearGroup.map rationalAdele)
    (RationalDiscreteness.matrixNeighborhood 2) (RationalDiscreteness.matrixNeighborhood_open 2)
    (RationalDiscreteness.one_mem_matrixNeighborhood 2) RationalDiscreteness.rational_mem_matrixNeighborhood

noncomputable def slices : ℕ → Set BinaryAdelicGL := exists_slices.choose

theorem slices_open (index : ℕ) : IsOpen (slices index) := exists_slices.choose_spec.1 index

theorem slices_cover (point : BinaryAdelicGL) : ∃ index, point ∈ slices index := exists_slices.choose_spec.2.1 point

theorem slices_unique (index : ℕ) (point : BinaryAdelicGL) (membership : point ∈ slices index)
    (element : BinaryRationalGL) (translated : element • point ∈ slices index) : element = 1 :=
  exists_slices.choose_spec.2.2 index point membership element translated

noncomputable def domain : Set BinaryAdelicGL := CountableSlices.domain (ActingGroup := BinaryRationalGL) slices

theorem domain_measurable : MeasurableSet domain :=
  CountableSlices.domain_measurable slices (fun index => (slices_open index).measurableSet)

theorem domain_fundamental : IsFundamentalDomain BinaryRationalGL domain BinaryHaar.measure :=
  CountableSlices.isFundamentalDomain slices (fun index => (slices_open index).measurableSet)
    slices_cover slices_unique BinaryHaar.measure

scoped instance hasFundamentalDomain : HasFundamentalDomain BinaryRationalGL BinaryAdelicGL BinaryHaar.measure :=
  domain_fundamental.hasFundamentalDomain _

theorem domain_unique (point : BinaryAdelicGL) : ∃! element : BinaryRationalGL, element • point ∈ domain := by
  obtain ⟨element, membership⟩ := CountableSlices.exists_representative
    (ActingGroup := BinaryRationalGL) slices slices_cover point
  exact ⟨element, membership, fun other otherMembership =>
    CountableSlices.representative_unique slices slices_unique point other element otherMembership membership⟩

theorem eisenstein_integral_identity {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL)
    (termIntegrable : ∀ frame, IntegrableOn (weightedTerm data test vector parameter point frame) domain BinaryHaar.measure)
    (absolute : Summable (fun frame => ∫ binary in domain,
      ‖weightedTerm data test vector parameter point frame binary‖ ∂BinaryHaar.measure))
    (rawIntegrable : ∀ flag : Flags .plane, Integrable (fun binary =>
      kernel test (rationalGroup flag.out⁻¹ * point) binary * innerCharacter data parameter (GeneralLinearGroup.det binary) *
        data.cusp.realize vector binary) BinaryHaar.measure) :
    ∑' flag, eisensteinSummand (sectionFunction data test vector) parameter point flag =
      outerCharacter data parameter (GeneralLinearGroup.det point) *
        ∫ binary in domain, ThetaInvariance.integrand data test vector parameter point binary ∂BinaryHaar.measure :=
  GodementUnfolding.eisenstein_integral_identity data test vector parameter point domain domain_fundamental
    termIntegrable absolute rawIntegrable

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryFundamentalDomain
