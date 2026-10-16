module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Inputs
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.LambdaContinuation
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.AwayCompression
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.RightEquivariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.FullRealization
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.ContinuationRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.NormPower

@[expose] public section


/-!
# The factorization `J = λ̃ · R` of the standard continuation near the edge

Original work by Claude Sonnet 5.5.

This is step 5 of the edge-convergence plan, made concrete. For a plane section `f`, an argument `g`
with integral finite part and a binary adele `B`, put

* `J(s) = |det B|^{-e(s)} · cont f (s) (lineLevi 1 B · g)`, the chosen standard continuation of the
  flat family of `f`, normalized as in `HilbertFullRealization.value_realizes_normalized`;
* `R(s) = localScalar f s g B`, the realization at `B` of the local Hilbert integral at `{∞, 3}`
  (holomorphic on `Re s > -n/2 - 1` by `EdgeInputs.LocalScalarAnalytic`).

In the half plane `Re s > -n/2` of absolute convergence of the global integral,
`J(s) = awayLam(s) · R(s)` (the away compression `standardValue_eq_awayLam_smul_localValue` and the
realization of the Hilbert integral). The meromorphic identity theorem
(`LambdaContinuation.lambda_continuation`) then yields a single meromorphic `λ̃` at the cohomological
point with `J = λ̃ · R` on a punctured neighbourhood, for *every* datum `(f, g, B)`.

The chosen continuation is only determined up to its values at isolated points of the half plane;
the regularization `regularized` (integral formula on the half plane) removes this ambiguity, and
`regularized_eventuallyEq_raw` shows it agrees with the chosen continuation on punctured
neighbourhoods of every point.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace EdgeFactorization

open EdgeInputs

/-- The normalizing factor `|det B|^{-e(s)}` of the line side. -/
def levelFactor (degree : ℕ) (binary : BinaryAdelicGL) (parameter : ℂ) : ℂ :=
  normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .line parameter)

theorem levelFactor_analytic (degree : ℕ) (binary : BinaryAdelicGL) (point : ℂ) :
    AnalyticAt ℂ (levelFactor degree binary) point := by
  have exponent : AnalyticAt ℂ
      (fun parameter : ℂ => -binaryInductionExponent degree .line parameter) point := by
    simp only [binaryInductionExponent, inductionExponent]
    exact (analyticAt_const.sub (analyticAt_const.sub analyticAt_id.div_const)).neg
  exact (NormPower.normPower_analytic (GeneralLinearGroup.det binary) _).comp exponent

theorem value_eq_of_eventuallyEq_nhdsNE {first second : ℂ → ℂ} {point : ℂ}
    (firstContinuous : ContinuousAt first point) (secondContinuous : ContinuousAt second point)
    (equal : first =ᶠ[𝓝[≠] point] second) : first point = second point :=
  ((firstContinuous.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE secondContinuous).mp equal).eq_of_nhds

section Values

variable {degree : ℕ} (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)

/-- The chosen standard continuation of the flat family of a plane section is a standard
continuation of that family. -/
theorem sectionContinuation_continues
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    IsStandardContinuation (flatFamily data holomorphic sectionValue)
      (RightEquivariance.sectionContinuation data holomorphic sectionValue) :=
  (StandardValue.chosenContinuation_spec data
    (HolomorphicStandardValue.regularFamily data holomorphic
      (SectionSpace.linearFlatExtension data holomorphic sectionValue))).1

/-- The normalized chosen continuation. -/
def rawValue (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (binary : BinaryAdelicGL) (argument : AdelicGL) (parameter : ℂ) : ℂ :=
  levelFactor degree binary parameter *
    RightEquivariance.sectionContinuation data holomorphic sectionValue parameter
      (lineLevi 1 binary * argument)

/-- The normalized scalar standard integral. -/
def integralValue (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (binary : BinaryAdelicGL) (argument : AdelicGL) (parameter : ℂ) : ℂ :=
  levelFactor degree binary parameter *
    ∫ coordinates, standardIntegrand (flatFamily data holomorphic sectionValue) parameter
      (lineLevi 1 binary * argument) coordinates ∂radicalMeasure

open Classical in
/-- The integral formula in the half plane of absolute convergence, the chosen continuation
elsewhere. -/
def regularized (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (binary : BinaryAdelicGL) (argument : AdelicGL) (parameter : ℂ) : ℂ :=
  if parameter ∈ globalHalfPlane degree then
    integralValue data holomorphic sectionValue binary argument parameter
  else rawValue data holomorphic sectionValue binary argument parameter

theorem rawValue_meromorphic (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (binary : BinaryAdelicGL) (argument : AdelicGL) (point : ℂ) :
    MeromorphicAt (rawValue data holomorphic sectionValue binary argument) point :=
  (levelFactor_analytic degree binary point).meromorphicAt.mul
    ((sectionContinuation_continues data holomorphic sectionValue).1 (lineLevi 1 binary * argument)
      point)

theorem raw_eventuallyEq_integral (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (binary : BinaryAdelicGL) (argument : AdelicGL) (point : ℂ)
    (inside : point ∈ globalHalfPlane degree) :
    rawValue data holomorphic sectionValue binary argument =ᶠ[𝓝[≠] point]
      integralValue data holomorphic sectionValue binary argument := by
  have germ := StandardContinuationRegularity.germ_eq_integral data
    (flatFamily data holomorphic sectionValue)
    (RightEquivariance.sectionContinuation data holomorphic sectionValue)
    (flatFamily_flat data holomorphic sectionValue)
    (sectionContinuation_continues data holomorphic sectionValue)
    (lineLevi 1 binary * argument) point inside
  filter_upwards [germ] with parameter equal
  exact congrArg (fun value => levelFactor degree binary parameter * value) equal

theorem integralValue_analyticAt (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (binary : BinaryAdelicGL) (argument : AdelicGL) (point : ℂ)
    (inside : point ∈ globalHalfPlane degree) :
    AnalyticAt ℂ (integralValue data holomorphic sectionValue binary argument) point :=
  (levelFactor_analytic degree binary point).mul
    (CompactScalarConvergence.standard_analyticAt data (flatFamily data holomorphic sectionValue)
      (flatFamily_flat data holomorphic sectionValue) point inside (lineLevi 1 binary * argument))

/-- The regularization agrees with the chosen continuation on punctured neighbourhoods of every
point: near a point the chosen continuation (meromorphic at the point) is analytic off the point
and agrees there with the integral formula wherever the latter converges. -/
theorem regularized_eventuallyEq_raw
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (binary : BinaryAdelicGL) (argument : AdelicGL) (point : ℂ) :
    regularized data holomorphic sectionValue binary argument =ᶠ[𝓝[≠] point]
      rawValue data holomorphic sectionValue binary argument := by
  filter_upwards [(rawValue_meromorphic data holomorphic sectionValue binary argument
    point).eventually_analyticAt] with parameter analytic
  by_cases inside : parameter ∈ globalHalfPlane degree
  · have equal := value_eq_of_eventuallyEq_nhdsNE analytic.continuousAt
      (integralValue_analyticAt data holomorphic sectionValue binary argument parameter
        inside).continuousAt
      (raw_eventuallyEq_integral data holomorphic sectionValue binary argument parameter inside)
    unfold regularized
    rw [ite_eq_left inside]
    exact equal.symm
  · unfold regularized
    rw [ite_eq_right inside]

theorem regularized_meromorphic
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (binary : BinaryAdelicGL) (argument : AdelicGL) (point : ℂ) :
    MeromorphicAt (regularized data holomorphic sectionValue binary argument) point :=
  (rawValue_meromorphic data holomorphic sectionValue binary argument point).congr
    (regularized_eventuallyEq_raw data holomorphic sectionValue binary argument point).symm

/-- In the half plane of absolute convergence the regularized value is the away compression scalar
times the realization of the local standard integral. -/
theorem regularized_eq_awayLam_mul (lsm : LocalVectorsSmooth data holomorphic)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (binary : BinaryAdelicGL) (argument : AdelicGL) (integral : IsIntegralArgument argument)
    (parameter : ℂ) (inside : parameter ∈ globalHalfPlane degree) :
    regularized data holomorphic sectionValue binary argument parameter =
      awayLam data parameter * localScalar data holomorphic sectionValue parameter argument binary := by
  have localHalf : parameter ∈ localHalfPlane degree := by
    have bound : -(degree : ℝ) / 2 < parameter.re := inside
    show -(degree : ℝ) / 2 - 1 < parameter.re
    linarith
  have stable : AwayStable argument := by
    obtain ⟨integralMatrix, equation⟩ := integral
    exact awayStable_of_good (awayGood_of_finite_integral ⟨integralMatrix, equation.symm⟩)
  have realizes := HilbertFullRealization.value_realizes_normalized data
    (flatFamily data holomorphic sectionValue) (flatFamily_flat data holomorphic sectionValue)
    parameter inside argument binary
  have compression := standardValue_eq_awayLam_smul_localValue data parameter
    (flatFamily data holomorphic sectionValue parameter)
    ((flatFamily_flat data holomorphic sectionValue).1 parameter) inside stable
  have smoothMembership := lsm sectionValue parameter localHalf argument integral
  have vectorEquation : HilbertStandardSmooth.vector data parameter
      (flatFamily data holomorphic sectionValue parameter)
      ((flatFamily_flat data holomorphic sectionValue).1 parameter) inside argument =
      awayLam data parameter • (⟨localVector data holomorphic sectionValue parameter argument,
        smoothMembership⟩ : data.cusp.smooth) :=
    Subtype.ext compression
  unfold regularized
  rw [ite_eq_left inside]
  unfold integralValue levelFactor
  rw [← realizes, vectorEquation, map_smul, Pi.smul_apply, smul_eq_mul]
  unfold localScalar
  rw [vecScalar_of_mem data smoothMembership binary]

end Values

section Continuation

variable {degree : ℕ} (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)

/-- The datum of the continuation argument: a section, an integral argument and a binary adele. -/
abbrev Datum : Type :=
  {datum : SectionSpace.inducedSections data .plane cohomologicalPoint × AdelicGL × BinaryAdelicGL //
    IsIntegralArgument datum.2.1}

/-- **Factorization of the standard continuation near the cohomological point.** There is a single
function `λ̃`, meromorphic at the cohomological point, such that for every plane section `f`, every
argument `g` with integral finite part and every binary adele `B`, on a punctured neighbourhood of
the cohomological point
`|det B|^{-e(s)} · cont f (s) (lineLevi 1 B · g) = λ̃(s) · localScalar f s g B`. -/
theorem exists_factorization (hdeg : 2 ≤ degree) (lsm : LocalVectorsSmooth data holomorphic)
    (lsa : LocalScalarAnalytic data holomorphic) :
    ∃ lam : ℂ → ℂ, MeromorphicAt lam cohomologicalPoint ∧
      ∀ (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
        (argument : AdelicGL), IsIntegralArgument argument → ∀ binary : BinaryAdelicGL,
        ∀ᶠ parameter in 𝓝[≠] cohomologicalPoint,
          levelFactor degree binary parameter *
              RightEquivariance.sectionContinuation data holomorphic sectionValue parameter
                (lineLevi 1 binary * argument) =
            lam parameter * localScalar data holomorphic sectionValue parameter argument binary := by
  have degreeReal : (2 : ℝ) ≤ degree := by exact_mod_cast hdeg
  have base : cohomologicalPoint ∈ localHalfPlane degree := by
    show -(degree : ℝ) / 2 - 1 < cohomologicalPoint.re
    rw [cohomologicalPoint_re]
    linarith
  have continuationData : LambdaContinuation.ContinuationData (localHalfPlane degree)
      (globalHalfPlane degree)
      (fun datum : Datum data => regularized data holomorphic datum.val.1 datum.val.2.2
        datum.val.2.1)
      (fun datum : Datum data => fun parameter => localScalar data holomorphic datum.val.1 parameter
        datum.val.2.1 datum.val.2.2)
      (fun parameter => awayLam data parameter) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold localHalfPlane
      exact (convex_halfSpace_re_gt (-(degree : ℝ) / 2 - 1)).isPreconnected
    · unfold globalHalfPlane
      exact isOpen_lt continuous_const Complex.continuous_re
    · intro parameter inside
      have bound : -(degree : ℝ) / 2 < parameter.re := inside
      show -(degree : ℝ) / 2 - 1 < parameter.re
      linarith
    · refine ⟨((-(degree : ℝ) / 2 + 1 : ℝ) : ℂ), ?_⟩
      show -(degree : ℝ) / 2 < ((-(degree : ℝ) / 2 + 1 : ℝ) : ℂ).re
      rw [Complex.ofReal_re]
      linarith
    · intro datum parameter _
      exact regularized_meromorphic data holomorphic datum.val.1 datum.val.2.2 datum.val.2.1
        parameter
    · intro datum
      exact lsa datum.val.1 datum.val.2.1 datum.property datum.val.2.2
    · intro datum parameter inside
      exact regularized_eq_awayLam_mul data holomorphic lsm datum.val.1 datum.val.2.2
        datum.val.2.1 datum.property parameter inside
  have transfer : ∀ (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
      (argument : AdelicGL) (binary : BinaryAdelicGL),
      regularized data holomorphic sectionValue binary argument =ᶠ[𝓝[≠] cohomologicalPoint]
        rawValue data holomorphic sectionValue binary argument :=
    fun sectionValue argument binary =>
      regularized_eventuallyEq_raw data holomorphic sectionValue binary argument cohomologicalPoint
  rcases LambdaContinuation.lambda_continuation continuationData base with
    ⟨_, vanishing⟩ | ⟨base_datum, meromorphic, _, factorization⟩
  · refine ⟨fun _ => 0, MeromorphicAt.const 0 _, ?_⟩
    intro sectionValue argument integral binary
    filter_upwards [vanishing ⟨(sectionValue, argument, binary), integral⟩,
      transfer sectionValue argument binary] with parameter zero same
    have raw : rawValue data holomorphic sectionValue binary argument parameter = 0 := by
      rw [← same]
      exact zero
    unfold rawValue at raw
    rw [raw]
    simp
  · refine ⟨LambdaContinuation.lamTilde
      (fun datum : Datum data => regularized data holomorphic datum.val.1 datum.val.2.2
        datum.val.2.1)
      (fun datum : Datum data => fun parameter => localScalar data holomorphic datum.val.1 parameter
        datum.val.2.1 datum.val.2.2) base_datum, meromorphic, ?_⟩
    intro sectionValue argument integral binary
    filter_upwards [factorization ⟨(sectionValue, argument, binary), integral⟩,
      transfer sectionValue argument binary] with parameter equation same
    have raw : rawValue data holomorphic sectionValue binary argument parameter =
        LambdaContinuation.lamTilde
          (fun datum : Datum data => regularized data holomorphic datum.val.1 datum.val.2.2
            datum.val.2.1)
          (fun datum : Datum data => fun parameter => localScalar data holomorphic datum.val.1
            parameter datum.val.2.1 datum.val.2.2) base_datum parameter *
          localScalar data holomorphic sectionValue parameter argument binary := by
      rw [← same]
      exact equation
    unfold rawValue at raw
    exact raw

/-- The analyticity radius of the factorization function away from its possible pole. -/
theorem exists_analytic_radius {lam : ℂ → ℂ} (meromorphic : MeromorphicAt lam cohomologicalPoint) :
    ∃ epsilon > 0, ∀ parameter : ℂ, parameter ≠ cohomologicalPoint →
      dist parameter cohomologicalPoint < epsilon → AnalyticAt ℂ lam parameter :=
  LambdaContinuation.exists_punctured_ball meromorphic.eventually_analyticAt

end Continuation

end EdgeFactorization

end TernaryPeriodPolynomials.EdgeConvergence
