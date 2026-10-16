module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Standard
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Inputs
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Circle
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Transport
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Factorization
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.RightEquivarianceFactorized
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.RightEquivarianceLocal
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliersXiSmooth

@[expose] public section


/-!
# Assembly of the edge standard operator at `n = 3`

Original work by Claude Sonnet 5.5.

`EdgeStandard.related_total_of_edgeStandardOperator` reduces the totality input of
`GraphReduction.standard_graph_of_eisenstein` at `n = 3` to an `EdgeStandardOperator`: smooth real
orbits, right real equivariance and smooth cusp lifts of the holomorphic-continuation standard
operator. This file derives all three from the four named analytic inputs about the *local* Hilbert
standard integral at `{∞, 3}` (`EdgeInputs`):

* `LocalVectorsSmooth`, `LocalScalarAnalytic` : smoothness of the local vectors and holomorphy of
  their realizations in the parameter on `Re s > -n/2 - 1`;
* `LocalLiftVector`, `LocalLiftRealization` : Cauchy circle averages of the local vectors are
  smooth vectors, jointly smooth in vertices and the real translation, realizing the circle
  averages of the realizations; `LocalLiftScalarSmooth` : the scalar circle average of a single
  section is smooth in the real translation;
* `TwistedLocalContinuity` : joint continuity of the local scalar for the twisted sections used for
  right real equivariance.

Proved here, from these inputs and the away compression (`AwayCompression`):

1. `EdgeFactorization.exists_factorization` : a single `λ̃`, meromorphic at the cohomological point,
   with `|det B|^{-e(s)} cont f (s) (lineLevi 1 B g) = λ̃(s) · localScalar f s g B` near it.
2. `edgeCompactLift_of_inputs` : for `κ` in the maximal compact, the standard value at
   `lineLevi 1 B κ y` is the (normalized) realization of the smooth vector given by the Cauchy
   circle average of `λ̃ · local vectors` (the circle average of `λ̃ R` is the value at the centre of
   the holomorphic function `J = λ̃ R`, by `EdgeCircle.circleAverage_eq_value`).
3. `smooth_real`, `smooth_lift` from 2 by `EdgeTransport` (every adelic argument is
   `n · lineLevi t B · κ`).
4. `right_real` from the `DiagonalDatum` of `RightEquivarianceFactorized`, built from 1 and
   `TwistedLocalContinuity`, at maximal compact arguments, then `EdgeTransport`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Metric Filter Topology
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence.EdgeStandard
open TernaryPeriodPolynomials.EdgeConvergence.EdgeInputs

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace EdgeAssembly

variable {degree : ℕ} (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)

/-- The standard value of a plane section is line covariant. -/
theorem edgeStd_covariant
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    EdgeTransport.LineCovariant data (edgeStd data holomorphic sectionValue).val := by
  obtain ⟨radicalInvariant, _⟩ := (edgeStd data holomorphic sectionValue).property
  exact
    { radical := fun first second argument => radicalInvariant first second argument
      rankOne := fun unit argument =>
        HolomorphicStandardValue.flatStandard_rankOne data holomorphic
          (SectionSpace.linearFlatExtension data holomorphic sectionValue) unit argument }

/-- A maximal compact times a real element has integral finite part. -/
theorem isIntegralArgument_mul_atInfinity {compact : AdelicGL}
    (membership : inMaximalCompact compact) (real : RealGL3) :
    IsIntegralArgument (compact * atInfinity real) := by
  obtain ⟨integral, equation⟩ := membership.2
  refine ⟨integral, ?_⟩
  rw [map_mul, InducedContinuity.finiteGroup_atInfinity, mul_one, equation]

theorem isIntegralArgument_of_compact {compact : AdelicGL} (membership : inMaximalCompact compact) :
    IsIntegralArgument compact := by
  obtain ⟨integral, equation⟩ := membership.2
  exact ⟨integral, equation.symm⟩

theorem closedBall_subset_localHalfPlane (hdeg : 2 ≤ degree) {radius : ℝ} (small : radius ≤ 1 / 4) :
    closedBall cohomologicalPoint radius ⊆ localHalfPlane degree := by
  have degreeReal : (2 : ℝ) ≤ degree := by exact_mod_cast hdeg
  intro parameter membership
  have bound : |parameter.re - cohomologicalPoint.re| ≤ radius :=
    calc |parameter.re - cohomologicalPoint.re| = |(parameter - cohomologicalPoint).re| := by
          rw [Complex.sub_re]
      _ ≤ ‖parameter - cohomologicalPoint‖ := Complex.abs_re_le_norm _
      _ = dist parameter cohomologicalPoint := (Complex.dist_eq _ _).symm
      _ ≤ radius := mem_closedBall.1 membership
  have lower := (abs_le.1 bound).1
  rw [cohomologicalPoint_re] at lower
  show -(degree : ℝ) / 2 - 1 < parameter.re
  linarith

/-- **The circle datum.** There are a function `lam`, meromorphic at the cohomological point and
analytic on a punctured disc, and a radius `r` such that for every plane section, every argument
with integral finite part and every binary adele, the circle average of `lam · localScalar` over
`|s - s₀| = r` is the normalized standard value at `lineLevi 1 B · g`: the circle average of the
factorization `λ̃ R` is the value at the centre of the holomorphic function `J = λ̃ R`. -/
theorem exists_circle_datum (hdeg : 2 ≤ degree) (lsm : LocalVectorsSmooth data holomorphic)
    (lsa : LocalScalarAnalytic data holomorphic) :
    ∃ (lam : ℂ → ℂ) (radius : ℝ), 0 < radius ∧
      closedBall cohomologicalPoint radius ⊆ localHalfPlane degree ∧
      ContinuousOn lam (sphere cohomologicalPoint radius) ∧
      ∀ (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
        (argument : AdelicGL), IsIntegralArgument argument → ∀ binary : BinaryAdelicGL,
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ parameter in C(cohomologicalPoint, radius),
            (parameter - cohomologicalPoint)⁻¹ • (lam parameter • localScalar data holomorphic
              sectionValue parameter argument binary) =
          EdgeFactorization.levelFactor degree binary cohomologicalPoint *
            RightEquivariance.sectionContinuation data holomorphic sectionValue
              cohomologicalPoint (lineLevi 1 binary * argument) := by
  obtain ⟨lam, meromorphic, factorization⟩ :=
    EdgeFactorization.exists_factorization data holomorphic hdeg lsm lsa
  obtain ⟨epsilon, epsilon_pos, lam_analytic⟩ := EdgeFactorization.exists_analytic_radius meromorphic
  set radius : ℝ := min (epsilon / 2) (1 / 4)
  have radius_pos : 0 < radius := lt_min (half_pos epsilon_pos) (by norm_num)
  have radius_lt : radius < epsilon :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self epsilon_pos)
  have radius_small : radius ≤ 1 / 4 := min_le_right _ _
  have ballInside := closedBall_subset_localHalfPlane (degree := degree) hdeg radius_small
  have lam_continuous : ContinuousOn lam (sphere cohomologicalPoint radius) := by
    intro parameter membership
    have onSphere : dist parameter cohomologicalPoint = radius := mem_sphere.1 membership
    have different : parameter ≠ cohomologicalPoint := by
      intro same
      rw [same, dist_self] at onSphere
      exact radius_pos.ne onSphere
    exact (lam_analytic parameter different
      (by rw [onSphere]; exact radius_lt)).continuousAt.continuousWithinAt
  refine ⟨lam, radius, radius_pos, ballInside, lam_continuous, ?_⟩
  intro sectionValue argument integral binary
  have localDifferentiable : DifferentiableOn ℂ
      (fun parameter => localScalar data holomorphic sectionValue parameter argument binary)
      (closedBall cohomologicalPoint radius) := by
    intro parameter membership
    exact ((lsa sectionValue argument integral binary) parameter
      (ballInside membership)).differentiableAt.differentiableWithinAt
  have valueAnalytic : AnalyticAt ℂ (fun parameter =>
      EdgeFactorization.levelFactor degree binary parameter *
        RightEquivariance.sectionContinuation data holomorphic sectionValue parameter
          (lineLevi 1 binary * argument)) cohomologicalPoint :=
    (EdgeFactorization.levelFactor_analytic degree binary cohomologicalPoint).mul
      (RightEquivariance.sectionContinuation_analyticAt data holomorphic sectionValue
        (lineLevi 1 binary * argument))
  exact EdgeCircle.circleAverage_eq_value radius_pos radius_lt lam_analytic localDifferentiable
    valueAnalytic (factorization sectionValue argument integral binary)

/-- **The compact-level Hilbert lift** (derived). For a family of plane sections with smooth cusp
lift and a maximal compact `κ`, the standard values at `lineLevi 1 B · κ · y` are the normalized
realizations of smooth vectors `W(x)` depending smoothly on `x` (vertices and `y`). -/
def EdgeCompactLift : Prop :=
  ∀ {arity : ℕ} (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices)),
    HasSmoothCuspLift data .plane cohomologicalPoint family →
    ∀ compact : AdelicGL, inMaximalCompact compact →
      ∃ lift : (Fin (arity + 1) → RealGL3) → data.cusp.smooth,
        Smooth (fun x => (lift x).val) ∧
        ∀ x binary, data.cusp.realize (lift x) binary =
          normPower (GeneralLinearGroup.det binary)
              (-binaryInductionExponent degree .line cohomologicalPoint) *
            (edgeStd data holomorphic ⟨family (fun index => x index.castSucc), induced _⟩).val
              (lineLevi 1 binary * (compact * atInfinity (x (Fin.last arity))))

theorem edgeCompactLift_of_inputs (hdeg : 2 ≤ degree) (lsm : LocalVectorsSmooth data holomorphic)
    (lsa : LocalScalarAnalytic data holomorphic) (lcl : LocalCircleLift data holomorphic) :
    EdgeCompactLift data holomorphic := by
  obtain ⟨lam, radius, radius_pos, ballInside, lam_continuous, circleValue⟩ :=
    exists_circle_datum data holomorphic hdeg lsm lsa
  intro arity family induced lift compact compactMembership
  obtain ⟨vectors, vectorsSmooth, vectorsRealize⟩ :=
    lcl lam radius radius_pos ballInside lam_continuous family induced lift compact
      compactMembership
  refine ⟨vectors, vectorsSmooth, ?_⟩
  intro x binary
  rw [vectorsRealize x binary]
  exact circleValue ⟨family (fun index => x index.castSucc), induced (fun index => x index.castSucc)⟩
    (compact * atInfinity (x (Fin.last arity)))
    (isIntegralArgument_mul_atInfinity compactMembership _) binary

/-- **Real smoothness of the orbit maps** of the standard value. -/
theorem smooth_real_of_inputs (hdeg : 2 ≤ degree) (lsm : LocalVectorsSmooth data holomorphic)
    (lsa : LocalScalarAnalytic data holomorphic) (lss : LocalLiftScalarSmooth data holomorphic)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    Smooth (fun x : Fin 1 → RealGL3 =>
      (edgeStd data holomorphic sectionValue).val (argument * atInfinity (x 0))) := by
  obtain ⟨lam, radius, radius_pos, ballInside, lam_continuous, circleValue⟩ :=
    exists_circle_datum data holomorphic hdeg lsm lsa
  refine EdgeTransport.smooth_real_of_compact (edgeStd_covariant data holomorphic sectionValue) ?_
    argument
  intro compact compactMembership binary
  have average := lss lam radius radius_pos ballInside lam_continuous sectionValue compact
    compactMembership binary
  have nonzero : EdgeFactorization.levelFactor degree binary cohomologicalPoint ≠ 0 :=
    ParabolicInvariance.normPower_ne_zero _ _
  have equation : (fun x : Fin 1 → RealGL3 =>
      (edgeStd data holomorphic sectionValue).val
        (lineLevi 1 binary * (compact * atInfinity (x 0)))) =
      fun x => (EdgeFactorization.levelFactor degree binary cohomologicalPoint)⁻¹ *
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ parameter in C(cohomologicalPoint, radius),
          (parameter - cohomologicalPoint)⁻¹ • (lam parameter • localScalar data holomorphic
            sectionValue parameter (compact * atInfinity (x 0)) binary)) := by
    funext x
    show (edgeStd data holomorphic sectionValue).val
        (lineLevi 1 binary * (compact * atInfinity (x 0))) =
      (EdgeFactorization.levelFactor degree binary cohomologicalPoint)⁻¹ *
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ parameter in C(cohomologicalPoint, radius),
          (parameter - cohomologicalPoint)⁻¹ • (lam parameter • localScalar data holomorphic
            sectionValue parameter (compact * atInfinity (x 0)) binary))
    rw [circleValue sectionValue (compact * atInfinity (x 0))
      (isIntegralArgument_mul_atInfinity compactMembership _) binary]
    exact (inv_mul_cancel_left₀ nonzero _).symm
  rw [equation]
  exact EdgeTransport.smooth_const_mul _ average

/-- **Smooth cusp lifts** of the standard values of families of plane sections. -/
theorem smooth_lift_of_inputs (hecl : EdgeCompactLift data holomorphic) {arity : ℕ}
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (function vertices))
    (lift : HasSmoothCuspLift data .plane cohomologicalPoint function) :
    HasSmoothCuspLift data .line cohomologicalPoint (fun vertices =>
      (edgeStd data holomorphic ⟨function vertices, induced vertices⟩).val) := by
  refine EdgeTransport.hasSmoothCuspLift_of_compact data _
    (fun vertices => edgeStd_covariant data holomorphic ⟨function vertices, induced vertices⟩) ?_
  intro compact compactMembership
  obtain ⟨vectors, vectorsSmooth, vectorsRealize⟩ :=
    hecl function induced lift compact compactMembership
  exact ⟨vectors, vectorsSmooth, vectorsRealize⟩

/-- **Right real equivariance at a maximal compact argument**, from the factorization and the
twisted continuity. -/
theorem right_real_at_compact (hdeg : 2 ≤ degree) (lsm : LocalVectorsSmooth data holomorphic)
    (lsa : LocalScalarAnalytic data holomorphic)
    (tl : TwistedLocalContinuity data holomorphic SectionMultipliersXiSmooth.heightLaw)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (real : RealGL3) (compact : AdelicGL) (compactMembership : inMaximalCompact compact)
    (binary : BinaryAdelicGL) :
    (edgeStd data holomorphic
        (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)).val
        (lineLevi 1 binary * compact) =
      (edgeStd data holomorphic sectionValue).val (lineLevi 1 binary * compact * atInfinity real) := by
  obtain ⟨lam, meromorphic, factorization⟩ :=
    EdgeFactorization.exists_factorization data holomorphic hdeg lsm lsa
  obtain ⟨epsilon, epsilon_pos, lam_analytic⟩ := EdgeFactorization.exists_analytic_radius meromorphic
  set radius : ℝ := min (epsilon / 2) (1 / 4)
  have radius_pos : 0 < radius := lt_min (half_pos epsilon_pos) (by norm_num)
  have radius_lt : radius < epsilon :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self epsilon_pos)
  have radius_small : radius ≤ 1 / 4 := min_le_right _ _
  have ballInside := closedBall_subset_localHalfPlane (degree := degree) hdeg radius_small
  have law := SectionMultipliersXiSmooth.heightLaw
  have normalizerNonzero : ∀ parameter : ℂ,
      EdgeFactorization.levelFactor degree binary parameter ≠ 0 := fun parameter =>
    ParabolicInvariance.normPower_ne_zero _ _
  have normalizerInverseAnalytic : ∀ parameter : ℂ,
      AnalyticAt ℂ (fun parameter => (EdgeFactorization.levelFactor degree binary parameter)⁻¹)
        parameter := fun parameter =>
    (EdgeFactorization.levelFactor_analytic degree binary parameter).inv
      (normalizerNonzero parameter)
  have normalizerInverseContinuous : Continuous
      (fun parameter : ℂ => (EdgeFactorization.levelFactor degree binary parameter)⁻¹) :=
    continuous_iff_continuousAt.2 fun parameter => (normalizerInverseAnalytic parameter).continuousAt
  let sections : ℂ → SectionSpace.inducedSections data .plane cohomologicalPoint := fun z =>
    ⟨SectionMultipliers.twist SectionMultipliersXi.logXi real z sectionValue.val,
      SectionMultipliers.isInduced_twist data cohomologicalPoint law real z sectionValue.val
        sectionValue.property⟩
  let localFamily : ℂ → ℂ → ℂ := fun parameter z =>
    (EdgeFactorization.levelFactor degree binary parameter)⁻¹ *
      localScalar data holomorphic (sections z) parameter compact binary
  let localTranslate : ℂ → ℂ := fun parameter =>
    (EdgeFactorization.levelFactor degree binary parameter)⁻¹ *
      localScalar data holomorphic sectionValue parameter (compact * atInfinity real) binary
  have sections_zero : sections 0 =
      RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue :=
    Subtype.ext (SectionMultipliers.twist_zero SectionMultipliersXi.logXi real sectionValue.val)
  have integral : IsIntegralArgument compact := isIntegralArgument_of_compact compactMembership
  have integralTranslate : IsIntegralArgument (compact * atInfinity real) :=
    isIntegralArgument_mul_atInfinity compactMembership real
  have scalarDifferentiable : DifferentiableOn ℂ lam
      (closedBall cohomologicalPoint radius \ {cohomologicalPoint}) := by
    intro parameter membership
    have different : parameter ≠ cohomologicalPoint := membership.2
    have inside : dist parameter cohomologicalPoint < epsilon :=
      lt_of_le_of_lt (mem_closedBall.1 membership.1) radius_lt
    exact (lam_analytic parameter different inside).differentiableAt.differentiableWithinAt
  have localDifferentiable : ∀ z : ℂ, ‖z‖ < 1 →
      DifferentiableOn ℂ (fun parameter => localFamily parameter z)
        (closedBall cohomologicalPoint radius) := by
    intro z _ parameter membership
    exact ((normalizerInverseAnalytic parameter).mul
      ((lsa (sections z) compact integral binary) parameter (ballInside membership))
      ).differentiableAt.differentiableWithinAt
  have localContinuous : ContinuousOn (fun p : ℂ × ℂ => localFamily p.1 p.2)
      (closedBall cohomologicalPoint radius ×ˢ ball (0 : ℂ) 1) := by
    have twisted := tl sectionValue real compact compactMembership binary radius 1 ballInside
    exact (normalizerInverseContinuous.comp continuous_fst).continuousOn.mul twisted
  have factorize : ∀ z : ℂ, ‖z‖ < 1 → ∀ᶠ parameter in 𝓝[≠] cohomologicalPoint,
      RightEquivariance.sectionContinuation data holomorphic (sections z) parameter
          (lineLevi 1 binary * compact) = lam parameter * localFamily parameter z := by
    intro z _
    filter_upwards [factorization (sections z) compact integral binary] with parameter equation
    have nonzero := normalizerNonzero parameter
    calc RightEquivariance.sectionContinuation data holomorphic (sections z) parameter
          (lineLevi 1 binary * compact)
        = (EdgeFactorization.levelFactor degree binary parameter)⁻¹ *
            (EdgeFactorization.levelFactor degree binary parameter *
              RightEquivariance.sectionContinuation data holomorphic (sections z) parameter
                (lineLevi 1 binary * compact)) := (inv_mul_cancel_left₀ nonzero _).symm
      _ = (EdgeFactorization.levelFactor degree binary parameter)⁻¹ *
            (lam parameter * localScalar data holomorphic (sections z) parameter compact binary) := by
          rw [equation]
      _ = lam parameter * localFamily parameter z := by
          change _ = lam parameter * ((EdgeFactorization.levelFactor degree binary parameter)⁻¹ *
            localScalar data holomorphic (sections z) parameter compact binary)
          ring
  have factorizeTranslate : ∀ᶠ parameter in 𝓝[≠] cohomologicalPoint,
      RightEquivariance.sectionContinuation data holomorphic sectionValue parameter
          (lineLevi 1 binary * compact * atInfinity real) =
        lam parameter * localTranslate parameter := by
    have associate : lineLevi 1 binary * compact * atInfinity real =
        lineLevi 1 binary * (compact * atInfinity real) := mul_assoc _ _ _
    filter_upwards [factorization sectionValue (compact * atInfinity real) integralTranslate binary]
      with parameter equation
    have nonzero := normalizerNonzero parameter
    rw [associate]
    calc RightEquivariance.sectionContinuation data holomorphic sectionValue parameter
          (lineLevi 1 binary * (compact * atInfinity real))
        = (EdgeFactorization.levelFactor degree binary parameter)⁻¹ *
            (EdgeFactorization.levelFactor degree binary parameter *
              RightEquivariance.sectionContinuation data holomorphic sectionValue parameter
                (lineLevi 1 binary * (compact * atInfinity real))) :=
          (inv_mul_cancel_left₀ nonzero _).symm
      _ = (EdgeFactorization.levelFactor degree binary parameter)⁻¹ *
            (lam parameter * localScalar data holomorphic sectionValue parameter
              (compact * atInfinity real) binary) := by rw [equation]
      _ = lam parameter * localTranslate parameter := by
          change _ = lam parameter * ((EdgeFactorization.levelFactor degree binary parameter)⁻¹ *
            localScalar data holomorphic sectionValue parameter (compact * atInfinity real)
              binary)
          ring
  have translateEquation : ∀ parameter : ℂ, parameter ≠ cohomologicalPoint →
      dist parameter cohomologicalPoint < radius →
      localTranslate parameter = localFamily parameter (parameter - cohomologicalPoint) := by
    intro parameter _ _
    exact congrArg (fun vector => (EdgeFactorization.levelFactor degree binary parameter)⁻¹ *
      vecScalar data vector binary)
      (RightEquivariance.localFlatValue_twist data holomorphic law sectionValue real parameter
        compact).symm
  have datum := RightEquivariance.diagonalDatum_of_factorization data holomorphic sectionValue real
    (lineLevi 1 binary * compact) sections sections_zero lam localFamily localTranslate radius 1
    radius_pos one_pos scalarDifferentiable localDifferentiable localContinuous factorize
    factorizeTranslate translateEquation
  exact RightEquivariance.value_eq_of_diagonalDatum data holomorphic sectionValue real
    (lineLevi 1 binary * compact) datum

/-- **Right real equivariance** of the standard operator. -/
theorem right_real_of_inputs (hdeg : 2 ≤ degree) (lsm : LocalVectorsSmooth data holomorphic)
    (lsa : LocalScalarAnalytic data holomorphic)
    (tl : TwistedLocalContinuity data holomorphic SectionMultipliersXiSmooth.heightLaw)
    (real : RealGL3)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    (edgeStd data holomorphic
        (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)).val =
      fun argument => (edgeStd data holomorphic sectionValue).val (argument * atInfinity real) :=
  EdgeTransport.LineCovariant.eq_of_compact
    (edgeStd_covariant data holomorphic
      (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue))
    ((edgeStd_covariant data holomorphic sectionValue).rightTranslate (atInfinity real))
    (fun compact compactMembership binary =>
      right_real_at_compact data holomorphic hdeg lsm lsa tl sectionValue real compact
        compactMembership binary)

/-- **The edge standard operator, from the four analytic inputs.** -/
theorem edgeStandardOperator_of_inputs (hdeg : 2 ≤ degree)
    (lsm : LocalVectorsSmooth data holomorphic) (lsa : LocalScalarAnalytic data holomorphic)
    (llv : LocalLiftVector data holomorphic) (llr : LocalLiftRealization data holomorphic)
    (lss : LocalLiftScalarSmooth data holomorphic)
    (tl : TwistedLocalContinuity data holomorphic SectionMultipliersXiSmooth.heightLaw) :
    EdgeStandardOperator data holomorphic := by
  have hecl : EdgeCompactLift data holomorphic :=
    edgeCompactLift_of_inputs data holomorphic hdeg lsm lsa
      (localCircleLift_of_parts data holomorphic llv llr)
  exact
    { smooth_real := fun sectionValue argument =>
        smooth_real_of_inputs data holomorphic hdeg lsm lsa lss sectionValue argument
      right_real := fun real sectionValue =>
        right_real_of_inputs data holomorphic hdeg lsm lsa tl real sectionValue
      smooth_lift := fun function induced lift =>
        smooth_lift_of_inputs data holomorphic hecl function induced lift }

end EdgeAssembly

end TernaryPeriodPolynomials.EdgeConvergence

namespace TernaryPeriodPolynomials.EdgeConvergence

open TernaryPeriodPolynomials.EdgeConvergence.EdgeInputs in
/-- **The edge standard operator at `n = 3`**, from the four analytic inputs on the local Hilbert
standard integral (see `EdgeInputs`). -/
theorem edgeStandardOperator_three {n : ℕ} (hn : n = 3) (data : InducingData n)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (lsm : LocalVectorsSmooth data holomorphic) (lsa : LocalScalarAnalytic data holomorphic)
    (llv : LocalLiftVector data holomorphic) (llr : LocalLiftRealization data holomorphic)
    (lss : LocalLiftScalarSmooth data holomorphic)
    (tl : TwistedLocalContinuity data holomorphic SectionMultipliersXiSmooth.heightLaw) :
    EdgeStandard.EdgeStandardOperator data holomorphic :=
  EdgeAssembly.edgeStandardOperator_of_inputs data holomorphic (by omega) lsm lsa llv llr lss tl

open TernaryPeriodPolynomials.EdgeConvergence.EdgeInputs in
/-- **Totality of the standard relation on plane source cocycles at `n = 3`**: the `existsIntegral`
input of `GraphReduction.standard_graph_of_eisenstein` for `n = 3`, from the four analytic inputs
on the local Hilbert standard integral. -/
theorem related_total_three {n : ℕ} (hn : n = 3) (data : InducingData n)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (lsm : LocalVectorsSmooth data holomorphic) (lsa : LocalScalarAnalytic data holomorphic)
    (llv : LocalLiftVector data holomorphic) (llr : LocalLiftRealization data holomorphic)
    (lss : LocalLiftScalarSmooth data holomorphic)
    (tl : TwistedLocalContinuity data holomorphic SectionMultipliersXiSmooth.heightLaw) :
    ∀ plane : TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace.sourceCocycles
        data .plane,
      ∃ line, TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardRelation.Related
        data plane line :=
  EdgeStandard.related_total_of_edgeStandardOperator data holomorphic
    (edgeStandardOperator_three hn data holomorphic lsm lsa llv llr lss tl)

end TernaryPeriodPolynomials.EdgeConvergence
