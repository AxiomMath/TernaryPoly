module

public import TernaryPeriodPolynomials.EisensteinSeries.Edge.TwistRecovery
public import TernaryPeriodPolynomials.EisensteinSeries.Edge.ThetaTwoParameter
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliersFlat
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.RightEquivarianceAnalytic
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.StandardEisenstein
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.Equivariance
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Helpers

@[expose] public section


/-!
# Right real equivariance of the Eisenstein value at `s₀`, in every degree

Fix a plane section `f` at `s₀`, a real `h` and an adelic `g`; let `F` and `F'` be the flat families of
`f` and of `R(h) f = f(· h)`. The claim `E(R(h) f)(g) = E(f)(g h)` compares the continuation of the
flat family `F'` at `g` with that of the (non-flat) analytic family `s ↦ F_s(· h)` at `g`, at `s₀`.

With `ρ_h(y) = Ξ(y h)/Ξ(y)` and the twisted sections `Φ_z = ρ_h^z · R(h) f`, the flat family of `Φ_z` is
`ρ_h^z F'` (`twist_flat`), and on the diagonal `z = s - s₀` it is `F_s(· h)` (`twist_diagonal`, H78's
`flat_twist_diagonal`). `TwistRecovery.exists_twisted_continuation` gives ONE explicit two-variable
function `C(z, s, y)` which, for every `z`, continues the Eisenstein series of `ρ_h^z F'`, and along
the diagonal continues that of `F_s(· h)`. It is built from universal meromorphic coefficients and
Godement theta integrals of the twisted tests, so on a small circle around `s₀` it is jointly
continuous in `(s, z)` (`ThetaTwoParameter`), and for each `z` it is holomorphic on the punctured
disc. The two-variable maximum-modulus argument of H78
(`RightEquivariance.eq_of_axis_diagonal`) then identifies the axis value `E(R(h) f)(s₀, g)` with the
limit of the diagonal, `E(f)(s₀, g h)`, with no control on the pole orders of the coefficients.

Result: `edgeEisensteinOperator : EdgeStandardEisenstein.EdgeEisensteinOperator data holomorphic`,
for every degree.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology Metric
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfilePackages
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms (fixedSmooth)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel (finiteCongruence)

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein.EdgeEisensteinRight

variable {degree : ℕ} (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)

/-- The twisted section `Φ_z = ρ_h^z · f(· h)`. -/
def twistSection (real : RealGL3) (z : ℂ)
    (f : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    SectionSpace.inducedSections data .plane cohomologicalPoint :=
  ⟨SectionMultipliers.twist SectionMultipliersXi.logXi real z f.val,
    SectionMultipliers.isInduced_twist data cohomologicalPoint SectionMultipliersXiSmooth.heightLaw
      real z f.val f.property⟩

/-- The flat family of `Φ_z` is `ρ_h^z` times the flat family of `f(· h)`. -/
theorem twist_flat (real : RealGL3) (z : ℂ)
    (f : SectionSpace.inducedSections data .plane cohomologicalPoint) (parameter : ℂ)
    (point : AdelicGL) :
    SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real z point *
        (SectionSpace.linearFlatExtension data holomorphic
          (RealTranslations.sectionRightReal data .plane cohomologicalPoint real f)).val
          parameter point =
      (SectionSpace.linearFlatExtension data holomorphic (twistSection data real z f)).val
        parameter point := by
  rw [SectionMultipliersFlat.linearFlatExtension_eq_xi data holomorphic
      SectionMultipliersXiSmooth.heightLaw
      (RealTranslations.sectionRightReal data .plane cohomologicalPoint real f) parameter point,
    SectionMultipliersFlat.linearFlatExtension_eq_xi data holomorphic
      SectionMultipliersXiSmooth.heightLaw (twistSection data real z f) parameter point]
  change _ * (_ * f.val (point * atInfinity real)) =
    _ * (SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real z point *
      f.val (point * atInfinity real))
  ring

/-- On the diagonal `z = s - s₀`, the twisted flat family is the right translate of that of `f`. -/
theorem twist_diagonal (real : RealGL3)
    (f : SectionSpace.inducedSections data .plane cohomologicalPoint) (parameter : ℂ)
    (point : AdelicGL) :
    SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real
        (parameter - cohomologicalPoint) point *
        (SectionSpace.linearFlatExtension data holomorphic
          (RealTranslations.sectionRightReal data .plane cohomologicalPoint real f)).val
          parameter point =
      (SectionSpace.linearFlatExtension data holomorphic f).val parameter
        (point * atInfinity real) := by
  rw [twist_flat data holomorphic real (parameter - cohomologicalPoint) f parameter point]
  exact SectionMultipliersFlat.flat_twist_diagonal data holomorphic
    SectionMultipliersXiSmooth.heightLaw f real parameter point

/-- A punctured closed disc around `s₀` free of poles of the coefficients and of zeros of the
regularization factor. -/
theorem exists_radius {size : ℕ} (coefficients : ℂ → Fin size → ℂ)
    (meromorphic : ∀ index parameter,
      MeromorphicAt (fun parameter => coefficients parameter index) parameter) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ parameter ∈ closedBall cohomologicalPoint radius,
      parameter ≠ cohomologicalPoint →
        (∀ index, AnalyticAt ℂ (fun parameter => coefficients parameter index) parameter) ∧
          GodementScalingFactor.regularizationFactor data parameter ≠ 0 := by
  have analytic : ∀ᶠ parameter in 𝓝[≠] cohomologicalPoint,
      ∀ index, AnalyticAt ℂ (fun parameter => coefficients parameter index) parameter :=
    Filter.eventually_all.mpr
      (fun index => (meromorphic index cohomologicalPoint).eventually_analyticAt)
  have factorAnalytic : AnalyticAt ℂ (GodementScalingFactor.regularizationFactor data)
      cohomologicalPoint :=
    (GodementScalingFactor.factor_differentiable data).analyticAt cohomologicalPoint
  have nonzero : ∀ᶠ parameter in 𝓝[≠] cohomologicalPoint,
      GodementScalingFactor.regularizationFactor data parameter ≠ 0 := by
    rcases factorAnalytic.eventually_eq_zero_or_eventually_ne_zero with zero | different
    · exfalso
      have analyticEverywhere : AnalyticOnNhd ℂ (GodementScalingFactor.regularizationFactor data)
          Set.univ := fun point _ =>
        (GodementScalingFactor.factor_differentiable data).analyticAt point
      have everywhere := analyticEverywhere.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ cohomologicalPoint)
        (by filter_upwards [zero] with point vanishes; simpa using vanishes)
      let large : ℂ := (((1 - (degree : ℝ)) / 2 + 1 : ℝ) : ℂ)
      have halfPlane : (1 - (degree : ℝ)) / 2 < large.re := by
        have real : large.re = (1 - (degree : ℝ)) / 2 + 1 := Complex.ofReal_re _
        rw [real]
        linarith
      exact GodementScalingFactor.factor_nonzero data large halfPlane
        (by simpa using everywhere (Set.mem_univ large))
    · exact different
  obtain ⟨epsilon, positive, ballProperty⟩ :=
    Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp (analytic.and nonzero))
  refine ⟨epsilon / 2, half_pos positive, fun parameter membership different => ?_⟩
  exact ballProperty (lt_of_le_of_lt (mem_closedBall.mp membership) (half_lt_self positive))
    different

/-! ### Regularity of the explicit continuation -/

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem godement_differentiableAt
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (testsHolomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact →
      UniformSchwartzBounds.Bounded (tests '' compact))
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL)
    (parameter : ℂ) (nonzero : GodementScalingFactor.regularizationFactor data parameter ≠ 0) :
    DifferentiableAt ℂ (fun parameter => VectorGodementContinuation.continuation data family
      (tests parameter) finiteScale offset parameter point) parameter := by
  have numerator : Differentiable ℂ (fun parameter => VectorThetaIntegral.continuation data family
      (BanachAdelicTheta.tensorTest (BanachSchwartzRegularization.regularize (tests parameter))
        (RectangularAdelicPoisson.finiteTest finiteScale offset)) parameter point) :=
    (ZeroConstantThetaIntegral.outer_differentiable data (Matrix.GeneralLinearGroup.det point)).mul
      (UniformVectorIntegral.differentiable data family continuous
        (fun parameter => BanachSchwartzRegularization.regularize (tests parameter))
        (RegularizedTestFamilies.pointwise_differentiable tests testsHolomorphic)
        (fun compact compactIs => RegularizedTestFamilies.family_bounded tests compact
          (bounded compact compactIs))
        (fun parameter => BanachSchwartzRegularization.regularize_zero (tests parameter))
        (fun parameter => BanachSchwartzRegularization.regularize_fourier_zero (tests parameter))
        finiteScale offset point)
  exact (numerator parameter).div ((GodementScalingFactor.factor_differentiable data) parameter)
    nonzero

theorem interpolation_differentiableAt {KeyType : Type} [Fintype KeyType]
    (families : KeyType → RealFamily data) (boxes : KeyType → Boxes) (point : AdelicGL)
    (parameter : ℂ) (nonzero : GodementScalingFactor.regularizationFactor data parameter ≠ 0) :
    DifferentiableAt ℂ (fun parameter =>
      FlatProfileInterpolation.continuation data families boxes parameter point) parameter := by
  unfold FlatProfileInterpolation.continuation FiniteGodementFamilies.continuation
  apply DifferentiableAt.fun_sum
  intro index _
  exact (differentiableAt_const _).mul (godement_differentiableAt data (families index.1).family
    (families index.1).continuous (families index.1).tests (families index.1).holomorphic
    (families index.1).bounded _ _ point parameter nonzero)

theorem average_differentiableAt (function : ℂ → AdelicGL → ℂ) (point : AdelicGL)
    (parameter : ℂ)
    (differentiable : ∀ y, DifferentiableAt ℂ (fun parameter => function parameter y) parameter) :
    DifferentiableAt ℂ (fun parameter =>
      FiniteSectionProjection.average data (function parameter) point) parameter := by
  unfold FiniteSectionProjection.average
  exact (differentiableAt_const _).mul (DifferentiableAt.fun_sum (fun index _ => differentiable _))

theorem average_continuousOn {Space : Type*} [TopologicalSpace Space]
    (function : Space → AdelicGL → ℂ) (point : AdelicGL) (set : Set Space)
    (continuous : ∀ y, ContinuousOn (fun x => function x y) set) :
    ContinuousOn (fun x => FiniteSectionProjection.average data (function x) point) set := by
  unfold FiniteSectionProjection.average
  exact continuousOn_const.mul (continuousOn_finsetSum _ (fun index _ => continuous _))

/-- The theta part of one term of the twisted interpolated continuation. -/
def thetaPart (real : RealGL3) (family : TwistRecovery.SupportedFamily data) (scale : FiniteAdelesˣ)
    (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (pair : ℂ × ℂ) : ℂ :=
  VectorThetaIntegral.continuation data family.base.family
    (BanachAdelicTheta.tensorTest
      (BanachSchwartzRegularization.regularize (TwistRecovery.twistedTests real family pair))
      (RectangularAdelicPoisson.finiteTest scale offset)) pair.1 point

/-- The regularization factor as a function of the pair. -/
def factorPart (pair : ℂ × ℂ) : ℂ := GodementScalingFactor.regularizationFactor data pair.1

/-- The interpolated Godement continuation of the twisted families, written out. -/
theorem twisted_interpolation_eq (real : RealGL3) {KeyType : Type} [Fintype KeyType]
    (families : KeyType → TwistRecovery.SupportedFamily data) (boxes : KeyType → Boxes)
    (point : AdelicGL) (pair : ℂ × ℂ) :
    FlatProfileInterpolation.continuation data
      (fun key => TwistRecovery.twistFamily real (families key) (fun _ => pair.2)
        (differentiable_const pair.2)) boxes pair.1 point =
      ∑ index : FlatProfileInterpolation.Index boxes,
        (boxes index.1).coefficients index.2.val *
          (thetaPart data real (families index.1)
            (FiniteLatticeMeasure.rationalScale (boxes index.1).scale) index.2.val.out point pair /
            factorPart data pair) := by
  simp only [FlatProfileInterpolation.continuation, FiniteGodementFamilies.continuation,
    VectorGodementContinuation.continuation, TwistRecovery.twistFamily, Prod.mk.eta,
    thetaPart, factorPart]
  rfl

theorem thetaPart_continuousOn (real : RealGL3) (family : TwistRecovery.SupportedFamily data)
    (scale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL)
    (pairs : Set (ℂ × ℂ)) (pairsCompact : IsCompact pairs) :
    ContinuousOn (thetaPart data real family scale offset point) pairs := by
  have joint := ThetaTwoParameter.regularized_continuousOn data family.base.family
    family.base.continuous (TwistRecovery.twistedTests real family)
    (TwistRecovery.twistedTests_pointwise real family)
    (TwistRecovery.twistedTests_bounded real family) scale offset pairs pairsCompact
    {point} isCompact_singleton
  have maps : Set.MapsTo (fun pair : ℂ × ℂ => (pair, point)) pairs (pairs ×ˢ {point}) :=
    fun _ membership => ⟨membership, rfl⟩
  have h2 := joint.comp (continuous_id.prodMk continuous_const).continuousOn maps
  exact h2.congr (fun pair _ => rfl)

theorem factorPart_continuous : Continuous (factorPart data) :=
  (GodementScalingFactor.factor_differentiable data).continuous.comp continuous_fst

/-- Joint continuity in `(s, z)` of one term of the interpolated twisted continuation. -/
theorem twisted_component_continuousOn (real : RealGL3) (family : TwistRecovery.SupportedFamily data)
    (scale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (coefficient : ℂ)
    (pairs : Set (ℂ × ℂ)) (pairsCompact : IsCompact pairs)
    (nonzero : ∀ pair ∈ pairs, factorPart data pair ≠ 0) (point : AdelicGL) :
    ContinuousOn (fun pair : ℂ × ℂ => coefficient *
      (thetaPart data real family scale offset point pair / factorPart data pair)) pairs :=
  continuousOn_const.mul ((thetaPart_continuousOn data real family scale offset point pairs
    pairsCompact).div (factorPart_continuous data).continuousOn nonzero)

/-- Joint continuity in `(s, z)` of the interpolated Godement continuation of the twisted
families. -/
theorem twisted_interpolation_continuousOn (real : RealGL3) {KeyType : Type} [Fintype KeyType]
    (families : KeyType → TwistRecovery.SupportedFamily data) (boxes : KeyType → Boxes)
    (pairs : Set (ℂ × ℂ)) (pairsCompact : IsCompact pairs)
    (nonzero : ∀ pair ∈ pairs, GodementScalingFactor.regularizationFactor data pair.1 ≠ 0)
    (point : AdelicGL) :
    ContinuousOn (fun pair : ℂ × ℂ => FlatProfileInterpolation.continuation data
      (fun key => TwistRecovery.twistFamily real (families key) (fun _ => pair.2)
        (differentiable_const pair.2)) boxes pair.1 point) pairs := by
  refine ContinuousOn.congr ?_ (fun pair _ =>
    twisted_interpolation_eq data real families boxes point pair)
  exact continuousOn_finsetSum _ (fun index _ =>
    twisted_component_continuousOn data real (families index.1)
      (FiniteLatticeMeasure.rationalScale (boxes index.1).scale) index.2.val.out
      ((boxes index.1).coefficients index.2.val) pairs pairsCompact nonzero point)

/-! ### Right real equivariance -/

/-- **Right real equivariance** of the Eisenstein value at `s₀`: `E(R(h) f)(g) = E(f)(g h)`. -/
theorem right_real_value (f : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (real : RealGL3) (argument : AdelicGL) :
    (SectionSpace.sectionEisensteinValue data holomorphic
        (RealTranslations.sectionRightReal data .plane cohomologicalPoint real f)).val argument =
      (SectionSpace.sectionEisensteinValue data holomorphic f).val (argument * atInfinity real) := by
  classical
  let shifted := RealTranslations.sectionRightReal data .plane cohomologicalPoint real f
  have shiftedFlat := (SectionSpace.linearFlatExtension data holomorphic shifted).property
  obtain ⟨size, coefficients, families, constants, meromorphic, continues⟩ :=
    TwistRecovery.exists_twisted_continuation real shiftedFlat
  -- the explicit continuation `C(z, s, y)`
  let recovered : ℂ → ℂ → AdelicGL → ℂ := fun z parameter point =>
    ∑ index, coefficients parameter index *
      FiniteSectionProjection.average data (fun point' => constants index *
        FlatProfileInterpolation.continuation data
          (fun key => TwistRecovery.twistFamily real (families index key) (fun _ => z)
            (differentiable_const z))
          (UniversalFiniteProfiles.boxes data) parameter point') point
  let twistedValue : ℂ → ℂ → AdelicGL → ℂ := fun z =>
    EisensteinValue.chosenContinuation data holomorphic
      (SectionSpace.linearFlatExtension data holomorphic (twistSection data real z f))
  -- for every `z`, `C(z, ·, ·)` continues the flat family of `Φ_z`
  have fixedContinues : ∀ z, IsEisensteinContinuation
      (SectionSpace.linearFlatExtension data holomorphic (twistSection data real z f)).val
      (recovered z) := by
    intro z
    refine ContinuationAlgebra.transfer (continues (fun _ => z) (differentiable_const z)) 0 ?_
    intro parameter _ point
    exact twist_flat data holomorphic real z f parameter point
  -- along the diagonal `z = s - s₀`, it continues `s ↦ F_s(· h)`
  have diagonalContinues : IsEisensteinContinuation
      (fun parameter point =>
        (SectionSpace.linearFlatExtension data holomorphic f).val parameter (point * atInfinity real))
      (fun parameter point => ∑ index, coefficients parameter index *
        FiniteSectionProjection.average data (fun point' => constants index *
          FlatProfileInterpolation.continuation data
            (fun key => TwistRecovery.twistFamily real (families index key)
              (fun parameter => parameter - cohomologicalPoint)
              (differentiable_id.sub_const cohomologicalPoint))
            (UniversalFiniteProfiles.boxes data) parameter point') point) := by
    refine ContinuationAlgebra.transfer (continues (fun parameter => parameter - cohomologicalPoint)
      (differentiable_id.sub_const cohomologicalPoint)) 0 ?_
    intro parameter _ point
    exact twist_diagonal data holomorphic real f parameter point
  have diagonalEq : ∀ parameter, recovered (parameter - cohomologicalPoint) parameter argument =
      ∑ index, coefficients parameter index *
        FiniteSectionProjection.average data (fun point' => constants index *
          FlatProfileInterpolation.continuation data
            (fun key => TwistRecovery.twistFamily real (families index key)
              (fun parameter => parameter - cohomologicalPoint)
              (differentiable_id.sub_const cohomologicalPoint))
            (UniversalFiniteProfiles.boxes data) parameter point') argument := by
    intro parameter
    simp only [recovered, FlatProfileInterpolation.continuation,
      FiniteGodementFamilies.continuation, TwistRecovery.twistFamily]
    rfl
  -- the analytic continuations of `F` and `F'`
  have originalSpec := EisensteinValue.chosenContinuation_spec data holomorphic
    (SectionSpace.linearFlatExtension data holomorphic f)
  have rightSpec := CompactEquivariance.eisensteinContinuation_right _ _ originalSpec.1
    (atInfinity real)
  have diagonalGerm :=
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.continuation_germs_agree
      diagonalContinues rightSpec argument cohomologicalPoint
  -- the radius
  obtain ⟨radius, radiusPositive, good⟩ := exists_radius data coefficients meromorphic
  -- the two-variable family
  let family : ℂ → ℂ → ℂ := fun parameter z =>
    if parameter = cohomologicalPoint then twistedValue z cohomologicalPoint argument
    else recovered z parameter argument
  have zeroSection : twistSection data real 0 f = shifted :=
    Subtype.ext (SectionMultipliers.twist_zero _ _ _)
  have axis : EisensteinValue.chosenContinuation data holomorphic
      (SectionSpace.linearFlatExtension data holomorphic shifted) cohomologicalPoint argument =
      family cohomologicalPoint 0 := by
    show _ = (if cohomologicalPoint = cohomologicalPoint then twistedValue 0 cohomologicalPoint argument
      else recovered 0 cohomologicalPoint argument)
    rw [ite_eq_left rfl]
    show _ = EisensteinValue.chosenContinuation data holomorphic
      (SectionSpace.linearFlatExtension data holomorphic (twistSection data real 0 f))
      cohomologicalPoint argument
    rw [zeroSection]
  have diagonal : ∀ᶠ parameter in 𝓝[≠] cohomologicalPoint,
      EisensteinValue.chosenContinuation data holomorphic
          (SectionSpace.linearFlatExtension data holomorphic f) parameter
          (argument * atInfinity real) =
        family parameter (parameter - cohomologicalPoint) := by
    filter_upwards [diagonalGerm, self_mem_nhdsWithin] with parameter germ different
    have ne : parameter ≠ cohomologicalPoint := different
    show _ = (if parameter = cohomologicalPoint then twistedValue (parameter - cohomologicalPoint)
        cohomologicalPoint argument
      else recovered (parameter - cohomologicalPoint) parameter argument)
    rw [ite_eq_right ne, diagonalEq]
    exact germ.symm
  have holo : ∀ z : ℂ, ‖z‖ < 1 →
      DifferentiableOn ℂ (fun parameter => family parameter z) (closedBall cohomologicalPoint radius) := by
    intro z _ point membership
    by_cases center : point = cohomologicalPoint
    · rw [center]
      have zSpec := EisensteinValue.chosenContinuation_spec data holomorphic
        (SectionSpace.linearFlatExtension data holomorphic (twistSection data real z f))
      have germ :=
        TernaryPeriodPolynomials.EisensteinRegularization.Helpers.continuation_germs_agree
          (fixedContinues z) zSpec.1 argument cohomologicalPoint
      have near : (fun parameter => family parameter z) =ᶠ[𝓝 cohomologicalPoint]
          (fun parameter => twistedValue z parameter argument) := by
        filter_upwards [eventually_nhdsWithin_iff.mp germ] with parameter close
        by_cases same : parameter = cohomologicalPoint
        · simp only [family, ite_eq_left same, twistedValue]
          rw [same]
        · simp only [family, ite_eq_right same]
          exact close same
      exact ((zSpec.2 argument).differentiableAt.congr_of_eventuallyEq near).differentiableWithinAt
    · have away : (fun parameter => family parameter z) =ᶠ[𝓝 point]
          (fun parameter => recovered z parameter argument) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds center] with parameter outside
        simp only [family, ite_eq_right (show parameter ≠ cohomologicalPoint from outside)]
      obtain ⟨analyticCoefficients, factorNonzero⟩ := good point membership center
      have differentiable : DifferentiableAt ℂ (fun parameter => recovered z parameter argument)
          point := by
        apply DifferentiableAt.fun_sum
        intro index _
        exact (analyticCoefficients index).differentiableAt.mul
          (average_differentiableAt data _ argument point (fun y =>
            (differentiableAt_const _).mul (interpolation_differentiableAt data _ _ y point
              factorNonzero)))
      exact (differentiable.congr_of_eventuallyEq away).differentiableWithinAt
  have circle : ContinuousOn (fun pair : ℂ × ℂ => family pair.1 pair.2)
      (sphere cohomologicalPoint radius ×ˢ ball (0 : ℂ) 1) := by
    have onSphere : ∀ pair ∈ sphere cohomologicalPoint radius ×ˢ ball (0 : ℂ) 1,
        pair.1 ∈ closedBall cohomologicalPoint radius ∧ pair.1 ≠ cohomologicalPoint := by
      intro pair membership
      refine ⟨sphere_subset_closedBall membership.1, fun same => ?_⟩
      have distance := mem_sphere.mp membership.1
      rw [same, dist_self] at distance
      exact radiusPositive.ne distance
    have equal : Set.EqOn (fun pair : ℂ × ℂ => family pair.1 pair.2)
        (fun pair : ℂ × ℂ => recovered pair.2 pair.1 argument)
        (sphere cohomologicalPoint radius ×ˢ ball (0 : ℂ) 1) := by
      intro pair membership
      simp only [family, ite_eq_right (onSphere pair membership).2]
    refine ContinuousOn.congr ?_ equal
    have compactPairs : IsCompact (sphere cohomologicalPoint radius ×ˢ closedBall (0 : ℂ) 1) :=
      (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
    have pairsNonzero : ∀ pair ∈ sphere cohomologicalPoint radius ×ˢ closedBall (0 : ℂ) 1,
        GodementScalingFactor.regularizationFactor data pair.1 ≠ 0 := by
      intro pair membership
      have sameRadius := onSphere (pair.1, 0) ⟨membership.1, mem_ball_self one_pos⟩
      exact (good pair.1 sameRadius.1 sameRadius.2).2
    apply continuousOn_finsetSum
    intro index _
    apply ContinuousOn.mul
    · intro pair membership
      exact (((good pair.1 (onSphere pair membership).1 (onSphere pair membership).2).1
        index).continuousAt.comp continuous_fst.continuousAt).continuousWithinAt
    · apply average_continuousOn data
      intro y
      apply continuousOn_const.mul
      exact (twisted_interpolation_continuousOn data real (families index)
        (UniversalFiniteProfiles.boxes data) _ compactPairs pairsNonzero y).mono
        (Set.prod_mono subset_rfl ball_subset_closedBall)
  have result := RightEquivariance.eq_of_axis_diagonal
    (A := fun parameter => EisensteinValue.chosenContinuation data holomorphic
      (SectionSpace.linearFlatExtension data holomorphic shifted) parameter argument)
    (B := fun parameter => EisensteinValue.chosenContinuation data holomorphic
      (SectionSpace.linearFlatExtension data holomorphic f) parameter (argument * atInfinity real))
    radiusPositive one_pos holo circle axis
    (originalSpec.2 (argument * atInfinity real)).continuousAt diagonal
  change EisensteinValue.eisensteinValue data holomorphic
      (SectionSpace.linearFlatExtension data holomorphic shifted) argument =
    EisensteinValue.eisensteinValue data holomorphic
      (SectionSpace.linearFlatExtension data holomorphic f) (argument * atInfinity real)
  exact result

/-- **The edge Eisenstein operator**: right real equivariance of the Eisenstein value at `s₀`, in
every degree (in particular `n = 3`, the edge of absolute convergence). -/
theorem edgeEisensteinOperator :
    EdgeStandardEisenstein.EdgeEisensteinOperator data holomorphic where
  right_real real sectionValue argument := right_real_value data holomorphic sectionValue real argument

end TernaryPeriodPolynomials.EdgeEisenstein.EdgeEisensteinRight
