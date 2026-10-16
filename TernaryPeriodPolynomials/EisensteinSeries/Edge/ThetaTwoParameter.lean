module

public import TernaryPeriodPolynomials.EisensteinSeries.Edge.GodementCompact
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.ThetaIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RegularizedTestFamilies

@[expose] public section


/-!
# The theta integral is jointly continuous in a pair of parameters and the point

The library proves that the vector-valued theta integral
`VectorThetaIntegral.total data family (tensorTest (tests s) finiteTest) point s` is holomorphic in
the single parameter `s` that drives both the test and the character
(`UniformVectorIntegral.differentiable`), bounded on compacts (`CompactThetaIntegral.total_bound`)
and continuous in the point (`GodementCompact.total_continuousOn`). This file proves the
two-parameter version: the test depends on a pair `p = (s, z)`, the character parameter is `p.1`,
and the integral is continuous in `(p, point)` on `pairs ×ˢ points` for compact `pairs`, `points`
(`total_continuousOn`).

The only hypotheses on the family of tests are separate continuity in the pair and uniform
Schwartz bounds on compact sets of pairs. The uniform bounds make the tests equi-Lipschitz, which
gives joint continuity of `(p, v) ↦ tests p v` (`joint_continuousOn`); the theta series is then a
dominated sum of jointly continuous terms (`banachTheta_continuousOn`), and the integral is
dominated by the two-parameter copy of `CompactThetaIntegral.exists_bound` (`exists_bound`).
The regularized tests `BanachSchwartzRegularization.regularize (tests p)` satisfy the same
hypotheses, which gives `regularized_continuousOn` for the continuation including the outer
character.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzRegularization
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LargeThetaIntegral

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein.ThetaTwoParameter

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source]

/-- A Schwartz map is Lipschitz with constant its `(0, 1)` seminorm. -/
theorem schwartz_lipschitz (test : SchwartzMap RealSpace Source) (first second : RealSpace) :
    ‖test first - test second‖ ≤ SchwartzMap.seminorm ℂ 0 1 test * ‖first - second‖ := by
  refine (convex_univ : Convex ℝ (Set.univ : Set RealSpace)).norm_image_sub_le_of_norm_fderiv_le
    (f := test) (fun x _ => test.differentiableAt) ?_ (Set.mem_univ second) (Set.mem_univ first)
  intro x _
  calc ‖fderiv ℝ test x‖ = ‖iteratedFDeriv ℝ 1 test x‖ :=
        (norm_iteratedFDeriv_one (𝕜 := ℝ) (f := ⇑test) (x := x)).symm
    _ ≤ SchwartzMap.seminorm ℂ 0 1 test := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ test 1 x

/-- A family of tests that is continuous in the pair for each value and uniformly Schwartz-bounded
on a set of pairs is jointly continuous in the pair and the value there. -/
theorem joint_continuousOn (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value))
    (pairs : Set (ℂ × ℂ)) (bounded : UniformSchwartzBounds.Bounded (tests '' pairs)) :
    ContinuousOn (fun x : (ℂ × ℂ) × RealSpace => tests x.1 x.2) (pairs ×ˢ Set.univ) := by
  obtain ⟨constant, _, constantBound⟩ := bounded 0 1
  intro x _
  obtain ⟨center, value⟩ := x
  let majorant : (ℂ × ℂ) × RealSpace → ℝ := fun y =>
    constant * ‖y.2 - value‖ + ‖tests y.1 value - tests center value‖
  have majorantContinuous : Continuous majorant :=
    (continuous_const.mul ((continuous_snd.sub continuous_const).norm)).add
      (((pointwise value).comp continuous_fst).sub continuous_const).norm
  have majorantZero : majorant (center, value) = 0 := by simp [majorant]
  have majorantTendsto : Tendsto majorant (nhdsWithin (center, value) (pairs ×ˢ Set.univ)) (nhds 0) := by
    have result := majorantContinuous.continuousAt (x := (center, value)) |>.tendsto
    rw [majorantZero] at result
    exact result.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    ?_ majorantTendsto)
  filter_upwards [self_mem_nhdsWithin] with y membership
  calc ‖tests y.1 y.2 - tests center value‖
      = ‖(tests y.1 y.2 - tests y.1 value) + (tests y.1 value - tests center value)‖ := by
        congr 1; abel
    _ ≤ ‖tests y.1 y.2 - tests y.1 value‖ + ‖tests y.1 value - tests center value‖ := norm_add_le _ _
    _ ≤ majorant y := by
        refine add_le_add ?_ le_rfl
        exact (schwartz_lipschitz (tests y.1) y.2 value).trans
          (mul_le_mul_of_nonneg_right (constantBound (tests y.1) ⟨y.1, membership.1, rfl⟩) (norm_nonneg _))

/-- Each term of the adelic theta series is jointly continuous in the pair and the point. -/
theorem matrixTerm_continuousOn (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value))
    (pairs : Set (ℂ × ℂ)) (bounded : UniformSchwartzBounds.Bounded (tests '' pairs))
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (points : Set AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) :
    ContinuousOn (fun q : (ℂ × ℂ) × AdelicGL => BanachAdelicTheta.matrixTerm
      (BanachAdelicTheta.tensorTest (tests q.1) finiteTest) q.2 binary matrix) (pairs ×ˢ points) := by
  have matrixContinuous : Continuous (fun q : (ℂ × ℂ) × AdelicGL =>
      q.2⁻¹.val * matrix.map rationalAdele * binary.val) :=
    ((Units.continuous_val.comp continuous_snd.inv).matrix_mul continuous_const).matrix_mul
      continuous_const
  have finitePart : Continuous (fun q : (ℂ × ℂ) × AdelicGL =>
      finiteTest (RectangularTransport.finite (q.2⁻¹.val * matrix.map rationalAdele * binary.val))) :=
    finiteContinuous.comp (AdelicSchwartzTheta.finite_continuous.comp matrixContinuous)
  have realPart : ContinuousOn (fun q : (ℂ × ℂ) × AdelicGL =>
      tests q.1 (RectangularTransport.archimedean
        (q.2⁻¹.val * matrix.map rationalAdele * binary.val))) (pairs ×ˢ points) :=
    (joint_continuousOn tests pointwise pairs bounded).comp
      (continuous_fst.prodMk (AdelicSchwartzTheta.archimedean_continuous.comp matrixContinuous)).continuousOn
      (fun q membership => ⟨membership.1, Set.mem_univ _⟩)
  exact finitePart.continuousOn.smul realPart

/-- The adelic theta series is jointly continuous in the pair and the point. -/
theorem banachTheta_continuousOn [CompleteSpace Source] (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value))
    (pairs : Set (ℂ × ℂ)) (bounded : UniformSchwartzBounds.Bounded (tests '' pairs))
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest)
    (points : Set AdelicGL) (pointsCompact : IsCompact points) (binary : BinaryAdelicGL) :
    ContinuousOn (fun q : (ℂ × ℂ) × AdelicGL => BanachAdelicTheta.fullTheta
      (BanachAdelicTheta.tensorTest (tests q.1) finiteTest) q.2 binary) (pairs ×ˢ points) := by
  obtain ⟨majorant, summableMajorant, _, majorantBound⟩ := UniformThetaMajorants.adelic
    (tests '' pairs) bounded finiteTest finiteContinuous finiteSupport (points ×ˢ {binary})
    (pointsCompact.prod isCompact_singleton)
  exact continuousOn_tsum (fun matrix => matrixTerm_continuousOn tests pointwise pairs bounded
      finiteTest finiteContinuous points binary matrix) summableMajorant
    (fun matrix q membership => majorantBound (tests q.1) ⟨q.1, membership.1, rfl⟩ (q.2, binary)
      ⟨membership.2, Set.mem_singleton _⟩ matrix)

/-- The vector-valued theta series is jointly continuous in the pair and the point. -/
theorem fullTheta_continuousOn [CompleteSpace Source] {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value))
    (pairs : Set (ℂ × ℂ)) (bounded : UniformSchwartzBounds.Bounded (tests '' pairs))
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest)
    (points : Set AdelicGL) (pointsCompact : IsCompact points) (binary : BinaryAdelicGL) :
    ContinuousOn (fun q : (ℂ × ℂ) × AdelicGL => VectorTheta.fullTheta data family
      (BanachAdelicTheta.tensorTest (tests q.1) finiteTest) q.2 binary) (pairs ×ˢ points) :=
  (BanachCuspDecay.evaluation data family continuous binary).continuous.comp_continuousOn
    (banachTheta_continuousOn tests pointwise pairs bounded finiteTest finiteContinuous finiteSupport
      points pointsCompact binary)

/-- The inner character of a fixed determinant is continuous in the parameter. -/
theorem innerCharacter_continuous {degree : ℕ} (data : InducingData degree) (binary : BinaryAdelicGL) :
    Continuous (fun parameter : ℂ =>
      GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary)) := by
  have equality : (fun parameter : ℂ =>
      GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary)) =
      fun parameter => GodementIntegral.innerCharacter data 0 (GeneralLinearGroup.det binary) *
        Complex.exp (parameter * (Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) : ℂ)) := by
    funext parameter
    exact LargeThetaIntegral.character_factor data parameter _
  rw [equality]
  fun_prop

/-- The theta integrand is jointly continuous in the pair and the point. -/
theorem integrand_continuousOn [CompleteSpace Source] {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value))
    (pairs : Set (ℂ × ℂ)) (bounded : UniformSchwartzBounds.Bounded (tests '' pairs))
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest)
    (points : Set AdelicGL) (pointsCompact : IsCompact points) (binary : BinaryAdelicGL) :
    ContinuousOn (fun q : (ℂ × ℂ) × AdelicGL => VectorThetaIntegral.integrand data family
      (BanachAdelicTheta.tensorTest (tests q.1) finiteTest) q.2 q.1.1 binary) (pairs ×ˢ points) := by
  have character : Continuous (fun q : (ℂ × ℂ) × AdelicGL =>
      GodementIntegral.innerCharacter data q.1.1 (GeneralLinearGroup.det binary)) :=
    (innerCharacter_continuous data binary).comp (continuous_fst.comp continuous_fst)
  exact character.continuousOn.mul (fullTheta_continuousOn data family continuous tests pointwise
    pairs bounded finiteTest finiteContinuous finiteSupport points pointsCompact binary)

/-- The weight exponent is bounded along a compact set of pairs. -/
theorem exists_weight (degree : ℕ) (pairs : Set (ℂ × ℂ)) (compact : IsCompact pairs) :
    ∃ weight : ℝ, 0 ≤ weight ∧
      ∀ pair ∈ pairs, |WeightedAbsoluteTheta.exponent degree pair.1| ≤ weight := by
  obtain ⟨weightBound, weightBounded⟩ := compact.exists_bound_of_continuousOn
    (f := fun pair : ℂ × ℂ => WeightedAbsoluteTheta.exponent degree pair.1)
    ((UniformVectorIntegral.exponent_continuous degree).comp continuous_fst).continuousOn
  refine ⟨max weightBound 0, le_max_right _ _, fun pair membership => ?_⟩
  have result : |WeightedAbsoluteTheta.exponent degree pair.1| ≤ weightBound := by
    have bound := weightBounded pair membership
    rwa [Real.norm_eq_abs] at bound
  exact result.trans (le_max_left _ _)

/-- Pointwise bound of the theta integrand over a compact set of pairs and points. -/
theorem integrand_bound [CompleteSpace Source] {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (points : Set AdelicGL)
    (pointsCompact : IsCompact points) (pairs : Set (ℂ × ℂ)) (compact : IsCompact pairs)
    (bounded : UniformSchwartzBounds.Bounded (tests '' pairs)) (binary : BinaryAdelicGL) :
    ∃ bound : ℝ, ∀ pair ∈ pairs, ∀ point ∈ points,
      ‖VectorThetaIntegral.integrand data family
        (BanachAdelicTheta.tensorTest (tests pair) finiteTest) point pair.1 binary‖ ≤ bound := by
  obtain ⟨thetaBound, thetaNonnegative, thetaBounded⟩ := CompactThetaIntegral.theta_bound data family
    continuous (tests '' pairs) bounded finiteTest finiteContinuous finiteSupport points
    pointsCompact binary
  obtain ⟨weight, weightNonnegative, weightBounds⟩ := exists_weight degree pairs compact
  refine ⟨Real.exp (weight * |height binary|) * thetaBound, ?_⟩
  intro pair pairMembership point pointMembership
  rw [VectorThetaIntegral.norm_integrand]
  apply mul_le_mul _ (thetaBounded (tests pair) ⟨pair, pairMembership, rfl⟩ point pointMembership)
    (norm_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (weightBounds pair pairMembership) (abs_nonneg _))

/-- The theta integrand as a function of the pair, the point and the binary variable. -/
def integrands [CompleteSpace Source] {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (tests : ℂ × ℂ → SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (pair : ℂ × ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) : ℂ :=
  VectorThetaIntegral.integrand data family (BanachAdelicTheta.tensorTest (tests pair) finiteTest)
    point pair.1 binary

/-- Slices of the theta integrand are continuous in the pair. -/
theorem integrands_pair_continuousOn [CompleteSpace Source] {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value))
    (pairs : Set (ℂ × ℂ)) (bounded : UniformSchwartzBounds.Bounded (tests '' pairs))
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest)
    (points : Set AdelicGL) (pointsCompact : IsCompact points) (point : AdelicGL)
    (membership : point ∈ points) (binary : BinaryAdelicGL) :
    ContinuousOn (fun pair => integrands data family tests finiteTest pair point binary) pairs := by
  have embed : ContinuousOn (fun pair : ℂ × ℂ => (pair, point)) pairs :=
    (continuous_id.prodMk continuous_const).continuousOn
  have composed := (integrand_continuousOn data family continuous tests pointwise pairs bounded
    finiteTest finiteContinuous finiteSupport points pointsCompact binary).comp embed
    (fun pair pairMembership => ⟨pairMembership, membership⟩)
  exact composed

/-- Slices of the theta integrand are continuous in the point. -/
theorem integrands_point_continuousOn [CompleteSpace Source] {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value))
    (pairs : Set (ℂ × ℂ)) (bounded : UniformSchwartzBounds.Bounded (tests '' pairs))
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest)
    (points : Set AdelicGL) (pointsCompact : IsCompact points) (pair : ℂ × ℂ)
    (membership : pair ∈ pairs) (binary : BinaryAdelicGL) :
    ContinuousOn (fun point => integrands data family tests finiteTest pair point binary) points := by
  have embed : ContinuousOn (fun point : AdelicGL => (pair, point)) points :=
    (continuous_const.prodMk continuous_id).continuousOn
  have composed := (integrand_continuousOn data family continuous tests pointwise pairs bounded
    finiteTest finiteContinuous finiteSupport points pointsCompact binary).comp embed
    (fun point pointMembership => ⟨membership, pointMembership⟩)
  exact composed

/-- The supremum of the theta integrand over pairs and points is measurable in the binary variable. -/
theorem bound_measurable [CompleteSpace Source] {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value))
    (pairs : Set (ℂ × ℂ)) (bounded : UniformSchwartzBounds.Bounded (tests '' pairs))
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest)
    (points : Set AdelicGL) (pointsCompact : IsCompact points) :
    Measurable (SeparateSupremum.bound (integrands data family tests finiteTest) pairs points) :=
  SeparateSupremum.measurable (integrands data family tests finiteTest) pairs points
    (fun pair _ point _ => VectorThetaIntegral.integrand_measurable data family continuous
      (tests pair) finiteTest finiteContinuous finiteSupport point pair.1)
    (fun point membership binary => integrands_pair_continuousOn data family continuous tests
      pointwise pairs bounded finiteTest finiteContinuous finiteSupport points pointsCompact point
      membership binary)
    (fun pair membership binary => integrands_point_continuousOn data family continuous tests
      pointwise pairs bounded finiteTest finiteContinuous finiteSupport points pointsCompact pair
      membership binary)

/-- The supremum of the theta integrand over pairs and points is integrable on the fundamental
domain. -/
theorem bound_integrable [CompleteSpace Source] {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value))
    (zeroValue : ∀ pair, tests pair 0 = 0)
    (zeroFourier : ∀ pair, FourierTransform.fourier (tests pair) 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (pairs : Set (ℂ × ℂ)) (compact : IsCompact pairs)
    (bounded : UniformSchwartzBounds.Bounded (tests '' pairs))
    (points : Set AdelicGL) (pointsCompact : IsCompact points) :
    IntegrableOn (fun binary => (SeparateSupremum.bound (integrands data family tests
      (RectangularAdelicPoisson.finiteTest finiteScale offset)) pairs points binary : ℂ))
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  have boundNonnegative := SeparateSupremum.nonnegative (integrands data family tests
    (RectangularAdelicPoisson.finiteTest finiteScale offset)) pairs points
  have boundMeasurable := bound_measurable data family continuous tests pointwise pairs bounded
    (RectangularAdelicPoisson.finiteTest finiteScale offset) (finiteTest_continuous finiteScale offset)
    (finiteTest_compactSupport finiteScale offset) points pointsCompact
  obtain ⟨weight, weightNonnegative, weightBounds⟩ := exists_weight degree pairs compact
  obtain ⟨scalarPower, scalarPowerBound⟩ := exists_nat_gt (2 * weight)
  obtain ⟨cuspPower, cuspPowerBound⟩ := exists_nat_gt weight
  obtain ⟨largeConstant, largeNonnegative, largeBound⟩ := CompactVectorTheta.large_log data family
    continuous (tests '' pairs) bounded finiteScale offset points pointsCompact scalarPower cuspPower
  obtain ⟨smallConstant, smallNonnegative, smallBound⟩ := CompactVectorTheta.small_log data family
    continuous (tests '' pairs) bounded finiteScale offset points pointsCompact scalarPower cuspPower
  refine ShellDecay.integrable_domain _ (Complex.measurable_ofReal.comp boundMeasurable) ?_
    ((largeConstant + smallConstant) * Real.exp (weight * |Real.log 2|))
    ((scalarPower : ℝ) - 2 * weight) ((cuspPower : ℝ) - weight)
    (by positivity) (sub_pos.mpr scalarPowerBound) (sub_pos.mpr cuspPowerBound) ?_
  · intro rational binary
    congr 1
    exact SeparateSupremum.congr (integrands data family tests
      (RectangularAdelicPoisson.finiteTest finiteScale offset)) pairs points _ _
      (fun pair _ point _ => VectorThetaIntegral.rational_invariant data family _ point pair.1
        rational binary)
  · intro integer natural shellParameter
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (boundNonnegative _)]
    apply SeparateSupremum.bounded (integrands data family tests
      (RectangularAdelicPoisson.finiteTest finiteScale offset)) pairs points _ _ (by positivity)
    intro pair membership point pointMembership
    change ‖VectorThetaIntegral.integrand data family _ point pair.1 _‖ ≤ _
    rw [VectorThetaIntegral.norm_integrand]
    simp only [SiegelShells.parameterize, height, SiegelChartFunctions.determinant_log_chart]
    have heightNonnegative : 0 ≤ (natural : ℝ) + shellParameter.2.2.1.val :=
      add_nonneg (Nat.cast_nonneg _) shellParameter.2.2.1.property.1
    have horizontal : |shellParameter.2.2.2.1.val| ≤ 1 := abs_le.mpr shellParameter.2.2.2.1.property
    exact UniformExponentialWeights.two_rates _ largeConstant smallConstant scalarPower cuspPower
      (WeightedAbsoluteTheta.exponent degree pair.1) weight
      ((integer : ℝ) + shellParameter.2.1.val) ((natural : ℝ) + shellParameter.2.2.1.val)
      (Real.log 2) largeNonnegative smallNonnegative (weightBounds pair membership)
      heightNonnegative
      (fun nonnegative => largeBound (tests pair) ⟨pair, membership, rfl⟩ (zeroValue pair) point
        pointMembership shellParameter.1 shellParameter.2.2.2.2 _ _ _ nonnegative
        heightNonnegative horizontal)
      (fun nonpositive => smallBound (tests pair) ⟨pair, membership, rfl⟩ (zeroFourier pair) point
        pointMembership shellParameter.1 shellParameter.2.2.2.2 _ _ _ nonpositive
        heightNonnegative horizontal)

/-- An integrable dominating function for the theta integrand, uniform over compact sets of pairs
and of points. -/
theorem exists_bound [CompleteSpace Source] {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value))
    (bounded : ∀ pairs : Set (ℂ × ℂ), IsCompact pairs → UniformSchwartzBounds.Bounded (tests '' pairs))
    (zeroValue : ∀ pair, tests pair 0 = 0)
    (zeroFourier : ∀ pair, FourierTransform.fourier (tests pair) 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (points : Set AdelicGL) (pointsCompact : IsCompact points)
    (pairs : Set (ℂ × ℂ)) (compact : IsCompact pairs) :
    ∃ bound : BinaryAdelicGL → ℝ, IntegrableOn bound BinaryFundamentalDomain.domain BinaryHaar.measure ∧
      ∀ pair ∈ pairs, ∀ point ∈ points, ∀ binary,
        ‖VectorThetaIntegral.integrand data family
          (BanachAdelicTheta.tensorTest (tests pair)
            (RectangularAdelicPoisson.finiteTest finiteScale offset)) point pair.1 binary‖ ≤ bound binary := by
  have integrable := bound_integrable data family continuous tests pointwise zeroValue zeroFourier
    finiteScale offset pairs compact (bounded pairs compact) points pointsCompact
  have boundNonnegative := SeparateSupremum.nonnegative (integrands data family tests
    (RectangularAdelicPoisson.finiteTest finiteScale offset)) pairs points
  refine ⟨SeparateSupremum.bound (integrands data family tests
      (RectangularAdelicPoisson.finiteTest finiteScale offset)) pairs points, ?_,
    fun pair membership point pointMembership binary =>
    SeparateSupremum.dominates (integrands data family tests
        (RectangularAdelicPoisson.finiteTest finiteScale offset)) pairs points binary
      (integrand_bound data family continuous tests _ (finiteTest_continuous finiteScale offset)
        (finiteTest_compactSupport finiteScale offset) points pointsCompact pairs compact
        (bounded pairs compact) binary)
      pair membership point pointMembership⟩
  change Integrable _ (BinaryHaar.measure.restrict BinaryFundamentalDomain.domain)
  apply integrable.norm.congr
  exact Filter.Eventually.of_forall (fun binary => by
    beta_reduce
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (boundNonnegative binary)])

/-- Regularizing a family of tests preserves continuity in the pair for each value. -/
theorem regularize_pointwise (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value)) (value : RealSpace) :
    Continuous (fun pair => regularize (tests pair) value) := by
  simp only [regularize, killFourier, killValue, _root_.sub_apply, _root_.smul_apply, dilate_apply]
  exact ((pointwise value).sub (pointwise _)).sub
    (((pointwise _).sub (pointwise _)).const_smul (64 : ℂ))

variable [CompleteSpace Source]

/-- The theta integral is jointly continuous in the pair and the point on compact sets. -/
theorem total_continuousOn {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value))
    (bounded : ∀ pairs : Set (ℂ × ℂ), IsCompact pairs → UniformSchwartzBounds.Bounded (tests '' pairs))
    (zeroValue : ∀ pair, tests pair 0 = 0)
    (zeroFourier : ∀ pair, FourierTransform.fourier (tests pair) 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (pairs : Set (ℂ × ℂ)) (pairsCompact : IsCompact pairs)
    (points : Set AdelicGL) (pointsCompact : IsCompact points) :
    ContinuousOn (fun q : (ℂ × ℂ) × AdelicGL => VectorThetaIntegral.total data family
      (BanachAdelicTheta.tensorTest (tests q.1)
        (RectangularAdelicPoisson.finiteTest finiteScale offset)) q.2 q.1.1) (pairs ×ˢ points) := by
  obtain ⟨bound, integrable, bounds⟩ := exists_bound data family continuous tests pointwise bounded
    zeroValue zeroFourier finiteScale offset points pointsCompact pairs pairsCompact
  unfold VectorThetaIntegral.total
  apply continuousOn_of_dominated (bound := bound)
  · intro q _
    exact (VectorThetaIntegral.integrand_measurable data family continuous (tests q.1) _
      (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset)
      q.2 q.1.1).aestronglyMeasurable
  · intro q membership
    exact Eventually.of_forall (fun binary => bounds q.1 membership.1 q.2 membership.2 binary)
  · exact integrable
  · exact Eventually.of_forall (fun binary => integrand_continuousOn data family continuous tests
      pointwise pairs (bounded pairs pairsCompact) _ (finiteTest_continuous finiteScale offset)
      (finiteTest_compactSupport finiteScale offset) points pointsCompact binary)

omit [CompleteSpace Source] in
/-- Regularizing a family of tests preserves uniform Schwartz bounds on compact sets of pairs. -/
theorem regularized_bounded (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (bounded : ∀ pairs : Set (ℂ × ℂ), IsCompact pairs → UniformSchwartzBounds.Bounded (tests '' pairs))
    (pairs : Set (ℂ × ℂ)) (compact : IsCompact pairs) :
    UniformSchwartzBounds.Bounded ((fun pair => regularize (tests pair)) '' pairs) := by
  simpa only [Set.image_image] using
    RegularizedTestFamilies.bounded (tests '' pairs) (bounded pairs compact)

/-- The outer character of the determinant is jointly continuous in the pair and the point. -/
theorem outer_continuous {degree : ℕ} (data : InducingData degree) :
    Continuous (fun q : (ℂ × ℂ) × AdelicGL =>
      GodementIntegral.outerCharacter data q.1.1 (GeneralLinearGroup.det q.2)) := by
  have result := GodementCompact.outerCharacter_comp_continuous data
    (parameters := fun q : (ℂ × ℂ) × AdelicGL => q.1.1) (points := fun q : (ℂ × ℂ) × AdelicGL => q.2)
    (continuous_fst.comp continuous_fst) continuous_snd
  exact result

/-- The regularized theta continuation, including the outer character, is jointly continuous in the
pair and the point on compact sets. -/
theorem regularized_continuousOn {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ × ℂ → SchwartzMap RealSpace Source)
    (pointwise : ∀ value, Continuous (fun pair => tests pair value))
    (bounded : ∀ pairs : Set (ℂ × ℂ), IsCompact pairs → UniformSchwartzBounds.Bounded (tests '' pairs))
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (pairs : Set (ℂ × ℂ)) (pairsCompact : IsCompact pairs)
    (points : Set AdelicGL) (pointsCompact : IsCompact points) :
    ContinuousOn (fun q : (ℂ × ℂ) × AdelicGL => VectorThetaIntegral.continuation data family
      (BanachAdelicTheta.tensorTest (BanachSchwartzRegularization.regularize (tests q.1))
        (RectangularAdelicPoisson.finiteTest finiteScale offset)) q.1.1 q.2) (pairs ×ˢ points) := by
  have thetaContinuous := total_continuousOn data family continuous
    (fun pair => regularize (tests pair)) (regularize_pointwise tests pointwise)
    (regularized_bounded tests bounded)
    (fun pair => regularize_zero (tests pair)) (fun pair => regularize_fourier_zero (tests pair))
    finiteScale offset pairs pairsCompact points pointsCompact
  unfold VectorThetaIntegral.continuation
  exact (outer_continuous data).continuousOn.mul thetaContinuous

end TernaryPeriodPolynomials.EdgeEisenstein.ThetaTwoParameter
