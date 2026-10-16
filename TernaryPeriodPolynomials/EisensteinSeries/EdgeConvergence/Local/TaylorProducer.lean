module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.MajorantCompact
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.AnalyticTaylor
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.TaylorBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RightOrbitAnalyticity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.Decomposition

@[expose] public section


/-!
# Taylor majorants of the local standard integrand

The Taylor coefficients of the right orbit of the plane cusp lift at the point
`w⁻¹ n(u) g` are controlled by the plane weight `planeWeight (binary, unit)` of a plane
decomposition of that point, times a bound uniform on the maximal compact. For an argument `g`
with integral finite part this weight is at most a constant times a negative power of the local
height of `u`, so the coefficients have an integrable geometric majorant on the local radical for
`Re s > -n/2 - 1`. This produces `LocalTaylorMajorant` and, through `localValue_expansion`, the
real smoothness of the local Hilbert standard integral.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise NNReal
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

open CompactTaylorBounds CuspTaylorBounds AdelicTaylorBounds

/-- The sum of squares of the entries of the real inverse of an argument. -/
def inverseSquares (argument : AdelicGL) : ℝ :=
  ∑ index, ∑ column, ((realGroup argument).inv column index) ^ 2

theorem inverseSquares_nonneg (argument : AdelicGL) : 0 ≤ inverseSquares argument :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The constant bounding the plane weight of a decomposition of a point of the local integrand by
a power of the local height. -/
def localTaylorConstant (degree : ℕ) (parameter : ℂ) (argument : AdelicGL) : ℝ :=
  (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
      (binaryInductionExponent degree .plane parameter).re *
    (3 * Real.sqrt (inverseSquares argument + 1)) ^
      (-(-((degree : ℝ) + 6) / 2 - parameter.re))

theorem localTaylorConstant_nonneg (degree : ℕ) (parameter : ℂ) (argument : AdelicGL) :
    0 ≤ localTaylorConstant degree parameter argument := by
  have rootPositive : 0 < Real.sqrt (inverseSquares argument + 1) :=
    Real.sqrt_pos.mpr (by linarith [inverseSquares_nonneg argument])
  exact mul_nonneg (Real.rpow_nonneg (adeleNorm _).property _)
    (Real.rpow_nonneg (mul_pos three_pos rootPositive).le _)

/-- The plane weight of a plane decomposition of a point of the local standard integrand is at most
a constant times a power of the local height. -/
theorem planeWeight_le_localHeight {degree : ℕ} (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (argument : AdelicGL)
    (integral : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (finite : finiteGroup argument = GeneralLinearGroup.map integralEmbedding integral)
    (coordinates : LocalLine × LocalLine) (first second : Adeles) (binary : BinaryAdelicGL)
    (unit : Adelesˣ) (compact : AdelicGL) (compactMembership : inMaximalCompact compact)
    (decomposition : weyl⁻¹ * localRadical coordinates * argument =
      planeUnipotent first second * planeLevi binary unit * compact) :
    planeWeight degree parameter binary unit ≤ localTaylorConstant degree parameter argument *
      localHeight coordinates ^ (-((degree : ℝ) + 6) / 2 - parameter.re) := by
  have exponentNonpositive : -((degree : ℝ) + 6) / 2 - parameter.re ≤ 0 := by linarith
  have rootPositive : 0 < Real.sqrt (inverseSquares argument + 1) :=
    Real.sqrt_pos.mpr (by linarith [inverseSquares_nonneg argument])
  have scalePositive : 0 < 3 * Real.sqrt (inverseSquares argument + 1) :=
    mul_pos three_pos rootPositive
  have heightPositive : 0 < localHeight coordinates := localHeight_pos coordinates
  have cornerLower := corner_lower_bound argument integral finite (inverseSquares argument)
    le_rfl coordinates first second binary unit compact compactMembership decomposition
  have lower : localHeight coordinates ≤ (3 * Real.sqrt (inverseSquares argument + 1)) *
      (adeleNorm unit : ℝ) := (inv_mul_le_iff₀ scalePositive).mp cornerLower
  have powerBound := HeightMajorant.negative_power_bound heightPositive scalePositive lower
    exponentNonpositive
  have determinantNonneg : 0 ≤ (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
      (binaryInductionExponent degree .plane parameter).re :=
    Real.rpow_nonneg (adeleNorm _).property _
  have weightEquality : planeWeight degree parameter binary unit =
      (adeleNorm (GeneralLinearGroup.det
        (planeUnipotent first second * planeLevi binary unit * compact)) : ℝ) ^
          (binaryInductionExponent degree .plane parameter).re *
        (adeleNorm unit : ℝ) ^ (-((degree : ℝ) + 6) / 2 - parameter.re) :=
    InducedHeight.plane_weight_identity degree parameter first second binary unit compact
      compactMembership
  rw [weightEquality, ← decomposition, standardArgument_det_norm]
  unfold localTaylorConstant
  calc (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
        (binaryInductionExponent degree .plane parameter).re *
        (adeleNorm unit : ℝ) ^ (-((degree : ℝ) + 6) / 2 - parameter.re)
      ≤ (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
        (binaryInductionExponent degree .plane parameter).re *
        ((3 * Real.sqrt (inverseSquares argument + 1)) ^
          (-(-((degree : ℝ) + 6) / 2 - parameter.re)) *
            localHeight coordinates ^ (-((degree : ℝ) + 6) / 2 - parameter.re)) :=
        mul_le_mul_of_nonneg_left powerBound determinantNonneg
    _ = _ := by ring

/-- The arguments whose finite part is integral are stable under real right translation. -/
theorem integralArguments_mul_atInfinity (argument : AdelicGL)
    (membership : argument ∈ integralArguments) (real : RealGL3) :
    argument * atInfinity real ∈ integralArguments := by
  obtain ⟨integral, finite⟩ := membership
  refine ⟨integral, ?_⟩
  rw [map_mul, InducedContinuity.finiteGroup_atInfinity, mul_one]
  exact finite

local instance {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin order => Matrices) E) :=
  ContinuousMultilinearMap.normedAddCommGroup'

local instance {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin order => Matrices) E) :=
  ContinuousMultilinearMap.normedSpace'

/-- **The producer.** For parameters with `Re s > -n/2 - 1` and an argument with integral finite
part, the Taylor coefficients of the right orbits of the plane cusp lift at the points
`w⁻¹ n(u) g` of the local integrand have an integrable geometric majorant on a common ball. -/
theorem exists_localTaylorMajorant {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (argument : AdelicGL)
    (integral : argument ∈ integralArguments) :
    Nonempty (LocalTaylorMajorant data parameter function induced argument) := by
  obtain ⟨integralArgument, finite⟩ := integral
  obtain ⟨radius, positive, constant, constantNonnegative, bounded⟩ :=
    maximalCompact_uniform data .plane parameter function induced
  have exponent : -((degree : ℝ) + 6) / 2 - parameter.re =
      -((degree : ℝ) / 2 + 3 + parameter.re) := by ring
  refine ⟨{
    radius := radius
    radius_pos := positive
    bound := fun coordinates => (localTaylorConstant degree parameter argument * constant) *
      localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + parameter.re))
    integrable := ?_
    expansions := ?_
    dominates := ?_ }⟩
  · exact (localHeight_rpow_integrable ((degree : ℝ) / 2 + 3 + parameter.re)
      (by linarith)).const_mul _
  · intro coordinates
    obtain ⟨first, second, binary, unit, compact, membership, decomposition⟩ :=
      AdelicDecomposition.adelic_planeDecomposition (weyl⁻¹ * localRadical coordinates * argument)
    change HasFPowerSeriesOnBall (matrixOrbit data .plane parameter function induced
        (weyl⁻¹ * localRadical coordinates * argument))
      (coefficients (matrixOrbit data .plane parameter function induced
        (weyl⁻¹ * localRadical coordinates * argument)) 1) 1 radius
    rw [decomposition]
    exact (plane_decomposition_bound data parameter function induced positive constant bounded
      first second binary unit compact membership).1
  · intro coordinates order
    obtain ⟨first, second, binary, unit, compact, membership, decomposition⟩ :=
      AdelicDecomposition.adelic_planeDecomposition (weyl⁻¹ * localRadical coordinates * argument)
    have estimate := (plane_decomposition_bound data parameter function induced positive constant
      bounded first second binary unit compact membership).2 order
    have weight := planeWeight_le_localHeight parameter halfPlane argument integralArgument
      finite coordinates first second binary unit compact membership decomposition
    rw [exponent] at weight
    change ‖coefficients (matrixOrbit data .plane parameter function induced
      (weyl⁻¹ * localRadical coordinates * argument)) 1 order‖ ≤ _
    rw [decomposition]
    refine estimate.trans (mul_le_mul_of_nonneg_right ?_
      (pow_nonneg (inv_nonneg.mpr radius.property) order))
    show planeWeight degree parameter binary unit * constant ≤
      (localTaylorConstant degree parameter argument * constant) *
        localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + parameter.re))
    calc planeWeight degree parameter binary unit * constant
        ≤ (localTaylorConstant degree parameter argument *
            localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + parameter.re))) * constant :=
          mul_le_mul_of_nonneg_right weight constantNonnegative
      _ = _ := by ring

open AdelicTaylorBounds SmoothJets in
/-- Real smoothness of a function on a set of arguments stable under right translation by the real
group, from analyticity of its right orbits at the identity. -/
theorem smooth_of_analyticAt_one_on {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : AdelicGL → E) (arguments : Set AdelicGL)
    (stable : ∀ argument ∈ arguments, ∀ real : RealGL3, argument * atInfinity real ∈ arguments)
    (analytic : ∀ argument ∈ arguments, AnalyticAt ℝ (rightMatrix function argument) 1)
    (argument : AdelicGL) (membership : argument ∈ arguments) :
    Smooth (fun real : Fin 1 → RealGL3 => function (argument * atInfinity (real 0))) := by
  apply (SmoothAnalyticity.smooth_iff_analyticOn _).mpr
  intro matrices matricesMembership
  let real : RealGL3 := invertibleMatrix (matrices 0)
  have realValue : real.val = matrices 0 := by
    dsimp [real, invertibleMatrix]
    rw [dite_eq_left (matricesMembership 0)]
    rfl
  let linear := TranslatedJets.tupleLeftMulL (fun _ : Fin 1 => real.inv)
  have centered : linear matrices = 1 := by
    funext index
    have indexZero : index = 0 := Subsingleton.elim _ _
    subst index
    change real.inv * matrices 0 = 1
    rw [← realValue]
    exact real.inv_val
  have analytic' : AnalyticAt ℝ (rightMatrix function (argument * atInfinity real))
      (linear matrices) := by
    rw [centered]
    exact analytic _ (stable argument membership real)
  have composed := analytic'.compContinuousLinearMap
  apply (composed.congr ?_).analyticWithinAt
  filter_upwards [(domain_open 3 1).mem_nhds matricesMembership] with other otherMembership
  change function ((argument * atInfinity real) *
    atInfinity (invertibleMatrix (real.inv * other 0))) =
      function (argument * atInfinity (invertibleMatrix (other 0)))
  rw [show real.inv = real⁻¹.val from rfl,
    TranslatedJets.invertibleMatrix_mul_left real⁻¹ (other 0) (otherMembership 0),
    mul_assoc, ← RealTranslations.atInfinity_mul, mul_inv_cancel_left]

/-- The right orbit of the local standard integral under the real group is analytic at the
identity, for parameters with `Re s > -n/2 - 1` and arguments with integral finite part. -/
theorem localValue_analyticAt_one_of_integral {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (argument : AdelicGL)
    (integral : argument ∈ integralArguments) :
    AnalyticAt ℝ (rightMatrix (localValue data parameter function induced) argument) 1 :=
  localValue_analyticAt_one data parameter function induced argument
    (exists_localTaylorMajorant data parameter function induced halfPlane argument integral).some

/-- **Real smoothness of the local Hilbert standard integral** along the real right orbit of an
argument with integral finite part, with no majorant hypothesis, for `Re s > -n/2 - 1`. -/
theorem localValue_right_smooth_of_integral {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (argument : AdelicGL)
    (integral : argument ∈ integralArguments) :
    Smooth (fun real : Fin 1 → RealGL3 =>
      localValue data parameter function induced (argument * atInfinity (real 0))) :=
  smooth_of_analyticAt_one_on (localValue data parameter function induced) integralArguments
    integralArguments_mul_atInfinity
    (fun argument membership => localValue_analyticAt_one_of_integral data parameter function
      induced halfPlane argument membership) argument integral

end TernaryPeriodPolynomials.EdgeConvergence
