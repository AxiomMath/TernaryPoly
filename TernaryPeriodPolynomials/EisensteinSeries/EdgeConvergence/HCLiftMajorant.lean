module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftUniform
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.AnalyticFamilyTaylor
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.TaylorProducerFamily
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalMajorant

@[expose] public section


/-!
# Taylor majorants of the local integrand, uniform on a compact set of parameters

Original work by Claude Sonnet 5.5.

For a compact set of parameters inside the vertical strip `lower ≤ Re s ≤ upper`, `lower` in the half
plane `Re s > -n/2 - 1`, and an argument with integral finite part, the Taylor coefficients (at a
real tuple) of the orbit functions of the cusp lift at the points `w⁻¹ n(u) g` of the local
integrand of the twisted family have one integrable geometric majorant on one ball, valid for all
parameters of the set (`UniformMajorant`). This is the proof of
`exists_localFamilyTaylorMajorant` with the uniform bounds `HCLift.exists_uniform_bounds` at the
maximal compact in place of the parameter-wise ones, and with the plane weight bounded by its values
on the boundary lines of the strip.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix MeasureTheory
  Filter Topology
open scoped Matrix.Norms.Elementwise NNReal
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open CompactTaylorBounds FamilyCuspTaylor
open CuspTaylorBounds (planeWeight)

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCLift

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedAddCommGroup
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  ContinuousMultilinearMap.normedAddCommGroup'

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedSpace ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  ContinuousMultilinearMap.normedSpace'

/-- A common ball and an integrable geometric majorant of the Taylor coefficients of the local
integrand, for all parameters of a set. -/
structure UniformMajorant {degree arity : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices))
    (weight : (Fin arity → RealGL3) → ℝ) (parameters : Set ℂ)
    (real : Fin (arity + 1) → RealGL3) (argument : AdelicGL) where
  radius : ℝ≥0
  radius_pos : 0 < radius
  bound : LocalLine × LocalLine → ℝ
  integrable : Integrable bound localRadicalMeasure
  expansions : ∀ parameter ∈ parameters, ∀ coordinates, HasFPowerSeriesOnBall
    (FamilyCuspTaylor.matrixOrbit data .plane parameter
      (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter)
      (weyl⁻¹ * localRadical coordinates * argument))
    (localFamilySeries data parameter (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter) real argument
      coordinates)
    (fun index => (real index).val) radius
  dominates : ∀ parameter ∈ parameters, ∀ coordinates order,
    ‖localFamilySeries data parameter (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter) real argument
      coordinates order‖ ≤ bound coordinates * (radius : ℝ)⁻¹ ^ order

namespace UniformMajorant

variable {degree arity : ℕ} {data : InducingData degree}
  {holomorphic : PlaneEisensteinHolomorphic data}
  {family : (Fin arity → RealGL3) → AdelicGL → ℂ}
  {induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices)}
  {weight : (Fin arity → RealGL3) → ℝ} {parameters : Set ℂ}
  {real : Fin (arity + 1) → RealGL3} {argument : AdelicGL}

/-- The `LocalFamilyTaylorMajorant` at one parameter of the set. -/
def toMajorant (majorant : UniformMajorant data holomorphic family induced weight parameters real
    argument) (parameter : ℂ) (membership : parameter ∈ parameters) :
    LocalFamilyTaylorMajorant data parameter
      (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter) real argument where
  radius := majorant.radius
  radius_pos := majorant.radius_pos
  bound := majorant.bound
  integrable := majorant.integrable
  expansions := majorant.expansions parameter membership
  dominates := majorant.dominates parameter membership

end UniformMajorant

/-- **The uniform majorant.** -/
theorem exists_uniformMajorant {degree arity : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices))
    (weight : (Fin arity → RealGL3) → ℝ)
    (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (real : Fin (arity + 1) → RealGL3) (lower upper : ℝ)
    (lowerHalfPlane : -(degree : ℝ) / 2 - 1 < lower) (ordered : lower ≤ upper)
    {parameters : Set ℂ} (compact : IsCompact parameters)
    (strip : ∀ parameter ∈ parameters, lower ≤ parameter.re ∧ parameter.re ≤ upper)
    (argument : AdelicGL) (compactArgument : inMaximalCompact argument) :
    Nonempty (UniformMajorant data holomorphic family induced weight parameters real argument) := by
  obtain ⟨radius, positive, constant, nonnegative, bounded⟩ :=
    exists_uniform_bounds data holomorphic family induced weight lift weightSmooth real compact
  obtain ⟨integralArgument, finite⟩ := compactArgument.2
  have upperHalfPlane : -(degree : ℝ) / 2 - 1 < upper := lowerHalfPlane.trans_le ordered
  have lowerComplex : -(degree : ℝ) / 2 - 1 < ((lower : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact lowerHalfPlane
  have upperComplex : -(degree : ℝ) / 2 - 1 < ((upper : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact upperHalfPlane
  have exponentLower : -((degree : ℝ) + 6) / 2 - ((lower : ℝ) : ℂ).re =
      -((degree : ℝ) / 2 + 3 + lower) := by
    rw [Complex.ofReal_re]
    ring
  have exponentUpper : -((degree : ℝ) + 6) / 2 - ((upper : ℝ) : ℂ).re =
      -((degree : ℝ) / 2 + 3 + upper) := by
    rw [Complex.ofReal_re]
    ring
  refine ⟨{
    radius := radius
    radius_pos := positive
    bound := fun coordinates =>
      ((localTaylorConstant degree (lower : ℂ) argument +
        localTaylorConstant degree (upper : ℂ) argument) * constant) *
          localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower))
    integrable := ?_
    expansions := ?_
    dominates := ?_ }⟩
  · exact (localHeight_strip_integrable lower lowerHalfPlane).const_mul _
  · intro parameter membership coordinates
    obtain ⟨first, second, binary, unit, compact', compactMembership, decomposition⟩ :=
      AdelicDecomposition.adelic_planeDecomposition (weyl⁻¹ * localRadical coordinates * argument)
    change HasFPowerSeriesOnBall (FamilyCuspTaylor.matrixOrbit data .plane parameter
        (twistedAt data holomorphic family induced weight parameter)
        (twistedAt_induced data holomorphic family induced weight parameter)
        (weyl⁻¹ * localRadical coordinates * argument))
      (coefficients (FamilyCuspTaylor.matrixOrbit data .plane parameter
        (twistedAt data holomorphic family induced weight parameter)
        (twistedAt_induced data holomorphic family induced weight parameter)
        (weyl⁻¹ * localRadical coordinates * argument)) (fun index => (real index).val))
      (fun index => (real index).val) radius
    rw [decomposition]
    exact (FamilyCuspTaylor.plane_decomposition_bound data parameter
      (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter) real positive constant
      (bounded parameter membership) first second binary unit compact' compactMembership).1
  · intro parameter membership coordinates order
    obtain ⟨lowerBound, upperBound⟩ := strip parameter membership
    obtain ⟨first, second, binary, unit, compact', compactMembership, decomposition⟩ :=
      AdelicDecomposition.adelic_planeDecomposition (weyl⁻¹ * localRadical coordinates * argument)
    have estimate := (FamilyCuspTaylor.plane_decomposition_bound data parameter
      (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter) real positive constant
      (bounded parameter membership) first second binary unit compact' compactMembership).2 order
    have weightLower := planeWeight_le_localHeight (lower : ℂ) lowerComplex argument
      integralArgument finite.symm coordinates first second binary unit compact' compactMembership
      decomposition
    have weightUpper := planeWeight_le_localHeight (upper : ℂ) upperComplex argument
      integralArgument finite.symm coordinates first second binary unit compact' compactMembership
      decomposition
    rw [exponentLower] at weightLower
    rw [exponentUpper] at weightUpper
    have stripBound := planeWeight_strip_bound degree binary unit lower upper parameter lowerBound
      upperBound
    have heightPositive : 0 < localHeight coordinates := localHeight_pos coordinates
    have exponentOrder : -((degree : ℝ) / 2 + 3 + upper) ≤ -((degree : ℝ) / 2 + 3 + lower) := by
      linarith
    have powerOrder : localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + upper)) ≤
        localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower)) :=
      Real.rpow_le_rpow_of_exponent_le (one_le_localHeight coordinates) exponentOrder
    change ‖coefficients (FamilyCuspTaylor.matrixOrbit data .plane parameter
      (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter)
      (weyl⁻¹ * localRadical coordinates * argument)) (fun index => (real index).val) order‖ ≤ _
    rw [decomposition]
    refine estimate.trans (mul_le_mul_of_nonneg_right ?_
      (pow_nonneg (inv_nonneg.mpr radius.property) order))
    show planeWeight degree parameter binary unit * constant ≤
      ((localTaylorConstant degree (lower : ℂ) argument +
        localTaylorConstant degree (upper : ℂ) argument) * constant) *
          localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower))
    calc planeWeight degree parameter binary unit * constant
        ≤ (planeWeight degree (lower : ℂ) binary unit + planeWeight degree (upper : ℂ) binary unit) *
            constant := mul_le_mul_of_nonneg_right stripBound nonnegative
      _ ≤ ((localTaylorConstant degree (lower : ℂ) argument *
              localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower))) +
            (localTaylorConstant degree (upper : ℂ) argument *
              localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + upper)))) * constant :=
          mul_le_mul_of_nonneg_right (add_le_add weightLower weightUpper) nonnegative
      _ ≤ ((localTaylorConstant degree (lower : ℂ) argument *
              localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower))) +
            (localTaylorConstant degree (upper : ℂ) argument *
              localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower)))) * constant :=
          mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_left powerOrder
            (localTaylorConstant_nonneg degree (upper : ℂ) argument))) nonnegative
      _ = _ := by ring

end TernaryPeriodPolynomials.EdgeConvergence.HCLift
