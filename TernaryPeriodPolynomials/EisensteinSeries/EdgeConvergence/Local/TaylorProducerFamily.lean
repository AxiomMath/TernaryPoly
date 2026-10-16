module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.TaylorProducer
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.AnalyticFamilyTaylor
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FamilyCuspTaylor

@[expose] public section


/-!
# Taylor majorants of the local standard integrand of a vertex family

The family analogue of `LocalTaylorProducer`: for a family of plane sections with a smooth cusp
lift, a parameter with `Re s > -n/2 - 1` and an argument with integral finite part, the joint
Taylor coefficients, at any real vertices, of the cusp lift at the points `w⁻¹ n(u) g` have an
integrable geometric majorant on the local radical. This produces `LocalFamilyTaylorMajorant` and
the joint smoothness of the local Hilbert standard integral in the vertices and the translation.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise NNReal
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

open CompactTaylorBounds FamilyCuspTaylor
open CuspTaylorBounds (planeWeight)

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedAddCommGroup
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  ContinuousMultilinearMap.normedAddCommGroup'

local instance {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedSpace ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => (SmoothJets.MatrixTuples 3 arity.succ)) E) :=
  ContinuousMultilinearMap.normedSpace'

/-- **The family producer.** For a family of plane sections with a smooth cusp lift, a parameter
with `Re s > -n/2 - 1`, real vertices `real` and an argument with integral finite part, the joint
Taylor coefficients of the cusp lift at the points `w⁻¹ n(u) g` of the local integrand have an
integrable geometric majorant on a common ball. -/
theorem exists_localFamilyTaylorMajorant {degree arity : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (lift : HasSmoothCuspLift data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (real : Fin (arity + 1) → RealGL3)
    (argument : AdelicGL) (integral : argument ∈ integralArguments) :
    Nonempty (LocalFamilyTaylorMajorant data parameter function induced real argument) := by
  obtain ⟨integralArgument, finite⟩ := integral
  obtain ⟨radius, positive, constant, constantNonnegative, bounded⟩ :=
    FamilyCuspTaylor.maximalCompact_uniform data .plane parameter function induced lift real
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
    change HasFPowerSeriesOnBall (FamilyCuspTaylor.matrixOrbit data .plane parameter function
        induced (weyl⁻¹ * localRadical coordinates * argument))
      (coefficients (FamilyCuspTaylor.matrixOrbit data .plane parameter function induced
        (weyl⁻¹ * localRadical coordinates * argument)) (fun index => (real index).val))
      (fun index => (real index).val) radius
    rw [decomposition]
    exact (FamilyCuspTaylor.plane_decomposition_bound data parameter function induced real
      positive constant bounded first second binary unit compact membership).1
  · intro coordinates order
    obtain ⟨first, second, binary, unit, compact, membership, decomposition⟩ :=
      AdelicDecomposition.adelic_planeDecomposition (weyl⁻¹ * localRadical coordinates * argument)
    have estimate := (FamilyCuspTaylor.plane_decomposition_bound data parameter function induced
      real positive constant bounded first second binary unit compact membership).2 order
    have weight := planeWeight_le_localHeight parameter halfPlane argument integralArgument
      finite coordinates first second binary unit compact membership decomposition
    rw [exponent] at weight
    change ‖coefficients (FamilyCuspTaylor.matrixOrbit data .plane parameter function induced
      (weyl⁻¹ * localRadical coordinates * argument)) (fun index => (real index).val) order‖ ≤ _
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

/-- **Joint smoothness of the local Hilbert standard integral** of a family of plane sections in
the vertices and the real right translation, for an argument with integral finite part and
`Re s > -n/2 - 1`, with no majorant hypothesis. -/
theorem localFamilyValue_joint_smooth_of_integral {degree arity : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (lift : HasSmoothCuspLift data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (argument : AdelicGL)
    (integral : argument ∈ integralArguments) :
    Smooth (AdelicFamilyTaylor.orbit (localFamilyValue data parameter function induced)
      argument) :=
  localFamilyValue_joint_smooth data parameter function induced lift argument
    (fun real => (exists_localFamilyTaylorMajorant data parameter function induced lift
      halfPlane real argument integral).some)

end TernaryPeriodPolynomials.EdgeConvergence
