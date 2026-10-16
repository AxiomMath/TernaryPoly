module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.ProfileRegularity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.Level

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileResidues

local instance residueTopology : TopologicalSpace (ZMod 3) := ⊥
local instance residueDiscrete : DiscreteTopology (ZMod 3) := ⟨rfl⟩

def character {degree : ℕ} (data : InducingData degree) (finitePoint : IntegralFiniteGL) : ℂ :=
  data.chi.toMonoidHom (GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding finitePoint)))

theorem character_nonzero {degree : ℕ} (data : InducingData degree) (finitePoint : IntegralFiniteGL) :
    character data finitePoint ≠ 0 := FrameProfile.character_ne_zero _ _

theorem outer_integral {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (finitePoint : IntegralFiniteGL) :
    outerCharacter data parameter (GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding finitePoint))) =
      character data finitePoint := by
  change character data finitePoint * normPower _ _ = _
  rw [normPower, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_integral, NNReal.coe_one, Real.log_one,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

theorem normalized_character {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (finitePoint : IntegralFiniteGL) (realPoint : RealGL3) :
    character data finitePoint • normalized induced
      (atFinite (GeneralLinearGroup.map integralEmbedding finitePoint) * atInfinity realPoint) =
      (outerCharacter data parameter (GeneralLinearGroup.det (atInfinity realPoint)))⁻¹ •
        planeCuspVector induced (atFinite (GeneralLinearGroup.map integralEmbedding finitePoint) * atInfinity realPoint) := by
  rw [normalized, map_mul, map_mul, outer_integral, mul_inv, smul_smul,
    ← mul_assoc, mul_inv_cancel₀ (character_nonzero data finitePoint), one_mul]

theorem same_reduction {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (first second : IntegralFiniteGL)
    (sameReduction : GeneralLinearGroup.map integralReduction first = GeneralLinearGroup.map integralReduction second)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    character data first • profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding first) frame) =
      character data second • profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding second) frame) := by
  rw [RealFrameChart.profile_eq induced _ frame fullRank, RealFrameChart.profile_eq induced _ frame fullRank,
    normalized_character, normalized_character, atFinite_atInfinity_commute, atFinite_atInfinity_commute]
  rw [planeCuspVector_same_integralReduction induced (atInfinity (point frame)) first second sameReduction]

theorem profile_eq_of_reduction {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (first second : IntegralFiniteGL)
    (sameReduction : GeneralLinearGroup.map integralReduction first = GeneralLinearGroup.map integralReduction second)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding first) frame) =
      ((character data first)⁻¹ * character data second) •
        profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding second) frame) := by
  have result := congrArg (fun vector : data.cusp.smooth => (character data first)⁻¹ • vector)
    (same_reduction induced first second sameReduction frame fullRank)
  simpa only [smul_smul, inv_mul_cancel₀ (character_nonzero data first), one_smul] using result

abbrev Residue := Set.range (GeneralLinearGroup.map integralReduction (n := Fin 3))

theorem profile_eq_representative {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (finitePoint : IntegralFiniteGL) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    let residue : Residue := ⟨GeneralLinearGroup.map integralReduction finitePoint, finitePoint, rfl⟩
    profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) frame) =
      ((character data finitePoint)⁻¹ * character data (integralResidueRepresentative residue)) •
        profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding (integralResidueRepresentative residue)) frame) := by
  let residue : Residue := ⟨GeneralLinearGroup.map integralReduction finitePoint, finitePoint, rfl⟩
  exact profile_eq_of_reduction induced finitePoint _ (integralResidueRepresentative_reduction residue).symm frame fullRank

theorem twisted_locallyConstant {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    IsLocallyConstant (fun finitePoint : IntegralFiniteGL => character data finitePoint •
      profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) frame)) := by
  have reduction : IsLocallyConstant (GeneralLinearGroup.map integralReduction (n := Fin 3)) :=
    (IsLocallyConstant.iff_continuous _).mpr TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.reductionMap_continuous
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro finitePoint
  exact ((IsLocallyConstant.iff_eventually_eq _).mp reduction finitePoint).mono
    (fun other equality => same_reduction induced other finitePoint equality frame fullRank)

theorem twisted_finite_range {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    (Set.range (fun finitePoint : IntegralFiniteGL => character data finitePoint •
      profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) frame))).Finite := by
  let representativeValue : Residue → data.cusp.smooth := fun residue =>
    character data (integralResidueRepresentative residue) • profile induced
      (adelicFrame (GeneralLinearGroup.map integralEmbedding (integralResidueRepresentative residue)) frame)
  apply (Set.finite_range representativeValue).subset
  rintro _ ⟨finitePoint, rfl⟩
  let residue : Residue := ⟨GeneralLinearGroup.map integralReduction finitePoint, finitePoint, rfl⟩
  refine ⟨residue, ?_⟩
  exact same_reduction induced _ finitePoint (integralResidueRepresentative_reduction residue) frame fullRank

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileResidues
