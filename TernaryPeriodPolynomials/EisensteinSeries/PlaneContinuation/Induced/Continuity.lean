module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.LocalBounds
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.Level

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedContinuity

local instance residueTopology : TopologicalSpace (ZMod 3) := ⊥
local instance residueDiscrete : DiscreteTopology (ZMod 3) := ⟨rfl⟩

instance groupMeasurable : MeasurableSpace AdelicGL := borel AdelicGL
instance groupBorel : BorelSpace AdelicGL := ⟨rfl⟩

theorem level_isOpen : IsOpen (finiteLevel : Set FiniteGL) :=
  integralMap_isOpenMap _ ((isOpen_discrete (rowStabilizer : Set (GeneralLinearGroup (Fin 3) (ZMod 3)))).preimage
    reductionMap_continuous)

theorem realGroup_continuous : Continuous realGroup := by
  apply Units.continuous_map
  exact continuous_pi (fun row => continuous_pi (fun column =>
    continuous_fst.comp ((continuous_apply column).comp (continuous_apply row))))

theorem finiteGroup_continuous : Continuous finiteGroup := by
  apply Units.continuous_map
  exact continuous_pi (fun row => continuous_pi (fun column =>
    continuous_snd.comp ((continuous_apply column).comp (continuous_apply row))))

theorem continuous {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) : Continuous function := by
  apply continuous_iff_continuousAt.mpr
  intro point
  have realContinuous : Continuous (fun realPoint : RealGL3 =>
      function (atFinite (finiteGroup point) * atInfinity realPoint)) :=
    (ScalarLocalBounds.smooth_continuous (induced.1 (atFinite (finiteGroup point)))).comp
      (continuous_pi (fun _ : Fin 1 => continuous_id))
  have comparisonContinuous : Continuous (fun other : AdelicGL =>
      function (atInfinity (realGroup other) * atFinite (finiteGroup point))) := by
    simpa only [Function.comp_def, atFinite_atInfinity_commute] using realContinuous.comp realGroup_continuous
  have tends : Filter.Tendsto (fun other : AdelicGL => (finiteGroup point)⁻¹ * finiteGroup other)
      (nhds point) (nhds 1) := by
    have result : ContinuousAt (fun other : AdelicGL => (finiteGroup point)⁻¹ * finiteGroup other) point :=
      (continuous_const.mul finiteGroup_continuous).continuousAt
    simpa only [ContinuousAt, inv_mul_cancel] using result
  have neighborhood := tends.eventually (level_isOpen.mem_nhds finiteLevel.one_mem)
  have equality : function =ᶠ[nhds point] (fun other : AdelicGL =>
      function (atInfinity (realGroup other) * atFinite (finiteGroup point))) := by
    filter_upwards [neighborhood] with other membership
    have invariance := induced.2.1 ⟨(finiteGroup point)⁻¹ * finiteGroup other, membership⟩
      (atInfinity (realGroup other) * atFinite (finiteGroup point))
    rw [mul_assoc, ← atFinite_mul, mul_inv_cancel_left, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adelicGL_eq_mul] at invariance
    exact invariance
  exact comparisonContinuous.continuousAt.congr_of_eventuallyEq equality

theorem measurable {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) : Measurable function :=
  (continuous induced).measurable

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedContinuity
