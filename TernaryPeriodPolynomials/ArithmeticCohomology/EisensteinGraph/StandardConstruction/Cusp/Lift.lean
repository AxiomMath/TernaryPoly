module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.MaximalCompact

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspLift

theorem normalized_mem {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) (argument : AdelicGL) :
    (fun binary : BinaryAdelicGL =>
      normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree side parameter) *
        function (binaryLevi side binary * argument)) ∈ cuspFunctions data.cusp := by
  cases side <;> exact induced.2.2.2.2.2 argument

def vector {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) (argument : AdelicGL) : data.cusp.smooth :=
  (LinearEquiv.ofInjective data.cusp.realize data.cusp.injective).symm
    ⟨_, normalized_mem data side parameter function induced argument⟩

theorem realizes {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) (argument : AdelicGL)
    (binary : BinaryAdelicGL) :
    data.cusp.realize (vector data side parameter function induced argument) binary =
      normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree side parameter) *
        function (binaryLevi side binary * argument) :=
  congrFun (LinearEquiv.ofInjective_symm_apply data.cusp.realize
    ⟨_, normalized_mem data side parameter function induced argument⟩) binary

theorem finite_invariant {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) (argument : AdelicGL)
    (level : finiteLevel) :
    vector data side parameter function induced (argument * atFinite level.val) =
      vector data side parameter function induced argument := by
  apply data.cusp.injective
  funext binary
  simp only [realizes, ← mul_assoc, induced.2.1 level]

theorem real_smooth {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) (argument : AdelicGL) :
    Smooth (fun real : Fin 1 → RealGL3 =>
      (vector data side parameter function induced (argument * atInfinity (real 0))).val) := by
  obtain ⟨lift, smooth, equality⟩ := induced.2.2.1 argument
  have agrees : ∀ real : Fin 1 → RealGL3,
      vector data side parameter function induced (argument * atInfinity (real 0)) = lift real := by
    intro real
    apply data.cusp.injective
    funext binary
    exact (realizes data side parameter function induced _ binary).trans
      (equality real binary).symm
  simpa only [agrees] using smooth

theorem real_continuous {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) (argument : AdelicGL) :
    Continuous (fun real : RealGL3 =>
      (vector data side parameter function induced (argument * atInfinity real)).val) := by
  have tupleContinuous : Continuous (fun real : Fin 1 → RealGL3 =>
      (vector data side parameter function induced (argument * atInfinity (real 0))).val) :=
    SmoothContinuity.smooth_continuous _
    (real_smooth data side parameter function induced argument)
  have constantTuple : Continuous (fun real : RealGL3 => fun _ : Fin 1 => real) :=
    continuous_pi (fun _ => continuous_id)
  have composed := tupleContinuous.comp constantTuple
  change Continuous (fun real : RealGL3 =>
    (vector data side parameter function induced (argument * atInfinity real)).val) at composed
  exact composed

theorem continuous {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) :
    Continuous (fun argument => (vector data side parameter function induced argument).val) := by
  apply continuous_iff_continuousAt.mpr
  intro element
  have localContinuous : Continuous (fun argument : AdelicGL =>
      (vector data side parameter function induced
        (atFinite (finiteGroup element) * atInfinity (realGroup argument))).val) :=
    (real_continuous data side parameter function induced
      (atFinite (finiteGroup element))).comp InducedContinuity.realGroup_continuous
  have near : ∀ᶠ argument : AdelicGL in 𝓝 element,
      (finiteGroup element)⁻¹ * finiteGroup argument ∈ finiteLevel := by
    exact (FiniteLevelTopology.finiteLevel_isOpen.preimage
      (continuous_const.mul InducedContinuity.finiteGroup_continuous)).mem_nhds (by simp)
  apply localContinuous.continuousAt.congr_of_eventuallyEq
  filter_upwards [near] with argument membership
  calc
    (vector data side parameter function induced argument).val =
        (vector data side parameter function induced
          (atFinite (finiteGroup element) * atInfinity (realGroup argument) *
            atFinite ((finiteGroup element)⁻¹ * finiteGroup argument))).val :=
      congrArg (fun value => (vector data side parameter function induced value).val)
        (InducedContinuity.split_right argument (finiteGroup element))
    _ = _ := congrArg Subtype.val
      (finite_invariant data side parameter function induced _ ⟨_, membership⟩)

theorem bounded {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) :
    ∃ bound : ℝ, ∀ element, inMaximalCompact element →
      ‖(vector data side parameter function induced element).val‖ ≤ bound :=
  MaximalCompact.isCompact.exists_bound_of_continuousOn
    (continuous data side parameter function induced).continuousOn

theorem flat_vector {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (element : AdelicGL) (membership : inMaximalCompact element) :
    vector data .plane parameter (extension parameter) (flat.1 parameter) element =
      vector data .plane cohomologicalPoint (extension cohomologicalPoint)
        (flat.1 cohomologicalPoint) element := by
  apply data.cusp.injective
  funext binary
  exact (realizes data .plane parameter _ (flat.1 parameter) element binary).trans
    ((flat.2.2 parameter binary element membership).trans
      (realizes data .plane cohomologicalPoint _ (flat.1 cohomologicalPoint) element binary).symm)

theorem flat_bounded {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) :
    ∃ bound : ℝ, ∀ parameter element, inMaximalCompact element →
      ‖(vector data .plane parameter (extension parameter) (flat.1 parameter) element).val‖ ≤ bound := by
  obtain ⟨bound, boundProperty⟩ := bounded data .plane cohomologicalPoint
    (extension cohomologicalPoint) (flat.1 cohomologicalPoint)
  refine ⟨bound, ?_⟩
  intro parameter element membership
  rw [flat_vector data extension flat parameter element membership]
  exact boundProperty element membership

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspLift
