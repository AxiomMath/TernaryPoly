module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.ModeMatrix

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedSectionAlgebra
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfileTuples

abbrev Space {degree : ℕ} (data : InducingData degree) := UniversalFiniteProfiles.Key data → data.cusp.H

def vectors {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (frame : Rectangular ℝ) :
    UniversalFiniteProfiles.Key data → data.cusp.smooth :=
  fun key => profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding (UniversalFiniteProfiles.representative data key)) frame)

def tuple {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (frame : Rectangular ℝ) : Space data :=
  fun key => (vectors induced frame key).val

def linear {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (frame : Rectangular ℝ) :
    inducedSpace data parameter →ₗ[ℂ] Space data :=
  LinearMap.pi (fun key => data.cusp.smooth.subtype.comp
    (profileLinear data parameter (adelicFrame (GeneralLinearGroup.map integralEmbedding
      (UniversalFiniteProfiles.representative data key)) frame)))

theorem linear_apply {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (frame : Rectangular ℝ)
    (function : inducedSpace data parameter) : linear data parameter frame function = tuple function.property frame := rfl

theorem profile_fixed {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : IntegralFiniteGL)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    (profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) frame)).val ∈
      fixedSubspace data.cusp finiteCongruence := by
  rw [RealProfileRegularity.profile_eq_model induced _ frame fullRank]
  exact (fixedSubspace data.cusp finiteCongruence).smul_mem _
    (InducedAnalyticFamilies.matrixCuspVector_fixed induced finitePoint (inverseMatrix frame))

def fixed {degree : ℕ} (data : InducingData degree) : Submodule ℂ (Space data) where
  carrier := {value | ∀ key, value key ∈ fixedSubspace data.cusp finiteCongruence}
  zero_mem' := fun _ => (fixedSubspace data.cusp finiteCongruence).zero_mem
  add_mem' first second := fun key => (fixedSubspace data.cusp finiteCongruence).add_mem (first key) (second key)
  smul_mem' scalar _ membership := fun key => (fixedSubspace data.cusp finiteCongruence).smul_mem scalar (membership key)

theorem fixed_isClosed {degree : ℕ} (data : InducingData degree) : IsClosed (fixed data : Set (Space data)) := by
  change IsClosed {value : Space data | ∀ key, value key ∈ fixedSubspace data.cusp finiteCongruence}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun key => (fixedSubspace_isClosed data.cusp finiteCongruence).preimage (continuous_apply key))

theorem tuple_fixed {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    tuple induced frame ∈ fixed data := fun key => profile_fixed induced (UniversalFiniteProfiles.representative data key) frame fullRank

theorem profile_selected {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : IntegralFiniteGL)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    tuple induced frame (UniversalFiniteProfiles.selected data finitePoint) =
      (profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) frame)).val :=
  congrArg Subtype.val (UniversalFiniteProfiles.profile_eq_selected induced finitePoint frame fullRank)

theorem flat_parameter {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (frame : Rectangular ℝ) (fullRank : FullRank frame) (parameter : ℂ) :
    tuple (flat.1 parameter) frame =
      Complex.exp ((parameter - cohomologicalPoint) * (RealFlatProfile.height frame : ℂ)) •
        tuple (flat.1 cohomologicalPoint) frame := by
  funext key
  exact congrArg Subtype.val (RealFlatProfile.profile_parameter flat _
    ⟨UniversalFiniteProfiles.representative data key, rfl⟩ frame fullRank parameter)

def generators {degree : ℕ} (data : InducingData degree) : Set (Space data) :=
  {value | ∃ parameter : ℂ, ∃ function : AdelicGL → ℂ, ∃ induced : IsInduced data .plane parameter function,
    ∃ frame : Rectangular ℝ, FullRank frame ∧ tuple induced frame = value}

def admissible {degree : ℕ} (data : InducingData degree) : Submodule ℂ (Space data) :=
  (Submodule.span ℂ (generators data)).topologicalClosure

theorem tuple_admissible {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    tuple induced frame ∈ admissible data :=
  (Submodule.span ℂ (generators data)).le_topologicalClosure
    (Submodule.subset_span ⟨parameter, function, induced, frame, fullRank, rfl⟩)

theorem admissible_le_fixed {degree : ℕ} (data : InducingData degree) : admissible data ≤ fixed data := by
  apply (Submodule.span ℂ (generators data)).topologicalClosure_minimal _ (fixed_isClosed data)
  apply Submodule.span_le.mpr
  rintro _ ⟨parameter, function, induced, frame, fullRank, rfl⟩
  exact tuple_fixed induced frame fullRank

theorem admissible_isClosed {degree : ℕ} (data : InducingData degree) :
    IsClosed (admissible data : Set (Space data)) := (Submodule.span ℂ (generators data)).isClosed_topologicalClosure

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfileTuples
