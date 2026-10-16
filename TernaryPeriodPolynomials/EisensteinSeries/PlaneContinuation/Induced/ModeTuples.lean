module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.FourierOperator
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.ModeRestriction
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FixedRecoveryFlat

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedSectionAlgebra
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedModeTuples

def tuple {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (frame : Rectangular ℝ) (fullRank : FullRank frame)
    (index : ℤ) : TupleModeRestriction.admissible data index :=
  ⟨fun key => ⟨RotationFourier.smoothMode data.cusp index (ProfileTuples.vectors induced frame key),
    smoothMode_mem_fixedMode data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact index
      ⟨ProfileTuples.vectors induced frame key,
        ProfileTuples.profile_fixed induced (UniversalFiniteProfiles.representative data key) frame fullRank⟩⟩,
    AdmissibleRealAction.mode_mem data index (ProfileTuples.tuple induced frame) (ProfileTuples.tuple_admissible induced frame fullRank)⟩

theorem tuple_val {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (frame : Rectangular ℝ) (fullRank : FullRank frame) (index : ℤ) :
    TupleModeRestriction.inclusion data index (tuple induced frame fullRank index).val =
      TupleFourierOperator.projection data index (ProfileTuples.tuple induced frame) := rfl

def linear {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (frame : Rectangular ℝ)
    (fullRank : FullRank frame) (index : ℤ) :
    inducedSpace data parameter →ₗ[ℂ] TupleModeRestriction.admissible data index where
  toFun function := tuple function.property frame fullRank index
  map_add' first second := by
    apply Subtype.ext
    apply TupleModeRestriction.inclusion_injective data index
    change TupleFourierOperator.projection data index (ProfileTuples.linear data parameter frame (first + second)) =
      TupleFourierOperator.projection data index (ProfileTuples.linear data parameter frame first) +
        TupleFourierOperator.projection data index (ProfileTuples.linear data parameter frame second)
    rw [map_add, map_add]
  map_smul' scalar function := by
    apply Subtype.ext
    apply TupleModeRestriction.inclusion_injective data index
    change TupleFourierOperator.projection data index (ProfileTuples.linear data parameter frame (scalar • function)) =
      scalar • TupleFourierOperator.projection data index (ProfileTuples.linear data parameter frame function)
    rw [map_smul, map_smul]

theorem linear_apply {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (frame : Rectangular ℝ)
    (fullRank : FullRank frame) (index : ℤ) (function : inducedSpace data parameter) :
    linear data parameter frame fullRank index function = tuple function.property frame fullRank index := rfl

theorem tuple_zero {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (frame : Rectangular ℝ)
    (fullRank : FullRank frame) (index : ℤ) : tuple (induced_zero data parameter) frame fullRank index = 0 :=
  map_zero (linear data parameter frame fullRank index)

theorem tuple_add {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {first second : AdelicGL → ℂ}
    (firstInduced : IsInduced data .plane parameter first) (secondInduced : IsInduced data .plane parameter second)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) (index : ℤ) :
    tuple (induced_add firstInduced secondInduced) frame fullRank index =
      tuple firstInduced frame fullRank index + tuple secondInduced frame fullRank index := by
  have equality := (linear data parameter frame fullRank index).map_add
    (⟨first, firstInduced⟩ : inducedSpace data parameter) ⟨second, secondInduced⟩
  exact equality

theorem tuple_smul {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (scalar : ℂ) (frame : Rectangular ℝ)
    (fullRank : FullRank frame) (index : ℤ) :
    tuple (induced_smul induced scalar) frame fullRank index = scalar • tuple induced frame fullRank index := by
  have equality := (linear data parameter frame fullRank index).map_smul scalar
    (⟨function, induced⟩ : inducedSpace data parameter)
  exact equality

theorem tuple_eq_of_modes {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {first second : AdelicGL → ℂ} (firstInduced : IsInduced data .plane parameter first)
    (secondInduced : IsInduced data .plane parameter second) (frame : Rectangular ℝ) (fullRank : FullRank frame)
    (equalities : ∀ index, tuple firstInduced frame fullRank index = tuple secondInduced frame fullRank index) :
    ProfileTuples.tuple firstInduced frame = ProfileTuples.tuple secondInduced frame := by
  funext key
  apply RotationFourier.eq_of_modes data.cusp
  intro index
  exact congrArg (fun value : TupleModeRestriction.admissible data index => (value.val key).val.val) (equalities index)

theorem recovered_tuple {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) (index : ℤ) :
    tuple (RecoveryGlobalCusp.section_induced induced (by linarith)) frame fullRank index =
      TupleModeRestriction.restricted data parameter halfPlane index (tuple induced frame fullRank index) := by
  apply Subtype.ext
  apply TupleModeRestriction.inclusion_injective data index
  rw [tuple_val, TupleInducedRecovery.tuple induced (by linarith) frame fullRank,
    TupleFourierOperator.projection_recovery]
  exact (congrArg (TupleRecoveryOperator.operator data parameter (by linarith))
    (tuple_val induced frame fullRank index).symm).trans
      (TupleModeRestriction.operator_val data parameter halfPlane index (tuple induced frame fullRank index).val).symm

theorem fixed_recovery_tuple {degree : ℕ} {data : InducingData degree} {original : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data original) (reference : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < reference.re)
    (parameter : ℂ) (frame : Rectangular ℝ) (fullRank : FullRank frame) (index : ℤ) :
    tuple ((FixedRecoveryFlat.isFlat flat reference (by linarith)).1 parameter) frame fullRank index =
      TupleModeRestriction.restricted data reference halfPlane index (tuple (flat.1 parameter) frame fullRank index) := by
  apply Subtype.ext
  apply TupleModeRestriction.inclusion_injective data index
  rw [tuple_val, FixedRecoveryFlat.tuple flat reference (by linarith) parameter frame fullRank,
    TupleFourierOperator.projection_recovery]
  exact (congrArg (TupleRecoveryOperator.operator data reference (by linarith))
    (tuple_val (flat.1 parameter) frame fullRank index).symm).trans
      (TupleModeRestriction.operator_val data reference halfPlane index (tuple (flat.1 parameter) frame fullRank index).val).symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedModeTuples
