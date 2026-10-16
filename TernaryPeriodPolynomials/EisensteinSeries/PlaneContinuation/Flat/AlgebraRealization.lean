module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.TupleAlgebra
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.ModeTuples

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedSectionAlgebra
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatAlgebraRealization

def Realizes {degree : ℕ} (data : InducingData degree)
    (operator : CompatibleTupleOperators.algebra data) : Prop :=
  ∀ original : flatSpace data, ∃ output : flatSpace data,
    ∀ (parameter : ℂ) (frame : Rectangular ℝ) (fullRank : FullRank frame) (index : ℤ),
      InducedModeTuples.tuple (output.property.1 parameter) frame fullRank index =
        operator.val index (InducedModeTuples.tuple (original.property.1 parameter) frame fullRank index)

theorem realizes_zero {degree : ℕ} (data : InducingData degree) : Realizes data 0 := by
  intro original
  refine ⟨0, ?_⟩
  intro parameter frame fullRank index
  exact InducedModeTuples.tuple_zero data parameter frame fullRank index

theorem realizes_one {degree : ℕ} (data : InducingData degree) : Realizes data 1 := by
  intro original
  exact ⟨original, fun _ _ _ _ => rfl⟩

theorem realizes_add {degree : ℕ} (data : InducingData degree)
    {first second : CompatibleTupleOperators.algebra data}
    (firstRealizes : Realizes data first) (secondRealizes : Realizes data second) :
    Realizes data (first + second) := by
  intro original
  obtain ⟨firstOutput, firstEquality⟩ := firstRealizes original
  obtain ⟨secondOutput, secondEquality⟩ := secondRealizes original
  refine ⟨firstOutput + secondOutput, ?_⟩
  intro parameter frame fullRank index
  exact (InducedModeTuples.tuple_add (firstOutput.property.1 parameter)
    (secondOutput.property.1 parameter) frame fullRank index).trans
      (congrArg₂ (fun first second : TupleModeRestriction.admissible data index => first + second)
        (firstEquality parameter frame fullRank index) (secondEquality parameter frame fullRank index))

theorem realizes_mul {degree : ℕ} (data : InducingData degree)
    {first second : CompatibleTupleOperators.algebra data}
    (firstRealizes : Realizes data first) (secondRealizes : Realizes data second) :
    Realizes data (first * second) := by
  intro original
  obtain ⟨intermediate, secondEquality⟩ := secondRealizes original
  obtain ⟨output, firstEquality⟩ := firstRealizes intermediate
  refine ⟨output, ?_⟩
  intro parameter frame fullRank index
  exact (firstEquality parameter frame fullRank index).trans
    (congrArg (first.val index) (secondEquality parameter frame fullRank index))

theorem realizes_scalar {degree : ℕ} (data : InducingData degree) (scalar : ℂ) :
    Realizes data (algebraMap ℂ (CompatibleTupleOperators.algebra data) scalar) := by
  intro original
  refine ⟨scalar • original, ?_⟩
  intro parameter frame fullRank index
  exact InducedModeTuples.tuple_smul (original.property.1 parameter) scalar frame fullRank index

def realizable {degree : ℕ} (data : InducingData degree) :
    Subalgebra ℂ (CompatibleTupleOperators.algebra data) where
  carrier := {operator | Realizes data operator}
  zero_mem' := realizes_zero data
  one_mem' := realizes_one data
  add_mem' := realizes_add data
  mul_mem' := realizes_mul data
  algebraMap_mem' := realizes_scalar data

theorem recovery_mem {degree : ℕ} (data : InducingData degree)
    (parameter : RecoveryTupleAlgebra.Parameter degree) :
    CompatibleTupleOperators.recovery data parameter.val parameter.property ∈ realizable data := by
  intro original
  refine ⟨⟨FixedRecoveryFlat.family original.property parameter.val,
    FixedRecoveryFlat.isFlat original.property parameter.val (by have := parameter.property; linarith)⟩, ?_⟩
  intro target frame fullRank index
  exact InducedModeTuples.fixed_recovery_tuple original.property parameter.val parameter.property
    target frame fullRank index

theorem algebra_le {degree : ℕ} (data : InducingData degree) :
    RecoveryTupleAlgebra.algebra data ≤ realizable data := by
  apply Algebra.adjoin_le
  rintro _ ⟨parameter, rfl⟩
  exact recovery_mem data parameter

theorem exists_flat {degree : ℕ} {data : InducingData degree} {original : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data original) (operator : RecoveryTupleAlgebra.algebra data) :
    ∃ output : ℂ → AdelicGL → ℂ, ∃ outputFlat : IsFlatSection data output,
      ∀ (parameter : ℂ) (frame : Rectangular ℝ) (fullRank : FullRank frame) (index : ℤ),
        InducedModeTuples.tuple (outputFlat.1 parameter) frame fullRank index =
          RecoveryTupleAlgebra.evaluation data index operator
            (InducedModeTuples.tuple (flat.1 parameter) frame fullRank index) := by
  obtain ⟨output, equality⟩ := (algebra_le data operator.property) ⟨original, flat⟩
  exact ⟨output.val, output.property, equality⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatAlgebraRealization
