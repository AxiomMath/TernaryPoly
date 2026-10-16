module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CompatibleTupleOperators
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.RecoveryInverse

@[expose] public section


open GeneralEisenstein
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleModeRestriction
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryTupleAlgebra

abbrev Parameter (degree : ℕ) := {parameter : ℂ // (1 - (degree : ℝ)) / 2 < parameter.re}

def algebra {degree : ℕ} (data : InducingData degree) : Subalgebra ℂ (CompatibleTupleOperators.algebra data) :=
  Algebra.adjoin ℂ (Set.range (fun parameter : Parameter degree =>
    CompatibleTupleOperators.recovery data parameter.val parameter.property))

instance algebraRing {degree : ℕ} (data : InducingData degree) : Ring (algebra data) :=
  Subalgebra.toRing (algebra data)

instance algebraAlgebra {degree : ℕ} (data : InducingData degree) : Algebra ℂ (algebra data) :=
  Subalgebra.algebra (algebra data)

instance finiteDimensional {degree : ℕ} (data : InducingData degree) : FiniteDimensional ℂ (algebra data) := by
  exact FiniteDimensional.of_injective (V := algebra data) (V₂ := CompatibleTupleOperators.algebra data)
    (algebra data).toSubmodule.subtype Subtype.val_injective

def recovery {degree : ℕ} (data : InducingData degree) (parameter : Parameter degree) : algebra data :=
  ⟨CompatibleTupleOperators.recovery data parameter.val parameter.property, Algebra.subset_adjoin ⟨parameter, rfl⟩⟩

def evaluation {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    algebra data →ₐ[ℂ] Module.End ℂ (admissible data index) where
  toFun value := value.val.val index
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

theorem evaluation_recovery {degree : ℕ} (data : InducingData degree) (parameter : Parameter degree) (index : ℤ) :
    evaluation data index (recovery data parameter) = restricted data parameter.val parameter.property index := rfl

theorem ext {degree : ℕ} (data : InducingData degree) (first second : algebra data)
    (equalities : ∀ index, evaluation data index first = evaluation data index second) : first = second :=
  Subtype.ext (Subtype.ext (funext equalities))

theorem unit_of_mulLeft_injective {AlgebraType : Type*} [Ring AlgebraType] [Algebra ℂ AlgebraType] [FiniteDimensional ℂ AlgebraType]
    (value : AlgebraType) (injective : Function.Injective (fun other => value * other)) : IsUnit value := by
  have surjective : Function.Surjective (fun other => value * other) :=
    (LinearMap.injective_iff_surjective (f := LinearMap.mulLeft ℂ value)).mp injective
  exact IsUnit.isUnit_iff_mulLeft_bijective.mpr ⟨injective, surjective⟩

theorem isUnit_of_modes {degree : ℕ} (data : InducingData degree) (value : algebra data)
    (invertible : ∀ index, IsUnit (evaluation data index value)) : IsUnit value := by
  apply unit_of_mulLeft_injective (AlgebraType := algebra data) value
  intro first second equality
  apply ext data
  intro index
  apply (invertible index).mul_left_cancel
  exact congrArg (evaluation data index) equality

theorem exists_cutoff {degree : ℕ} (data : InducingData degree) :
    ∃ cutoff : ℝ, (1 - (degree : ℝ)) / 2 < cutoff ∧
      ∀ parameter : Parameter degree, cutoff ≤ parameter.val.re → IsUnit (recovery data parameter) := by
  obtain ⟨cutoff, bound, invertible⟩ := UniformRecoveryInverse.exists_mode_cutoff data
  refine ⟨cutoff, bound, ?_⟩
  intro parameter above
  apply isUnit_of_modes data
  intro index
  exact invertible parameter.val above index parameter.property

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryTupleAlgebra
