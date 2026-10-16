module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Flat.AlgebraRealization
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.TupleDetermination
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ContinuationAlgebra

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedSectionAlgebra
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveredAlgebraCombination

def function {degree : ℕ} {data : InducingData degree} {Indices : Type*} [Fintype Indices]
    {families : Indices → ℂ → AdelicGL → ℂ} (flat : ∀ index, IsFlatSection data (families index))
    (coefficients : ℂ → Indices → ℂ) : ℂ → AdelicGL → ℂ :=
  fun parameter point => ∑ index, coefficients parameter index *
    FiniteSectionProjection.sectionFunction ((flat index).1 parameter) point

theorem exists_continuation {degree : ℕ} {data : InducingData degree} {Indices : Type*} [Fintype Indices]
    {families : Indices → ℂ → AdelicGL → ℂ} (flat : ∀ index, IsFlatSection data (families index))
    (coefficients : ℂ → Indices → ℂ)
    (meromorphic : ∀ index parameter, MeromorphicAt (fun parameter => coefficients parameter index) parameter) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation (function flat coefficients) continuation := by
  choose continuations continues using fun index => FiniteSectionProjection.exists_continuation (flat index)
  exact ⟨fun parameter point => ∑ index, coefficients parameter index * continuations index parameter point,
    ContinuationAlgebra.finset_sum Finset.univ
      (fun index parameter point => coefficients parameter index *
        FiniteSectionProjection.sectionFunction ((flat index).1 parameter) point)
      (fun index parameter point => coefficients parameter index * continuations index parameter point)
      (fun index _ => ContinuationAlgebra.multiply (continues index)
        (fun parameter => coefficients parameter index) (meromorphic index))⟩

def inducedCombination {degree : ℕ} {data : InducingData degree} {Indices : Type*} [Fintype Indices]
    {families : Indices → ℂ → AdelicGL → ℂ} (flat : ∀ index, IsFlatSection data (families index))
    (coefficients : ℂ → Indices → ℂ) (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) :
    inducedSpace data parameter :=
  ∑ index, coefficients parameter index •
    ⟨FiniteSectionProjection.sectionFunction ((flat index).1 parameter),
      RecoveryGlobalCusp.section_induced ((flat index).1 parameter) halfPlane⟩

theorem section_val {degree : ℕ} {data : InducingData degree} {Indices : Type*} [Fintype Indices]
    {families : Indices → ℂ → AdelicGL → ℂ} (flat : ∀ index, IsFlatSection data (families index))
    (coefficients : ℂ → Indices → ℂ) (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) :
    (inducedCombination flat coefficients parameter halfPlane).val = function flat coefficients parameter := by
  funext point
  simp only [inducedCombination, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, function]

theorem combination_mode {degree : ℕ} {data : InducingData degree} {Indices : Type*} [Fintype Indices]
    {families : Indices → ℂ → AdelicGL → ℂ} (flat : ∀ index, IsFlatSection data (families index))
    (coefficients : ℂ → Indices → ℂ) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) (index : ℤ) :
    InducedModeTuples.tuple (inducedCombination flat coefficients parameter (by linarith)).property frame fullRank index =
      ∑ basisIndex, coefficients parameter basisIndex • TupleModeRestriction.restricted data parameter halfPlane index
        (InducedModeTuples.tuple ((flat basisIndex).1 parameter) frame fullRank index) := by
  change InducedModeTuples.linear data parameter frame fullRank index
    (inducedCombination flat coefficients parameter (by linarith)) = _
  simp only [inducedCombination, map_sum, map_smul, InducedModeTuples.linear_apply,
    InducedModeTuples.recovered_tuple _ halfPlane]

theorem action_sum_identity {AlgebraType Vector Indices : Type*} [Ring AlgebraType] [Algebra ℂ AlgebraType]
    [AddCommGroup Vector] [Module ℂ Vector] [Fintype Indices]
    (evaluation : AlgebraType →ₐ[ℂ] Module.End ℂ Vector) (recovery : AlgebraType)
    (operators : Indices → AlgebraType) (coefficients : Indices → ℂ)
    (inverse : recovery * (∑ index, coefficients index • operators index) = 1) (vector : Vector) :
    (∑ index, coefficients index • evaluation recovery (evaluation (operators index) vector)) = vector := by
  calc
    _ = evaluation (recovery * (∑ index, coefficients index • operators index)) vector := by
      simp only [map_mul, map_sum, map_smul, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = vector := by rw [inverse, map_one]; rfl

theorem eq_original {degree : ℕ} {data : InducingData degree} {Indices : Type*} [Fintype Indices]
    {original : ℂ → AdelicGL → ℂ} (originalFlat : IsFlatSection data original)
    {families : Indices → ℂ → AdelicGL → ℂ} (flat : ∀ index, IsFlatSection data (families index))
    (operators : Indices → RecoveryTupleAlgebra.algebra data) (coefficients : ℂ → Indices → ℂ)
    (realizations : ∀ basisIndex parameter frame fullRank index,
      InducedModeTuples.tuple ((flat basisIndex).1 parameter) frame fullRank index =
        RecoveryTupleAlgebra.evaluation data index (operators basisIndex)
          (InducedModeTuples.tuple (originalFlat.1 parameter) frame fullRank index))
    (parameter : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re)
    (inverse : RecoveryTupleAlgebra.recovery data ⟨parameter, halfPlane⟩ *
      (∑ index, coefficients parameter index • operators index) = 1) :
    function flat coefficients parameter = original parameter := by
  rw [← section_val flat coefficients parameter (by linarith)]
  apply InducedTupleDetermination.ext (inducedCombination flat coefficients parameter (by linarith)).property
    (originalFlat.1 parameter)
  intro frame fullRank
  apply InducedModeTuples.tuple_eq_of_modes
  intro index
  rw [combination_mode flat coefficients parameter halfPlane frame fullRank index]
  simp only [realizations]
  have key := action_sum_identity (AlgebraType := RecoveryTupleAlgebra.algebra data)
    (Vector := TupleModeRestriction.admissible data index) (RecoveryTupleAlgebra.evaluation data index)
    (RecoveryTupleAlgebra.recovery data ⟨parameter, halfPlane⟩) operators (coefficients parameter) inverse
    (InducedModeTuples.tuple (originalFlat.1 parameter) frame fullRank index)
  have hR : TupleModeRestriction.restricted data parameter halfPlane index =
      RecoveryTupleAlgebra.evaluation data index
        (RecoveryTupleAlgebra.recovery data ⟨parameter, halfPlane⟩) :=
    (RecoveryTupleAlgebra.evaluation_recovery data ⟨parameter, halfPlane⟩ index).symm
  exact (Finset.sum_congr rfl fun x _ => congrArg (fun T : Module.End ℂ
    (TupleModeRestriction.admissible data index) => coefficients parameter x •
      T ((RecoveryTupleAlgebra.evaluation data index (operators x))
        (InducedModeTuples.tuple (originalFlat.1 parameter) frame fullRank index))) hR).trans key

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveredAlgebraCombination
