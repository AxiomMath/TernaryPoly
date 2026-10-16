module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.TupleAlgebra
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.AlgebraInverse

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryTupleAlgebra
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MeromorphicRecoveryAlgebra

abbrev Point {degree : ℕ} (data : InducingData degree) :=
  Σ index : ℤ, TupleModeRestriction.admissible data index × (UniversalFiniteProfiles.Key data × BinaryAdelicGL)

def sample {degree : ℕ} (data : InducingData degree) (point : Point data) : algebra data →ₗ[ℂ] ℂ :=
  (LinearMap.proj point.2.2).comp ((TupleModeMatrix.restrictedRealization data point.1).comp
    ((LinearMap.applyₗ (R := ℂ) (M₂ := TupleModeRestriction.admissible data point.1) point.2.1).comp
      (evaluation data point.1).toLinearMap))

def realization {degree : ℕ} (data : InducingData degree) : algebra data →ₗ[ℂ] (Point data → ℂ) :=
  LinearMap.pi (sample data)

theorem realization_injective {degree : ℕ} (data : InducingData degree) :
    Function.Injective (realization data) := by
  intro first second equality
  apply RecoveryTupleAlgebra.ext data
  intro index
  apply LinearMap.ext
  intro value
  apply TupleModeMatrix.restrictedRealization_injective data index
  funext point
  exact congrFun equality ⟨index, value, point⟩

theorem exists_sample_meromorphic {degree : ℕ} (data : InducingData degree) (point : Point data) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter : Parameter degree, continuation parameter.val = realization data (recovery data parameter) point := by
  rcases point with ⟨index, value, key, binary⟩
  have averaged := TupleModeMatrix.averagedRow_exists_meromorphic data index value.val
    (UniversalFiniteProfiles.representative data key) binary
  obtain ⟨continuation, meromorphic, equality⟩ := averaged
  exact ⟨continuation, meromorphic, fun parameter => equality parameter.val parameter.property⟩

theorem exists_functional_meromorphic {degree : ℕ} (data : InducingData degree)
    (functional : algebra data →ₗ[ℂ] ℂ) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter : Parameter degree, continuation parameter.val = functional (recovery data parameter) := by
  exact MeromorphicFiniteEvaluation.exists_meromorphic (Vector := algebra data) (Point := Point data)
    (realization data) (realization_injective data)
    {parameter | (1 - (degree : ℝ)) / 2 < parameter.re} (recovery data)
    (exists_sample_meromorphic data) functional

theorem exists_multiplication_matrix {degree : ℕ} (data : InducingData degree)
    {Indices : Type*} [Fintype Indices] [DecidableEq Indices]
    (basis : Module.Basis Indices ℂ (algebra data)) :
    ∃ matrix : ℂ → Matrix Indices Indices ℂ,
      (∀ row column parameter, MeromorphicAt (fun parameter => matrix parameter row column) parameter) ∧
      ∀ parameter : Parameter degree, matrix parameter.val =
        LinearMap.toMatrix basis basis (LinearMap.mulLeft ℂ (recovery data parameter)) := by
  exact FiniteAlgebraInverse.multiplication_matrix (AlgebraType := algebra data) basis
    {parameter | (1 - (degree : ℝ)) / 2 < parameter.re} (recovery data)
    (exists_functional_meromorphic data)

theorem exists_inverse_coefficients {degree : ℕ} (data : InducingData degree)
    {Indices : Type*} [Fintype Indices] [DecidableEq Indices]
    (basis : Module.Basis Indices ℂ (algebra data)) :
    ∃ coefficients : ℂ → Indices → ℂ, ∃ cutoff : ℝ,
      (1 - (degree : ℝ)) / 2 < cutoff ∧
      (∀ index parameter, MeromorphicAt (fun parameter => coefficients parameter index) parameter) ∧
      ∀ parameter : Parameter degree, cutoff ≤ parameter.val.re →
        recovery data parameter * (∑ index, coefficients parameter.val index • basis index) = 1 ∧
          (∑ index, coefficients parameter.val index • basis index) * recovery data parameter = 1 := by
  exact FiniteAlgebraInverse.exists_inverse_coefficients (AlgebraType := algebra data) basis
    ((1 - (degree : ℝ)) / 2) (recovery data) (exists_functional_meromorphic data)
    (RecoveryTupleAlgebra.exists_cutoff data)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MeromorphicRecoveryAlgebra
