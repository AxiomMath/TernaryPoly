module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.ProjectedEntries
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MeromorphicFiniteEvaluation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryProjectedEntries

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryModeMatrix

def realization {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    fixedMode data.cusp finiteCongruence index →ₗ[ℂ] (BinaryAdelicGL → ℂ) :=
  data.cusp.realize.comp (fixedMode data.cusp finiteCongruence index).subtype

theorem realization_injective {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    Function.Injective (realization data index) :=
  data.cusp.injective.comp Subtype.val_injective

theorem exists_functional_meromorphic {degree : ℕ} (data : InducingData degree) (point : IntegralFiniteGL)
    (key : UniversalFiniteProfiles.Key data) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index)
    (functional : fixedMode data.cusp finiteCongruence index →ₗ[ℂ] ℂ) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re),
        continuation parameter = functional (modeOperator data parameter halfPlane point key index vector) := by
  let _ := EndpointAdmissibility.all_finiteDimensional data index
  let domain : Set ℂ := {parameter | (1 - (degree : ℝ)) / 2 < parameter.re}
  let family : domain → fixedMode data.cusp finiteCongruence index :=
    fun parameter => modeOperator data parameter.val parameter.property point key index vector
  have scalarContinuations (evaluation : BinaryAdelicGL) :
      ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
        ∀ parameter : domain, continuation parameter.val = realization data index (family parameter) evaluation := by
    obtain ⟨continuation, meromorphic, equality⟩ := RecoveryProjectedEntries.exists_meromorphic data point key index vector evaluation
    exact ⟨continuation, meromorphic, fun parameter => equality parameter.val parameter.property⟩
  obtain ⟨continuation, meromorphic, equality⟩ := MeromorphicFiniteEvaluation.exists_meromorphic
    (realization data index) (realization_injective data index) domain family scalarContinuations functional
  exact ⟨continuation, meromorphic, fun parameter halfPlane => equality ⟨parameter, halfPlane⟩⟩

theorem exists_matrix {degree : ℕ} (data : InducingData degree) (point : IntegralFiniteGL)
    (key : UniversalFiniteProfiles.Key data) (index : ℤ) {Indices : Type*} [Fintype Indices] [DecidableEq Indices]
    (basis : Module.Basis Indices ℂ (fixedMode data.cusp finiteCongruence index)) :
    ∃ matrix : ℂ → Matrix Indices Indices ℂ,
      (∀ row column parameter, MeromorphicAt (fun parameter => matrix parameter row column) parameter) ∧
      ∀ parameter (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re),
        matrix parameter = LinearMap.toMatrix basis basis (modeOperator data parameter halfPlane point key index) := by
  choose entries meromorphic equalities using fun row column : Indices =>
    exists_functional_meromorphic data point key index (basis column) (basis.coord row)
  refine ⟨fun parameter row column => entries row column parameter, meromorphic, ?_⟩
  intro parameter halfPlane
  apply Matrix.ext
  intro row column
  rw [LinearMap.toMatrix_apply]
  exact equalities row column parameter halfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryModeMatrix
