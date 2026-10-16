module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.ModeRestriction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleModeRestriction
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleModeMatrix

def realization {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    Space data index →ₗ[ℂ] (UniversalFiniteProfiles.Key data × BinaryAdelicGL → ℂ) :=
  LinearMap.pi (fun point => ((LinearMap.proj point.2).comp (RecoveryModeMatrix.realization data index)).comp
    (LinearMap.proj point.1))

theorem realization_injective {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    Function.Injective (realization data index) := by
  intro first second equality
  funext key
  apply RecoveryModeMatrix.realization_injective data index
  funext point
  exact congrFun equality (key, point)

theorem averagedRow_exists_meromorphic {degree : ℕ} (data : InducingData degree) (index : ℤ)
    (value : Space data index) (point : IntegralFiniteGL) (evaluation : BinaryAdelicGL) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re),
        continuation parameter = data.cusp.realize (averagedRow data parameter halfPlane point index value).val evaluation := by
  choose continuations meromorphic equalities using
    fun (residue : FiniteSectionProjection.levelImage data) (key : UniversalFiniteProfiles.Key data) =>
      RecoveryProjectedEntries.exists_meromorphic data (point * FiniteSectionProjection.representative data residue)
        key index (value key) evaluation
  refine ⟨fun parameter => (Fintype.card (FiniteSectionProjection.levelImage data) : ℂ)⁻¹ *
    ∑ residue, FiniteProfileResidues.character data (FiniteSectionProjection.representative data residue) *
      ∑ key, continuations residue key parameter, ?_, ?_⟩
  · intro parameter
    apply analyticAt_const.meromorphicAt.mul
    apply MeromorphicAt.fun_sum
    intro residue _
    apply analyticAt_const.meromorphicAt.mul
    exact MeromorphicAt.fun_sum (fun key _ => meromorphic residue key parameter)
  · intro parameter halfPlane
    simp only [averagedRow, projectedRow, LinearMap.smul_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, Submodule.coe_smul, Submodule.coe_sum,
      map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, equalities _ _ parameter halfPlane]

def restrictedRealization {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    admissible data index →ₗ[ℂ] (UniversalFiniteProfiles.Key data × BinaryAdelicGL → ℂ) :=
  (realization data index).comp (admissible data index).subtype

theorem restrictedRealization_injective {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    Function.Injective (restrictedRealization data index) :=
  (realization_injective data index).comp Subtype.val_injective

theorem exists_functional_meromorphic {degree : ℕ} (data : InducingData degree) (index : ℤ)
    (value : admissible data index) (functional : admissible data index →ₗ[ℂ] ℂ) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re),
        continuation parameter = functional (restricted data parameter halfPlane index value) := by
  let domain : Set ℂ := {parameter | (1 - (degree : ℝ)) / 2 < parameter.re}
  let family : domain → admissible data index := fun parameter => restricted data parameter.val parameter.property index value
  have scalarContinuations (point : UniversalFiniteProfiles.Key data × BinaryAdelicGL) :
      ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
        ∀ parameter : domain, continuation parameter.val = restrictedRealization data index (family parameter) point := by
    obtain ⟨continuation, meromorphic, equality⟩ := averagedRow_exists_meromorphic data index value.val
      (UniversalFiniteProfiles.representative data point.1) point.2
    exact ⟨continuation, meromorphic, fun parameter => equality parameter.val parameter.property⟩
  obtain ⟨continuation, meromorphic, equality⟩ := MeromorphicFiniteEvaluation.exists_meromorphic
    (restrictedRealization data index) (restrictedRealization_injective data index) domain family scalarContinuations functional
  exact ⟨continuation, meromorphic, fun parameter halfPlane => equality ⟨parameter, halfPlane⟩⟩

theorem exists_matrix {degree : ℕ} (data : InducingData degree) (index : ℤ)
    {Indices : Type*} [Fintype Indices] [DecidableEq Indices]
    (basis : Module.Basis Indices ℂ (admissible data index)) :
    ∃ matrix : ℂ → Matrix Indices Indices ℂ,
      (∀ row column parameter, MeromorphicAt (fun parameter => matrix parameter row column) parameter) ∧
      ∀ parameter (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re),
        matrix parameter = LinearMap.toMatrix basis basis (restricted data parameter halfPlane index) := by
  choose entries meromorphic equalities using fun row column : Indices =>
    exists_functional_meromorphic data index (basis column) (basis.coord row)
  refine ⟨fun parameter row column => entries row column parameter, meromorphic, ?_⟩
  intro parameter halfPlane
  apply Matrix.ext
  intro row column
  rw [LinearMap.toMatrix_apply]
  exact equalities row column parameter halfPlane

theorem eventually_det_ne_zero {degree : ℕ} (data : InducingData degree) (index : ℤ)
    {Indices : Type*} [Fintype Indices] [DecidableEq Indices]
    (basis : Module.Basis Indices ℂ (admissible data index)) (matrix : ℂ → Matrix Indices Indices ℂ)
    (equality : ∀ parameter (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re),
      matrix parameter = LinearMap.toMatrix basis basis (restricted data parameter halfPlane index))
    (reference : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < reference.re) :
    ∀ᶠ number : ℕ in atTop, (matrix (reference + number)).det ≠ 0 := by
  filter_upwards [TupleModeRestriction.eventually_isUnit data reference halfPlane] with number invertible
  rw [equality _ (shifted_halfPlane reference halfPlane number)]
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  exact (LinearMap.isUnit_toMatrix_iff basis).mpr (invertible index)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleModeMatrix
