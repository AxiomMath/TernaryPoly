module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AdmissibleRecoveryOperator

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleModeRestriction

theorem unit_of_injective {Vector : Type*} [AddCommGroup Vector] [Module ℂ Vector] [FiniteDimensional ℂ Vector]
    (linear : Module.End ℂ Vector) (injective : Function.Injective linear) : IsUnit linear :=
  (LinearMap.isUnit_iff_ker_eq_bot linear).mpr (LinearMap.ker_eq_bot.mpr injective)

abbrev Space {degree : ℕ} (data : InducingData degree) (index : ℤ) :=
  UniversalFiniteProfiles.Key data → fixedMode data.cusp finiteCongruence index

instance finiteDimensional {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    FiniteDimensional ℂ (Space data index) := by
  let _ := EndpointAdmissibility.all_finiteDimensional data index
  infer_instance

def inclusion {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    Space data index →ₗ[ℂ] ProfileTuples.Space data :=
  LinearMap.pi (fun key => data.cusp.smooth.subtype.comp
    ((fixedMode data.cusp finiteCongruence index).subtype.comp (LinearMap.proj key)))

theorem inclusion_apply {degree : ℕ} (data : InducingData degree) (index : ℤ)
    (value : Space data index) (key : UniversalFiniteProfiles.Key data) :
    inclusion data index value key = (value key).val.val := rfl

theorem inclusion_injective {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    Function.Injective (inclusion data index) := by
  intro first second equality
  funext key
  exact Subtype.ext (Subtype.ext (congrFun equality key))

def admissible {degree : ℕ} (data : InducingData degree) (index : ℤ) : Submodule ℂ (Space data index) :=
  (ProfileTuples.admissible data).comap (inclusion data index)

def projectedRow {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (point : IntegralFiniteGL) (index : ℤ) :
    Space data index →ₗ[ℂ] fixedMode data.cusp finiteCongruence index :=
  ∑ key : UniversalFiniteProfiles.Key data,
    (RecoveryProjectedEntries.modeOperator data parameter halfPlane point key index).comp (LinearMap.proj key)

def averagedRow {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (point : IntegralFiniteGL) (index : ℤ) :
    Space data index →ₗ[ℂ] fixedMode data.cusp finiteCongruence index :=
  (Fintype.card (FiniteSectionProjection.levelImage data) : ℂ)⁻¹ •
    ∑ residue : FiniteSectionProjection.levelImage data,
      FiniteProfileResidues.character data (FiniteSectionProjection.representative data residue) •
        projectedRow data parameter halfPlane (point * FiniteSectionProjection.representative data residue) index

def operator {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (index : ℤ) :
    Module.End ℂ (Space data index) :=
  LinearMap.pi (fun key => averagedRow data parameter halfPlane (UniversalFiniteProfiles.representative data key) index)

theorem projectedRow_val {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (point : IntegralFiniteGL) (index : ℤ)
    (value : Space data index) :
    (projectedRow data parameter halfPlane point index value).val.val =
      TupleRecoveryOperator.projectedRow data parameter (by linarith) point (inclusion data index value) := by
  simp only [projectedRow, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum, TupleRecoveryOperator.projectedRow, ContinuousLinearMap.comp_apply,
    TupleRecoveryOperator.row_apply, map_sum]
  rfl

theorem averagedRow_val {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (point : IntegralFiniteGL) (index : ℤ)
    (value : Space data index) :
    (averagedRow data parameter halfPlane point index value).val.val =
      TupleRecoveryOperator.averagedRow data parameter (by linarith) point (inclusion data index value) := by
  simp only [averagedRow, TupleRecoveryOperator.averagedRow, LinearMap.smul_apply, LinearMap.sum_apply,
    _root_.smul_apply, _root_.sum_apply, Submodule.coe_smul, Submodule.coe_sum, projectedRow_val]

theorem operator_val {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (index : ℤ) (value : Space data index) :
    inclusion data index (operator data parameter halfPlane index value) =
      TupleRecoveryOperator.operator data parameter (by linarith) (inclusion data index value) := by
  funext key
  exact averagedRow_val data parameter halfPlane (UniversalFiniteProfiles.representative data key) index value

theorem operator_preserves {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (index : ℤ) (value : Space data index)
    (membership : value ∈ admissible data index) :
    operator data parameter halfPlane index value ∈ admissible data index := by
  change inclusion data index (operator data parameter halfPlane index value) ∈ ProfileTuples.admissible data
  rw [operator_val]
  exact TupleParameterShift.operator_preserves data parameter (by linarith) _ membership

def restricted {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (index : ℤ) :
    Module.End ℂ (admissible data index) :=
  (operator data parameter halfPlane index).restrict (operator_preserves data parameter halfPlane index)

def embedding {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    admissible data index →ₗ[ℂ] AdmissibleRecoveryOperator.Space data :=
  (inclusion data index).restrict (fun _ membership => membership)

theorem embedding_injective {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    Function.Injective (embedding data index) := by
  intro first second equality
  exact Subtype.ext (inclusion_injective data index (congrArg Subtype.val equality))

theorem restricted_embedding {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (index : ℤ) (value : admissible data index) :
    embedding data index (restricted data parameter halfPlane index value) =
      AdmissibleRecoveryOperator.operator data parameter (by linarith) (embedding data index value) :=
  Subtype.ext (operator_val data parameter halfPlane index value.val)

theorem restricted_isUnit {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (index : ℤ)
    (invertible : IsUnit (AdmissibleRecoveryOperator.operator data parameter (by linarith))) :
    IsUnit (restricted data parameter halfPlane index) := by
  have injective : Function.Injective (restricted data parameter halfPlane index) := by
    intro first second equality
    apply embedding_injective data index
    apply (ContinuousLinearMap.isUnit_iff_bijective.mp invertible).1
    rw [← restricted_embedding data parameter halfPlane index first,
      ← restricted_embedding data parameter halfPlane index second, equality]
  exact unit_of_injective (Vector := admissible data index) (restricted data parameter halfPlane index) injective

theorem shifted_halfPlane {degree : ℕ} (reference : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < reference.re) (number : ℕ) :
    (1 - (degree : ℝ)) / 2 < (reference + number).re := by
  simp only [Complex.add_re, Complex.natCast_re]
  exact lt_add_of_lt_of_nonneg halfPlane (Nat.cast_nonneg number)

theorem eventually_isUnit {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < reference.re) :
    ∀ᶠ number : ℕ in atTop, ∀ index : ℤ,
      IsUnit (restricted data (reference + number) (shifted_halfPlane reference halfPlane number) index) := by
  filter_upwards [AdmissibleRecoveryOperator.eventually_isUnit data reference (by linarith)] with number invertible
  intro index
  exact restricted_isUnit data (reference + number) (shifted_halfPlane reference halfPlane number) index invertible

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleModeRestriction
