module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.EndpointDetection
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.RecoveryCommutation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleModeRestriction TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleLadder
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompatibleTupleOperators

abbrev Family {degree : ℕ} (data : InducingData degree) := ∀ index : ℤ, Module.End ℂ (admissible data index)

instance endRing {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    Ring (Module.End ℂ (admissible data index)) := Module.End.instRing (R := ℂ) (N₁ := admissible data index)

instance familyRing {degree : ℕ} (data : InducingData degree) : Ring (Family data) := Pi.ring

def algebra {degree : ℕ} (data : InducingData degree) : Subalgebra ℂ (Family data) where
  carrier := {family | (∀ index value, admissibleRaising data index (family index value) =
      family (index + 2) (admissibleRaising data index value)) ∧
    (∀ index value, admissibleLowering data index (family index value) =
      family (index - 2) (admissibleLowering data index value))}
  zero_mem' := ⟨by intros; simp, by intros; simp⟩
  one_mem' := ⟨by intros; rfl, by intros; rfl⟩
  add_mem' first second := ⟨by
    intro index value
    simp only [Pi.add_apply, LinearMap.add_apply, map_add, first.1, second.1], by
    intro index value
    simp only [Pi.add_apply, LinearMap.add_apply, map_add, first.2, second.2]⟩
  mul_mem' first second := ⟨by
    intro index value
    simp only [Pi.mul_apply, Module.End.mul_apply, first.1, second.1], by
    intro index value
    simp only [Pi.mul_apply, Module.End.mul_apply, first.2, second.2]⟩
  algebraMap_mem' scalar := ⟨by
    intro index value
    change admissibleRaising data index (scalar • value) = scalar • admissibleRaising data index value
    exact map_smul _ scalar value, by
    intro index value
    change admissibleLowering data index (scalar • value) = scalar • admissibleLowering data index value
    exact map_smul _ scalar value⟩

theorem casimir {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth) :
    LieCasimir.casimir data.cusp vector = (((degree + 3 : ℤ) : ℂ) * ((degree + 3 : ℤ) - 2)) • vector := by
  have scalar : ((degree + 3 : ℤ) : ℂ) * ((degree + 3 : ℤ) - 2) = (degree + 3 : ℂ) * (degree + 1) := by
    push_cast
    ring
  rw [scalar]
  exact CohomologicalCasimir.scalar data vector

theorem zero_of_endpoints {degree : ℕ} (data : InducingData degree) (family : algebra data)
    (positive : family.val (degree + 3) = 0) (negative : family.val (-(degree + 3)) = 0) : family = 0 := by
  apply Subtype.ext
  funext index
  exact TupleEndpointDetection.zero_of_endpoints data (degree + 3) (by omega) (casimir data)
    family.val family.property.1 family.property.2 positive negative index

def endpointLinear {degree : ℕ} (data : InducingData degree) :
    algebra data →ₗ[ℂ] Module.End ℂ (admissible data (degree + 3)) × Module.End ℂ (admissible data (-(degree + 3))) :=
  ((LinearMap.proj (degree + 3 : ℤ)).prod (LinearMap.proj (-(degree + 3 : ℤ)))).comp (algebra data).toSubmodule.subtype

theorem endpointLinear_injective {degree : ℕ} (data : InducingData degree) :
    Function.Injective (endpointLinear data) := by
  intro first second equality
  have zero : first - second = 0 := zero_of_endpoints data (first - second)
    (sub_eq_zero.mpr (congrArg Prod.fst equality)) (sub_eq_zero.mpr (congrArg Prod.snd equality))
  exact sub_eq_zero.mp zero

instance finiteDimensional {degree : ℕ} (data : InducingData degree) : FiniteDimensional ℂ (algebra data) :=
  FiniteDimensional.of_injective (endpointLinear data) (endpointLinear_injective data)

def recovery {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) : algebra data :=
  ⟨fun index => restricted data parameter halfPlane index,
    TupleRecoveryCommutation.restricted_raising data parameter halfPlane,
    TupleRecoveryCommutation.restricted_lowering data parameter halfPlane⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompatibleTupleOperators
