module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Plane.FlagCharts
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneFlagCharts

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneFlagSeries

def indexEquivalence : Chart ≃ Unit ⊕ (ℚ ⊕ (ℚ × ℚ)) where
  toFun
    | .origin => .inl ()
    | .vertical shift => .inr (.inl shift)
    | .affine slope shift => .inr (.inr (slope, shift))
  invFun
    | .inl _ => .origin
    | .inr (.inl shift) => .vertical shift
    | .inr (.inr (slope, shift)) => .affine slope shift
  left_inv chart := by cases chart <;> rfl
  right_inv index := by rcases index with ⟨⟨⟩⟩ | (shift | ⟨slope, shift⟩) <;> rfl

variable {Target : Type*} [NormedAddCommGroup Target] [CompleteSpace Target]

theorem tsum_charts (function : Chart → Target) (summable : Summable function) :
    ∑' chart, function chart = function .origin +
      ((∑' shift : ℚ, function (.vertical shift)) + ∑' slope : ℚ, ∑' shift : ℚ, function (.affine slope shift)) := by
  have indexed : Summable (fun index => function (indexEquivalence.symm index)) :=
    summable.comp_injective indexEquivalence.symm.injective
  have outer : Summable (fun index : ℚ ⊕ (ℚ × ℚ) => function (indexEquivalence.symm (.inr index))) :=
    indexed.comp_injective Sum.inr_injective
  have affineSummable : Summable (fun pair : ℚ × ℚ => function (.affine pair.1 pair.2)) :=
    outer.comp_injective Sum.inr_injective
  calc
    _ = ∑' index, function (indexEquivalence.symm index) := (indexEquivalence.symm.tsum_eq function).symm
    _ = _ := by
      rw [(indexed.comp_injective Sum.inl_injective).tsum_sum outer]
      rw [(outer.comp_injective Sum.inl_injective).tsum_sum affineSummable]
      change (∑' _ : Unit, function .origin) +
        ((∑' shift : ℚ, function (.vertical shift)) + ∑' pair : ℚ × ℚ, function (.affine pair.1 pair.2)) = _
      rw [affineSummable.tsum_prod, tsum_fintype]
      simp

theorem tsum_flags (function : Flags .plane → Target) (summable : Summable function) :
    ∑' flag, function flag = function (PlaneFlagCharts.flag .origin) +
      ((∑' shift : ℚ, function (PlaneFlagCharts.flag (.vertical shift))) +
        ∑' slope : ℚ, ∑' shift : ℚ, function (PlaneFlagCharts.flag (.affine slope shift))) := by
  rw [← PlaneFlagCharts.equivalence.tsum_eq function]
  exact tsum_charts (function ∘ PlaneFlagCharts.flag) (summable.comp_injective flag_injective)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneFlagSeries
