module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ProjectedCoefficientIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryQuotientAverage
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteQuotientIntegral

theorem integral_eq_average {GroupType Quotient : Type} [Group GroupType] [MeasurableSpace GroupType]
    [MeasurableMul GroupType] [Group Quotient] [Fintype Quotient]
    (measure : Measure GroupType) [IsProbabilityMeasure measure] [measure.IsMulLeftInvariant]
    (quotient : GroupType →* Quotient) (representative : Quotient → GroupType)
    (representativeImage : ∀ index, quotient (representative index) = index)
    (function : GroupType → ℂ) (integrable : Integrable function measure)
    (factors : ∀ first second, quotient first = quotient second → function first = function second) :
    (∫ element, function element ∂measure) =
      (Fintype.card Quotient : ℂ)⁻¹ * ∑ index, function (representative index) := by
  have sumEquality (element : GroupType) :
      (∑ index, function (representative index * element)) = ∑ index, function (representative index) := by
    apply Finset.sum_equiv (Equiv.mulRight (quotient element)) (fun _ => by simp)
    intro index _
    apply factors
    rw [map_mul, representativeImage, representativeImage]
    rfl
  have integrated := congrArg (fun f : GroupType → ℂ => ∫ element, f element ∂measure) (funext sumEquality)
  rw [integral_finsetSum Finset.univ (fun index _ => integrable.comp_mul_left (representative index))] at integrated
  simp only [integral_mul_left_eq_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, integral_const,
    Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at integrated
  have nonzero : (Fintype.card Quotient : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (inv_mul_cancel_left₀ nonzero _).symm.trans (congrArg (fun value : ℂ => (Fintype.card Quotient : ℂ)⁻¹ * value) integrated)

def levelEquiv : integralCongruence ≃* finiteCongruence :=
  integralCongruence.equivMapOfInjective (Matrix.GeneralLinearGroup.map integralEmbedding) (by
    intro first second equality
    apply Units.ext
    exact Matrix.map_injective integralEmbedding_injective (congrArg Units.val equality))

theorem levelEquiv_val (matrix : integralCongruence) :
    (levelEquiv matrix).val = Matrix.GeneralLinearGroup.map integralEmbedding matrix.val := rfl

variable {Quotient : Type} [Group Quotient] [Finite Quotient]

def integralMap (quotient : IntegralBinaryGL →* Quotient) : integralCongruence →* image quotient where
  toFun matrix := ⟨quotient matrix.val, ⟨matrix.val, matrix.property, rfl⟩⟩
  map_one' := Subtype.ext quotient.map_one
  map_mul' first second := Subtype.ext (quotient.map_mul first.val second.val)

def finiteMap (quotient : IntegralBinaryGL →* Quotient) : finiteCongruence →* image quotient :=
  (integralMap quotient).comp levelEquiv.symm.toMonoidHom

def finiteRepresentative (quotient : IntegralBinaryGL →* Quotient) (index : image quotient) : finiteCongruence :=
  levelEquiv ⟨representative quotient index, representative_level quotient index⟩

omit [Finite Quotient] in
theorem finiteRepresentative_image (quotient : IntegralBinaryGL →* Quotient) (index : image quotient) :
    finiteMap quotient (finiteRepresentative quotient index) = index := by
  change integralMap quotient (levelEquiv.symm (levelEquiv _)) = index
  rw [levelEquiv.symm_apply_apply]
  exact Subtype.ext (representative_image quotient index)

theorem level_integral (quotient : IntegralBinaryGL →* Quotient)
    (function : finiteCongruence → ℂ) (integrable : Integrable function FiniteCompactIntegral.measure)
    (factors : ∀ first second, finiteMap quotient first = finiteMap quotient second → function first = function second) :
    (∫ element, function element ∂FiniteCompactIntegral.measure) =
      (Fintype.card (image quotient) : ℂ)⁻¹ * ∑ index, function (finiteRepresentative quotient index) :=
  integral_eq_average FiniteCompactIntegral.measure (finiteMap quotient) (finiteRepresentative quotient)
    (finiteRepresentative_image quotient) function integrable factors

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteQuotientIntegral
