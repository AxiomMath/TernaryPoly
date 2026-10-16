module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.FinAvgLeviAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.ThreeMeasure

@[expose] public section


/-!
# The integral Levi preserves the finite radical measure

The row-vector action `f ↦ f A` of an integral invertible matrix on `FiniteAwayThree²` is a continuous
additive automorphism preserving the integral lattice, so it preserves the normalized Haar measure.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory TopologicalSpace

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem leviRowAction_mul (A B : GeneralLinearGroup (Fin 2) ℤ) (f : FiniteAwayThree × FiniteAwayThree) :
    leviRowAction B (leviRowAction A f) = leviRowAction (A * B) f := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp only [leviRowAction_fst, leviRowAction_snd, finiteLeviMatrix, map_mul, Units.val_mul,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem leviRowAction_one (f : FiniteAwayThree × FiniteAwayThree) : leviRowAction 1 f = f := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [leviRowAction_fst, leviRowAction_snd, finiteLeviMatrix]

theorem leviRowAction_add (A : GeneralLinearGroup (Fin 2) ℤ) (f g : FiniteAwayThree × FiniteAwayThree) :
    leviRowAction A (f + g) = leviRowAction A f + leviRowAction A g := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp only [leviRowAction_fst, leviRowAction_snd, Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add] <;> ring

theorem leviRowAction_continuous (A : GeneralLinearGroup (Fin 2) ℤ) : Continuous (leviRowAction A) := by
  unfold leviRowAction
  fun_prop

/-- The row-vector action as a continuous additive automorphism. -/
def leviRowEquiv (A : GeneralLinearGroup (Fin 2) ℤ) :
    (FiniteAwayThree × FiniteAwayThree) ≃ₜ+ (FiniteAwayThree × FiniteAwayThree) where
  toFun := leviRowAction A
  invFun := leviRowAction A⁻¹
  left_inv f := by rw [leviRowAction_mul, mul_inv_cancel, leviRowAction_one]
  right_inv f := by rw [leviRowAction_mul, inv_mul_cancel, leviRowAction_one]
  map_add' := leviRowAction_add A
  continuous_toFun := leviRowAction_continuous A
  continuous_invFun := leviRowAction_continuous A⁻¹

/-- The integral lattice of `FiniteAwayThree`. -/
abbrev awayIntegral : Set FiniteAwayThree := Subtype.val ⁻¹' Set.range integralEmbedding

theorem leviRowAction_integral (A : GeneralLinearGroup (Fin 2) ℤ) {f : FiniteAwayThree × FiniteAwayThree}
    (hf : f ∈ awayIntegral ×ˢ awayIntegral) : leviRowAction A f ∈ awayIntegral ×ˢ awayIntegral := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hf
  constructor
  · refine ⟨x * (A.val 0 0 : IntegralAdeles) + y * (A.val 1 0 : IntegralAdeles), ?_⟩
    rw [leviRowAction_fst, map_add, map_mul, map_mul, hx, hy]
    simp [finiteLeviMatrix, GeneralLinearGroup.map_apply]
  · refine ⟨x * (A.val 0 1 : IntegralAdeles) + y * (A.val 1 1 : IntegralAdeles), ?_⟩
    rw [leviRowAction_snd, map_add, map_mul, map_mul, hx, hy]
    simp [finiteLeviMatrix, GeneralLinearGroup.map_apply]

theorem leviRowAction_preimage_integral (A : GeneralLinearGroup (Fin 2) ℤ) :
    leviRowAction A ⁻¹' (awayIntegral ×ˢ awayIntegral) = awayIntegral ×ˢ awayIntegral := by
  ext f
  constructor
  · intro hf
    have back := leviRowAction_integral A⁻¹ hf
    rwa [leviRowAction_mul, mul_inv_cancel, leviRowAction_one] at back
  · exact leviRowAction_integral A

/-- The normalized product measure on the finite radical coordinates. -/
abbrev awayProductMeasure : Measure (FiniteAwayThree × FiniteAwayThree) :=
  finiteAwayThreeMeasure.prod finiteAwayThreeMeasure

/-- **The integral Levi preserves the finite radical measure.** -/
theorem leviRowAction_measurePreserving (A : GeneralLinearGroup (Fin 2) ℤ) :
    MeasurePreserving (leviRowAction A) awayProductMeasure awayProductMeasure := by
  let K₀ : PositiveCompacts (FiniteAwayThree × FiniteAwayThree) :=
    finiteAwayThreeUnitCompact ×ˢ finiteAwayThreeUnitCompact
  have hK : (K₀ : Set (FiniteAwayThree × FiniteAwayThree)) = awayIntegral ×ˢ awayIntegral := rfl
  have measurable : Measurable (leviRowAction A) := (leviRowAction_continuous A).measurable
  refine ⟨measurable, ?_⟩
  have haar : (awayProductMeasure.map (leviRowEquiv A)).IsAddHaarMeasure :=
    ContinuousAddEquiv.isAddHaarMeasure_map awayProductMeasure (leviRowEquiv A)
  have mapEquality : awayProductMeasure.map (leviRowAction A) =
      awayProductMeasure.map (leviRowEquiv A) := rfl
  have hval : (awayProductMeasure.map (leviRowEquiv A)) K₀ = awayProductMeasure K₀ := by
    rw [← mapEquality, Measure.map_apply measurable K₀.isCompact.measurableSet, hK,
      leviRowAction_preimage_integral]
  have h1 := Measure.addHaarMeasure_unique (awayProductMeasure.map (leviRowEquiv A)) K₀
  have h2 := Measure.addHaarMeasure_unique awayProductMeasure K₀
  rw [mapEquality, h1, hval]
  exact h2.symm

end TernaryPeriodPolynomials.AnalyticClasses
