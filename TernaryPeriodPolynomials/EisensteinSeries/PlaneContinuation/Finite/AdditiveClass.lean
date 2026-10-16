module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.Poisson

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteAdditiveClass

noncomputable def rationalPart (value : FiniteAdeles) : ℚ :=
  (AdelicAdditiveReduction.exists_rational_add_integral value).choose

noncomputable def integralPart (value : FiniteAdeles) : IntegralAdeles :=
  (AdelicAdditiveReduction.exists_rational_add_integral value).choose_spec.choose

theorem decomposition (value : FiniteAdeles) :
    value = algebraMap ℚ FiniteAdeles (rationalPart value) + integralEmbedding (integralPart value) :=
  (AdelicAdditiveReduction.exists_rational_add_integral value).choose_spec.choose_spec

noncomputable def finiteClass (value : FiniteAdeles) : AddCircle (1 : ℝ) :=
  ((rationalPart value : ℝ) : AddCircle (1 : ℝ))

theorem class_of_decomposition (value : FiniteAdeles) (rational : ℚ) (integral : IntegralAdeles)
    (equality : value = algebraMap ℚ FiniteAdeles rational + integralEmbedding integral) :
    finiteClass value = ((rational : ℝ) : AddCircle (1 : ℝ)) := by
  have differenceIntegral : algebraMap ℚ FiniteAdeles (rationalPart value - rational) ∈ Set.range integralEmbedding := by
    refine ⟨integral - integralPart value, ?_⟩
    rw [map_sub, map_sub]
    linear_combination decomposition value - equality
  obtain ⟨integer, integerEquality⟩ :=
    (IntegralRationals.integral_iff_integer (rationalPart value - rational)).mp differenceIntegral
  apply sub_eq_zero.mp
  change ((rationalPart value : ℝ) : AddCircle (1 : ℝ)) - ((rational : ℝ) : AddCircle (1 : ℝ)) = 0
  rw [← AddCircle.coe_sub, ← Rat.cast_sub, integerEquality]
  simpa only [Rat.cast_intCast] using TorusPeriodization.integer_cast_zero integer

theorem class_rational (rational : ℚ) :
    finiteClass (algebraMap ℚ FiniteAdeles rational) = ((rational : ℝ) : AddCircle (1 : ℝ)) :=
  class_of_decomposition _ rational 0 (by rw [map_zero, add_zero])

theorem class_integral (integral : IntegralAdeles) : finiteClass (integralEmbedding integral) = 0 := by
  simpa only [Rat.cast_zero, AddCircle.coe_zero] using
    class_of_decomposition (integralEmbedding integral) 0 integral (by rw [map_zero, zero_add])

theorem class_zero : finiteClass 0 = 0 := by
  simpa only [map_zero] using class_integral 0

theorem class_add (first second : FiniteAdeles) : finiteClass (first + second) = finiteClass first + finiteClass second := by
  have equality : first + second = algebraMap ℚ FiniteAdeles (rationalPart first + rationalPart second) +
      integralEmbedding (integralPart first + integralPart second) := by
    rw [map_add, map_add]
    linear_combination decomposition first + decomposition second
  rw [class_of_decomposition _ _ _ equality, Rat.cast_add, AddCircle.coe_add]
  rfl

noncomputable def classHom : FiniteAdeles →+ AddCircle (1 : ℝ) where
  toFun := finiteClass
  map_zero' := class_zero
  map_add' := class_add

theorem class_kernel (value : FiniteAdeles) : classHom value = 0 ↔ value ∈ Set.range integralEmbedding := by
  constructor
  · intro vanishing
    obtain ⟨integer, equality⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp vanishing
    have realEquality : (integer : ℝ) = (rationalPart value : ℝ) := by simpa only [zsmul_eq_mul, mul_one] using equality
    have rationalEquality : rationalPart value = (integer : ℚ) := by exact_mod_cast realEquality.symm
    refine ⟨integer + integralPart value, ?_⟩
    have valueEquality := decomposition value
    rw [rationalEquality, map_intCast] at valueEquality
    rw [map_add, map_intCast]
    exact valueEquality.symm
  · rintro ⟨integral, rfl⟩
    exact class_integral integral

theorem class_locallyConstant : IsLocallyConstant classHom := by
  apply IsLocallyConstant.iff_isOpen_fiber_apply.mpr
  intro value
  have equality : classHom ⁻¹' {classHom value} = {other | other - value ∈ Set.range integralEmbedding} := by
    ext other
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, ← class_kernel, map_sub, sub_eq_zero]
  rw [equality]
  exact integralLattice_isOpen.preimage (continuous_id.sub continuous_const)

theorem class_continuous : Continuous classHom := class_locallyConstant.continuous

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteAdditiveClass
