module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.SemidirectPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

section FiniteCocycles

variable {GroupType Coefficient : Type} [Group GroupType]
  [AddCommGroup Coefficient] [Module ℂ Coefficient]

def finiteCocycleAverage [Fintype GroupType] (values : GroupType → Coefficient) :
    Coefficient :=
  (Fintype.card GroupType : ℂ)⁻¹ • ∑ element, values element

theorem finiteCocycleAverage_coboundary [Fintype GroupType]
    (representation : Representation ℂ GroupType Coefficient)
    (values : GroupType → Coefficient)
    (relation : ∀ first second,
      values (first * second) = values first + representation first (values second))
    (element : GroupType) :
    values element = finiteCocycleAverage values -
      representation element (finiteCocycleAverage values) := by
  classical
  have sum_relation :
      ∑ second, values second =
        (Fintype.card GroupType : ℂ) • values element +
          representation element (∑ second, values second) := by
    calc
      ∑ second, values second = ∑ second, values (element * second) :=
        (Equiv.sum_comp (Equiv.mulLeft element) values).symm
      _ = ∑ second, (values element + representation element (values second)) := by
        apply Finset.sum_congr rfl
        intro second _
        exact relation element second
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          ← map_sum, Nat.cast_smul_eq_nsmul]
  have card_ne : (Fintype.card GroupType : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have scaled := congrArg (fun value : Coefficient =>
    (Fintype.card GroupType : ℂ)⁻¹ • value) sum_relation
  rw [smul_add, smul_smul, inv_mul_cancel₀ card_ne, one_smul,
    ← map_smul] at scaled
  exact (eq_sub_iff_add_eq.mpr scaled.symm)

end FiniteCocycles

section FiniteTwoCocycles

variable {GroupType Coefficient : Type} [Group GroupType]
  [AddCommGroup Coefficient] [Module ℂ Coefficient]

theorem cocycle_primitive_on_finite_subgroup
    (ambient target : Subgroup GroupType) [Fintype target]
    (inclusion : target ≤ ambient)
    (representation : Representation ℂ GroupType Coefficient)
    (cocycle : cocycles ambient representation) :
    ∃ primitive : cochains target representation 1, ∀ vertices,
      (differentialOne target representation primitive).val vertices =
        cocycle.val.val vertices := by
  classical
  let values : target → Coefficient := fun first =>
    (Fintype.card target : ℂ)⁻¹ • ∑ second : target,
      barValue ambient representation cocycle first.val second.val
  have card_ne : (Fintype.card target : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have bar_relation (first second : target) :
      barValue ambient representation cocycle first.val second.val =
        values first + representation first.val (values second) -
          values (first * second) := by
    have point_relation (third : target) :=
      barValue_cocycle ambient representation cocycle
        ⟨first.val, inclusion first.property⟩ second.val third.val
    have summed := congrArg (fun value : target → Coefficient => ∑ third, value third)
      (funext point_relation)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, ← map_sum] at summed
    have translate_sum :
        ∑ third : target, barValue ambient representation cocycle
            first.val (second.val * third.val) =
          ∑ third : target, barValue ambient representation cocycle first.val third.val := by
      exact Equiv.sum_comp (Equiv.mulLeft second)
        (fun third : target => barValue ambient representation cocycle first.val third.val)
    rw [translate_sum] at summed
    have scaled := congrArg (fun value : Coefficient =>
      (Fintype.card target : ℂ)⁻¹ • value) summed
    simp only [smul_sub, smul_add, smul_zero, ← map_smul] at scaled
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ card_ne, one_smul] at scaled
    dsimp only [values]
    convert (sub_eq_zero.mp scaled).symm using 1
    abel
  obtain ⟨primitive, primitive_eq⟩ := cocycle_coboundary_of_path_values target
    representation (restrictCocycle ambient target inclusion representation cocycle)
    values (by
      intro first second third
      change cocycle.val.val ![first.val, second.val, third.val] = _
      rw [cocycle_eq_barValue ambient representation cocycle
        ⟨first.val, inclusion first.property⟩]
      have relation := bar_relation (first⁻¹ * second) (second⁻¹ * third)
      have product_eq : (first⁻¹ * second) * (second⁻¹ * third) = first⁻¹ * third := by
        group
      rw [product_eq] at relation
      exact congrArg (representation first.val) relation)
  refine ⟨primitive, ?_⟩
  intro vertices
  exact congrFun (congrArg Subtype.val primitive_eq) vertices

end FiniteTwoCocycles

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
