module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.PolynomialBadLineNormalization.Helpers

theorem goodChain_zero : GoodChain (0 : EdgeChains) := by
  simp [GoodChain]

theorem goodChain_add {left right : EdgeChains}
    (left_good : GoodChain left) (right_good : GoodChain right) :
    GoodChain (left + right) := by
  classical
  intro edge edge_support
  by_cases left_support : edge ∈ left.support
  · exact left_good edge left_support
  · apply right_good edge
    rw [Finsupp.mem_support_iff] at edge_support ⊢
    rw [Finsupp.notMem_support_iff] at left_support
    simpa only [Finsupp.add_apply, left_support, zero_add] using edge_support

theorem goodChain_neg {chain : EdgeChains} (chain_good : GoodChain chain) :
    GoodChain (-chain) := by
  classical
  intro edge edge_support
  apply chain_good edge
  simpa only [Finsupp.mem_support_iff, Finsupp.neg_apply, neg_ne_zero] using edge_support

theorem goodChain_sub {left right : EdgeChains}
    (left_good : GoodChain left) (right_good : GoodChain right) :
    GoodChain (left - right) := by
  simpa only [sub_eq_add_neg] using goodChain_add left_good (goodChain_neg right_good)

theorem path_difference_goodCycle {first second : rationalLevel → EdgeChains}
    (first_paths : IsPathFamily first) (second_paths : IsPathFamily second)
    (element : rationalLevel) : GoodCycle (first element - second element) := by
  constructor
  · rw [map_sub, (first_paths element).2, (second_paths element).2, sub_self]
  · exact goodChain_sub (first_paths element).1 (second_paths element).1

noncomputable def extendOneCochain {ambient coefficients : Type}
    [Group ambient] [AddCommGroup coefficients] [Module ℂ coefficients]
    (subgroup : Subgroup ambient) (representation : Representation ℂ ambient coefficients)
    (values : subgroup → coefficients) : cochains subgroup representation 1 := by
  classical
  refine ⟨fun vertices => representation (vertices 0)
    (if membership : (vertices 0)⁻¹ * vertices 1 ∈ subgroup then
      values ⟨(vertices 0)⁻¹ * vertices 1, membership⟩ else 0), ?_⟩
  intro element vertices
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  rw [map_mul, Module.End.mul_apply]

theorem extendOneCochain_apply {ambient coefficients : Type}
    [Group ambient] [AddCommGroup coefficients] [Module ℂ coefficients]
    (subgroup : Subgroup ambient) (representation : Representation ℂ ambient coefficients)
    (values : subgroup → coefficients) (first second : subgroup) :
    (extendOneCochain subgroup representation values).val ![first.val, second.val] =
      representation first.val (values (first⁻¹ * second)) := by
  classical
  simp only [extendOneCochain, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, dite_eq_left
      (subgroup.mul_mem (subgroup.inv_mem first.property) second.property)]
  rfl

theorem classOf_boundaryMap {ambient coefficients : Type}
    [Group ambient] [AddCommGroup coefficients] [Module ℂ coefficients]
    (subgroup : Subgroup ambient) (representation : Representation ℂ ambient coefficients)
    (cochain : cochains subgroup representation 1) :
    classOf subgroup representation (boundaryMap subgroup representation cochain) = 0 := by
  change (LinearMap.range (boundaryMap subgroup representation)).mkQ
    (boundaryMap subgroup representation cochain) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨cochain, rfl⟩

theorem change_path_representative {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_properties : IsPolynomialFunctional polynomial functional)
    {first second : rationalLevel → EdgeChains}
    {original : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (first_paths : IsPathFamily first) (second_paths : IsPathFamily second)
    (original_realization : RealizesPathClass functional first original) :
    ∃ changed : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter),
      RealizesPathClass functional second changed ∧
      classOf rationalLevel (rationalCoefficientComponent degree trivialCharacter) changed =
        classOf rationalLevel (rationalCoefficientComponent degree trivialCharacter) original := by
  let representation := rationalCoefficientComponent degree trivialCharacter
  let values : rationalLevel → HomogeneousPoly degree :=
    fun element => functional (first element - second element)
  let correction := extendOneCochain rationalLevel representation values
  let changed := original - boundaryMap rationalLevel representation correction
  refine ⟨changed, ?_, ?_⟩
  · intro first_vertex second_vertex third_vertex
    have translation := functional_properties.1 (first_vertex⁻¹ * second_vertex)
      (first (second_vertex⁻¹ * third_vertex) - second (second_vertex⁻¹ * third_vertex))
      (path_difference_goodCycle first_paths second_paths (second_vertex⁻¹ * third_vertex))
    have multiplication :
        (first_vertex⁻¹ * second_vertex) * (second_vertex⁻¹ * third_vertex) =
          first_vertex⁻¹ * third_vertex := by simp
    have representation_composition :
        representation first_vertex.val
          (representation (first_vertex⁻¹ * second_vertex).val
            (values (second_vertex⁻¹ * third_vertex))) =
          representation second_vertex.val (values (second_vertex⁻¹ * third_vertex)) := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    change original.val.val _ - (differentialOne rationalLevel representation correction).val _ = _
    rw [original_realization]
    change representation first_vertex.val
        (functional (first (first_vertex⁻¹ * second_vertex) +
          translateChain (first_vertex⁻¹ * second_vertex).val
            (first (second_vertex⁻¹ * third_vertex)) - first (first_vertex⁻¹ * third_vertex))) -
      (correction.val ![second_vertex.val, third_vertex.val] -
        correction.val ![first_vertex.val, third_vertex.val] +
        correction.val ![first_vertex.val, second_vertex.val]) = _
    rw [extendOneCochain_apply, extendOneCochain_apply, extendOneCochain_apply]
    rw [← representation_composition]
    change _ = representation first_vertex.val
      (functional (second (first_vertex⁻¹ * second_vertex) +
        translateChain (first_vertex⁻¹ * second_vertex).val
          (second (second_vertex⁻¹ * third_vertex)) - second (first_vertex⁻¹ * third_vertex)))
    dsimp [values] at translation ⊢
    rw [← translation]
    simp only [map_add, map_sub] at *
    abel
  · change classOf rationalLevel representation
      (original - boundaryMap rationalLevel representation correction) = _
    rw [map_sub, classOf_boundaryMap, sub_zero]

end TernaryPeriodPolynomials.PolynomialBadLineNormalization.Helpers
