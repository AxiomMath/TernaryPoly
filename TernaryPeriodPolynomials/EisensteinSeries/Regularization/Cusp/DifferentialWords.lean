module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.DifferentiatedVectors

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def cuspDifferentialWord (cusp : CuspidalRepresentation)
    (directions : List (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) : Module.End ℂ cusp.smooth :=
  directions.foldr (fun direction operator =>
    cuspSmoothInfinitesimalAction cusp direction * operator) 1

theorem cuspDifferentialWord_nil (cusp : CuspidalRepresentation) :
    cuspDifferentialWord cusp [] = 1 := rfl

theorem cuspDifferentialWord_cons (cusp : CuspidalRepresentation)
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)
    (directions : List (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) :
    cuspDifferentialWord cusp (direction :: directions) =
      cuspSmoothInfinitesimalAction cusp direction * cuspDifferentialWord cusp directions := rfl

theorem cuspDifferentialWord_append (cusp : CuspidalRepresentation)
    (first second : List (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) :
    cuspDifferentialWord cusp (first ++ second) =
      cuspDifferentialWord cusp first * cuspDifferentialWord cusp second := by
  induction first with
  | nil => simp [cuspDifferentialWord_nil]
  | cons direction directions induction =>
    simp only [List.cons_append, cuspDifferentialWord_cons, induction, mul_assoc]

theorem cuspDifferentialWord_inner (cusp : CuspidalRepresentation)
    (directions : List (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) (first second : cusp.smooth) :
    inner ℂ (cuspDifferentialWord cusp directions first).val second.val =
      (-1 : ℂ) ^ directions.length *
        inner ℂ first.val (cuspDifferentialWord cusp directions.reverse second).val := by
  induction directions generalizing first second with
  | nil => simp [cuspDifferentialWord_nil]
  | cons direction directions induction =>
    have skew := cuspInfinitesimalAction_skew cusp direction
      (cuspDifferentialWord cusp directions first) second
    have equality := eq_neg_of_add_eq_zero_left skew
    change inner ℂ (cuspDifferentialWord cusp (direction :: directions) first).val second.val =
      -inner ℂ (cuspDifferentialWord cusp directions first).val
        (cuspSmoothInfinitesimalAction cusp direction second).val at equality
    rw [equality, induction]
    simp only [List.length_cons, List.reverse_cons, cuspDifferentialWord_append,
      cuspDifferentialWord_cons, cuspDifferentialWord_nil, mul_one, Module.End.mul_apply, pow_succ]
    ring

theorem cuspDifferentialWord_limit_zero
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (directions : List (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ))
    {I : Type*} {filter : Filter I} [filter.NeBot] (vectors : I → cusp.smooth) {limit : cusp.H}
    (vectors_limit : Tendsto (fun index => (vectors index).val) filter (nhds 0))
    (derivatives_limit : Tendsto
      (fun index => (cuspDifferentialWord cusp directions (vectors index)).val)
      filter (nhds limit)) : limit = 0 := by
  apply cohomological_inner_ext cohomological
  intro test
  have first_limit := derivatives_limit.inner (𝕜 := ℂ) (tendsto_const_nhds (x := test.val))
  have second_limit := (tendsto_const_nhds (x := (-1 : ℂ) ^ directions.length)).mul
    (vectors_limit.inner (𝕜 := ℂ)
      (tendsto_const_nhds (x := (cuspDifferentialWord cusp directions.reverse test).val)))
  have pairings : (fun index =>
      inner ℂ (cuspDifferentialWord cusp directions (vectors index)).val test.val) =
      fun index => (-1 : ℂ) ^ directions.length *
        inner ℂ (vectors index).val (cuspDifferentialWord cusp directions.reverse test).val :=
    funext (fun index => cuspDifferentialWord_inner cusp directions (vectors index) test)
  rw [pairings] at first_limit
  have equal_limits := tendsto_nhds_unique first_limit second_limit
  simpa only [inner_zero_left, mul_zero] using equal_limits

theorem cuspDifferentialWord_limit_eq
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (directions : List (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ))
    {I : Type*} {filter : Filter I} [filter.NeBot] (vectors : I → cusp.smooth)
    (vector : cusp.smooth) {limit : cusp.H}
    (vectors_limit : Tendsto (fun index => (vectors index).val) filter (nhds vector.val))
    (derivatives_limit : Tendsto
      (fun index => (cuspDifferentialWord cusp directions (vectors index)).val)
      filter (nhds limit)) : limit = (cuspDifferentialWord cusp directions vector).val := by
  apply sub_eq_zero.mp
  apply cuspDifferentialWord_limit_zero cohomological directions
    (filter := filter) (fun index => vectors index - vector)
  · simpa using vectors_limit.sub (tendsto_const_nhds (x := vector.val))
  · simpa only [map_sub, Submodule.coe_sub] using derivatives_limit.sub
      (tendsto_const_nhds (x := (cuspDifferentialWord cusp directions vector).val))

theorem cuspDifferentialWord_mem_finiteFixed (cusp : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (directions : List (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ))
    (vector : cuspFiniteFixedSubmodule cusp level) :
    cuspDifferentialWord cusp directions vector.val ∈ cuspFiniteFixedSubmodule cusp level := by
  induction directions with
  | nil => exact vector.property
  | cons direction directions induction =>
    exact cuspOrbitDerivative_mem_finiteFixed cusp level 1
      ⟨cuspDifferentialWord cusp directions vector.val, induction⟩ (fun _ => direction)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
