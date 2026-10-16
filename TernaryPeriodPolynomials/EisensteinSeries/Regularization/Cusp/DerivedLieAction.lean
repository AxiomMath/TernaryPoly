module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.InfinitesimalBrackets
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

attribute [local instance] LieRing.ofAssociativeRing

noncomputable def cuspDerivedAction (cusp : CuspidalRepresentation) :
    Matrix (Fin 2) (Fin 2) ℝ →ₗ⁅ℝ⁆ Module.End ℂ cusp.smooth where
  toFun direction := cuspSmoothInfinitesimalAction cusp (fun _ => direction)
  map_add' first second := by
    apply LinearMap.ext
    intro vector
    apply Subtype.ext
    change cuspInfinitesimalAction cusp (fun _ => first + second) vector =
      cuspInfinitesimalAction cusp (fun _ => first) vector +
        cuspInfinitesimalAction cusp (fun _ => second) vector
    simp only [cuspInfinitesimalAction_eq_matrix_fderiv, map_add]
  map_smul' scalar direction := by
    apply LinearMap.ext
    intro vector
    apply Subtype.ext
    change cuspInfinitesimalAction cusp (fun _ => scalar • direction) vector =
      scalar • cuspInfinitesimalAction cusp (fun _ => direction) vector
    simp only [cuspInfinitesimalAction_eq_matrix_fderiv, map_smul]
  map_lie' {first second} := by
    simp only [Ring.lie_def]
    exact (cuspSmoothInfinitesimalAction_commutator cusp first second).symm

theorem cuspDerivedAction_apply_val (cusp : CuspidalRepresentation)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) (vector : cusp.smooth) :
    (cuspDerivedAction cusp direction vector).val =
      fderiv ℝ (cuspMatrixOrbit cusp vector) 1 direction :=
  cuspInfinitesimalAction_eq_matrix_fderiv cusp (fun _ => direction) vector

theorem cuspDerivedAction_skew (cusp : CuspidalRepresentation)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) (first second : cusp.smooth) :
    inner ℂ (cuspDerivedAction cusp direction first).val second.val +
      inner ℂ first.val (cuspDerivedAction cusp direction second).val = 0 :=
  cuspInfinitesimalAction_skew cusp (fun _ => direction) first second

theorem cuspDerivedAction_finiteFixed (cusp : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (direction : Matrix (Fin 2) (Fin 2) ℝ)
    (vector : cuspFiniteFixedSubmodule cusp level) :
    cuspDerivedAction cusp direction vector.val ∈ cuspFiniteFixedSubmodule cusp level :=
  cuspOrbitDerivative_mem_finiteFixed cusp level 1 vector (fun _ => fun _ => direction)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
