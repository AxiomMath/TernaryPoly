module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.FourOne
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.Algebra

@[expose] public section



/-! Degree-one/four analog of `IsometryAdjoint.lean`: the adjunction between `star4to1`/
`star1to4` with respect to `onePairing`/`fourPairing`, needed for the ISOMETRY
`fourPairing (star1to4 β) (star1to4 γ) = (1/96) * onePairing β γ`. Mirrors
`star3to2_star2to3_adjoint_iso` one degree up: unconditional, no alternation hypothesis. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity
open TernaryPeriodPolynomials.Argument.CoercivityOne

/-- Moving a single trailing index `p` to the front, across the leading quadruple
`(j, k, l, m)`, does not change the sign of `eps5` (a `4`-adjacent-transposition move, which is
even). -/
theorem eps5_block41_iso (p j k l m : Fin 5) : eps5 p j k l m = eps5 j k l m p := by
  show epsFive ![p, j, k, l, m] = epsFive ![j, k, l, m, p]
  have h : (![p, j, k, l, m] : Fin 5 → Fin 5) = ![j, k, l, m, p] ∘
      (Equiv.swap (3 : Fin 5) 4 * Equiv.swap (2 : Fin 5) 3 * Equiv.swap (1 : Fin 5) 2 *
        Equiv.swap (0 : Fin 5) 1) := by
    funext w; fin_cases w <;> rfl
  rw [h, epsFive_comp_perm]
  simp only [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (3 : Fin 5) ≠ 4),
    Equiv.Perm.sign_swap (by decide : (2 : Fin 5) ≠ 3),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 5) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (0 : Fin 5) ≠ 1)]
  norm_num

/-- Rotating a 5-fold sum, moving the leading single binder after the trailing quadruple. Pure
Fubini reindexing (four adjacent transpositions via `Finset.sum_comm`), independent of the
summand. -/
private theorem sum5_rotate1_iso (F : Fin 5 → Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ) :
    (∑ p : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, F p j k l m) =
      ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ p : Fin 5, F p j k l m := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [Finset.sum_comm]

/-- `star4to1` is adjoint to `star1to4` with respect to `onePairing`/`fourPairing`, with no
scalar correction and no alternation hypothesis: both sides unfold to the same quintuple sum once
`eps5_block41_iso` identifies the two block orders of `eps5`. -/
theorem star4to1_star1to4_adjoint_iso (b : FourCoordinates) (c : OneCoordinates) :
    onePairing (star4to1 b) c = fourPairing b (star1to4 c) := by
  have hL : onePairing (star4to1 b) c =
      (1 / 24 : ℝ) * ∑ p : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5,
        eps5 p j k l m * tangentWeight p * tangentWeight j * tangentWeight k *
          tangentWeight l * tangentWeight m * factorialPairing (b j k l m) (c p) := by
    simp only [onePairing, star4to1, map_smul, map_sum, LinearMap.smul_apply,
      LinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    apply Finset.sum_congr rfl; intro m _
    ring
  have hR : fourPairing b (star1to4 c) =
      (1 / 24 : ℝ) * ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ p : Fin 5,
        eps5 j k l m p * tangentWeight j * tangentWeight k * tangentWeight l *
          tangentWeight m * tangentWeight p * factorialPairing (b j k l m) (c p) := by
    simp only [fourPairing, star1to4, map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    apply Finset.sum_congr rfl; intro m _
    apply Finset.sum_congr rfl; intro p _
    ring
  rw [hL, hR, sum5_rotate1_iso]
  have hEq : (∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ p : Fin 5,
      eps5 p j k l m * tangentWeight p * tangentWeight j * tangentWeight k *
        tangentWeight l * tangentWeight m * factorialPairing (b j k l m) (c p)) =
      ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ p : Fin 5,
        eps5 j k l m p * tangentWeight j * tangentWeight k * tangentWeight l *
          tangentWeight m * tangentWeight p * factorialPairing (b j k l m) (c p) := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    apply Finset.sum_congr rfl; intro m _
    apply Finset.sum_congr rfl; intro p _
    rw [eps5_block41_iso]
    ring
  rw [hEq]

end TernaryPeriodPolynomials.Argument.Coercivity
