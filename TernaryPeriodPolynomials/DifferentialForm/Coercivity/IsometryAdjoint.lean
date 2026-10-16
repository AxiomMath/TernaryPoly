module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeStar

@[expose] public section



/-! Self-contained adjunction between `star2to3`/`star3to2` with respect to `twoPairing`/
`threePairing`, needed for ISOMETRY. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

/-- Moving the trailing pair `(d, e)` to the front, across the leading triple `(a, b, c)`, does
not change the sign of `eps5` (a `3 * 2`-block transposition, which is even). -/
theorem eps5_block32_iso (a b c d e : Fin 5) : eps5 d e a b c = eps5 a b c d e := by
  show epsFive ![d, e, a, b, c] = epsFive ![a, b, c, d, e]
  have h : (![d, e, a, b, c] : Fin 5 → Fin 5) = ![a, b, c, d, e] ∘
      (Equiv.swap (0 : Fin 5) 3 * Equiv.swap (1 : Fin 5) 4 * Equiv.swap (2 : Fin 5) 3 *
        Equiv.swap (3 : Fin 5) 4) := by
    funext w; fin_cases w <;> rfl
  rw [h, epsFive_comp_perm]
  simp only [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin 5) ≠ 3),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 5) ≠ 4),
    Equiv.Perm.sign_swap (by decide : (2 : Fin 5) ≠ 3),
    Equiv.Perm.sign_swap (by decide : (3 : Fin 5) ≠ 4)]
  norm_num

/-- Rotating a 5-fold sum, moving the leading pair of binders after the trailing triple. Pure
Fubini reindexing (six adjacent transpositions via `Finset.sum_comm`), independent of the
summand. -/
private theorem sum5_rotate_iso (F : Fin 5 → Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ) :
    (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, F i j k l m) =
      ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ i : Fin 5, ∑ j : Fin 5, F i j k l m := by
  have s1 : ∀ i : Fin 5, (∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, F i j k l m) =
      ∑ k : Fin 5, ∑ j : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, F i j k l m :=
    fun i => Finset.sum_comm
  have s2 : ∀ i k : Fin 5, (∑ j : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, F i j k l m) =
      ∑ l : Fin 5, ∑ j : Fin 5, ∑ m : Fin 5, F i j k l m :=
    fun i k => Finset.sum_comm
  have s3 : ∀ i k l : Fin 5, (∑ j : Fin 5, ∑ m : Fin 5, F i j k l m) =
      ∑ m : Fin 5, ∑ j : Fin 5, F i j k l m :=
    fun i k l => Finset.sum_comm
  have s4 : (∑ i : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ j : Fin 5, F i j k l m) =
      ∑ k : Fin 5, ∑ i : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ j : Fin 5, F i j k l m :=
    Finset.sum_comm
  have s5 : ∀ k : Fin 5, (∑ i : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ j : Fin 5, F i j k l m) =
      ∑ l : Fin 5, ∑ i : Fin 5, ∑ m : Fin 5, ∑ j : Fin 5, F i j k l m :=
    fun k => Finset.sum_comm
  have s6 : ∀ k l : Fin 5, (∑ i : Fin 5, ∑ m : Fin 5, ∑ j : Fin 5, F i j k l m) =
      ∑ m : Fin 5, ∑ i : Fin 5, ∑ j : Fin 5, F i j k l m :=
    fun k l => Finset.sum_comm
  calc (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, F i j k l m)
      = ∑ i : Fin 5, ∑ k : Fin 5, ∑ j : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, F i j k l m :=
        Finset.sum_congr rfl (fun i _ => s1 i)
    _ = ∑ i : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ j : Fin 5, ∑ m : Fin 5, F i j k l m :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => s2 i k))
    _ = ∑ i : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ j : Fin 5, F i j k l m :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ =>
          Finset.sum_congr rfl (fun l _ => s3 i k l)))
    _ = ∑ k : Fin 5, ∑ i : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ j : Fin 5, F i j k l m := s4
    _ = ∑ k : Fin 5, ∑ l : Fin 5, ∑ i : Fin 5, ∑ m : Fin 5, ∑ j : Fin 5, F i j k l m :=
        Finset.sum_congr rfl (fun k _ => s5 k)
    _ = ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ i : Fin 5, ∑ j : Fin 5, F i j k l m :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => s6 k l))

/-- `star3to2` is adjoint to `star2to3` with respect to `twoPairing`/`threePairing`, with no
scalar correction and no alternation hypothesis: both sides unfold to the same quintuple sum once
`eps5_block32_iso` identifies the two block orders of `eps5`. -/
theorem star3to2_star2to3_adjoint_iso (b : ThreeCoordinates) (c : TwoCoordinates) :
    twoPairing (star3to2 b) c = threePairing b (star2to3 c) := by
  have hL : twoPairing (star3to2 b) c =
      (1 / 12 : ℝ) * ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5,
        eps5 i j k l m * tangentWeight i * tangentWeight j * tangentWeight k *
          tangentWeight l * tangentWeight m * factorialPairing (b k l m) (c i j) := by
    simp only [twoPairing, star3to2, map_smul, map_sum, LinearMap.smul_apply,
      LinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    apply Finset.sum_congr rfl; intro m _
    ring
  have hR : threePairing b (star2to3 c) =
      (1 / 12 : ℝ) * ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ i : Fin 5, ∑ j : Fin 5,
        eps5 k l m i j * tangentWeight k * tangentWeight l * tangentWeight m *
          tangentWeight i * tangentWeight j * factorialPairing (b k l m) (c i j) := by
    simp only [threePairing, star2to3, map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    apply Finset.sum_congr rfl; intro m _
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hL, hR, sum5_rotate_iso]
  have hEq : (∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ i : Fin 5, ∑ j : Fin 5,
      eps5 i j k l m * tangentWeight i * tangentWeight j * tangentWeight k *
        tangentWeight l * tangentWeight m * factorialPairing (b k l m) (c i j)) =
      ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ i : Fin 5, ∑ j : Fin 5,
        eps5 k l m i j * tangentWeight k * tangentWeight l * tangentWeight m *
          tangentWeight i * tangentWeight j * factorialPairing (b k l m) (c i j) := by
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    apply Finset.sum_congr rfl; intro m _
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [eps5_block32_iso]
    ring
  rw [hEq]

end TernaryPeriodPolynomials.Argument.Coercivity
