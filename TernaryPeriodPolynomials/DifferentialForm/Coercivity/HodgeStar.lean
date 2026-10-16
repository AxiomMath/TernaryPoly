module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeThree

@[expose] public section



/-! A Hodge-star-style reindexing between `TwoCoordinates` and `ThreeCoordinates`, built from a
5-index sign `eps5` on `Fin 5` (the determinant of the 0/1 indicator matrix of a tuple, vanishing
unless the tuple is injective) weighted by `tangentWeight`. This file builds the foundational
`eps5` facts and the two maps `star2to3`/`star3to2`, with their alternating- and
homogeneous-degree-preservation lemmas. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

/-- The sign of a 5-tuple `f : Fin 5 → Fin 5`, as the determinant of its indicator matrix.
Vanishes unless `f` is injective (`epsFive_eq_zero_of_not_injective`), and squares to `1` when it
is (`epsFive_sq_eq_one_of_injective`). -/
def epsFive (f : Fin 5 → Fin 5) : ℝ :=
  Matrix.det (Matrix.of fun i j => if f i = j then (1 : ℝ) else 0)

theorem epsFive_eq_zero_of_not_injective {f : Fin 5 → Fin 5} (hf : ¬ Function.Injective f) :
    epsFive f = 0 := by
  show Matrix.det (Matrix.of fun i j => if f i = j then (1 : ℝ) else 0) = 0
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
  apply Matrix.det_zero_of_row_eq hne
  funext k
  simp [Matrix.of_apply, hij]

theorem epsFive_sq_eq_one_of_injective {f : Fin 5 → Fin 5} (hf : Function.Injective f) :
    epsFive f ^ 2 = 1 := by
  set P : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of fun i j => if f i = j then (1 : ℝ) else 0 with hP
  have hortho : P * P.transpose = (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
    funext i i'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hP, Matrix.of_apply, Matrix.one_apply]
    simp [hf.eq_iff, eq_comm]
  have step : P.det * P.transpose.det = (P * P.transpose).det :=
    (Matrix.det_mul P P.transpose).symm
  rw [Matrix.det_transpose] at step
  rw [hortho, Matrix.det_one] at step
  show P.det ^ 2 = 1
  rw [sq]
  exact step

theorem epsFive_comp_perm (f : Fin 5 → Fin 5) (τ : Equiv.Perm (Fin 5)) :
    epsFive (f ∘ τ) = (Equiv.Perm.sign τ : ℝ) * epsFive f := by
  show Matrix.det (Matrix.of fun i j => if f (τ i) = j then (1 : ℝ) else 0)
    = (Equiv.Perm.sign τ : ℝ) * Matrix.det (Matrix.of fun i j => if f i = j then (1 : ℝ) else 0)
  have hM : (Matrix.of fun i j => if f (τ i) = j then (1 : ℝ) else 0)
      = (Matrix.of fun i j => if f i = j then (1 : ℝ) else 0).submatrix τ id := by
    funext i j
    simp [Matrix.submatrix_apply]
  rw [hM, Matrix.det_permute]

theorem epsFive_comp_swap (f : Fin 5 → Fin 5) {x y : Fin 5} (hxy : x ≠ y) :
    epsFive (f ∘ Equiv.swap x y) = - epsFive f := by
  rw [epsFive_comp_perm f (Equiv.swap x y), Equiv.Perm.sign_swap hxy]
  norm_num

/-- Named 5-argument form of `epsFive`. -/
def eps5 (a b c d e : Fin 5) : ℝ := epsFive ![a, b, c, d, e]

/-- Swapping the first two arguments of `eps5` negates it. -/
theorem eps5_swap01 (a b c d e : Fin 5) : eps5 b a c d e = - eps5 a b c d e := by
  show epsFive ![b, a, c, d, e] = - epsFive ![a, b, c, d, e]
  have h : (![b, a, c, d, e] : Fin 5 → Fin 5) = ![a, b, c, d, e] ∘ Equiv.swap 0 1 := by
    funext w; fin_cases w <;> rfl
  rw [h, epsFive_comp_swap _ (by decide : (0 : Fin 5) ≠ 1)]

/-- Cycling the first three arguments of `eps5` (sending `(a, b, c)` to `(c, a, b)`) leaves it
unchanged, matching `IsAlternatingThree`'s cyclic clause. -/
theorem eps5_cycle201 (a b c d e : Fin 5) : eps5 c a b d e = eps5 a b c d e := by
  show epsFive ![c, a, b, d, e] = epsFive ![a, b, c, d, e]
  have h : (![c, a, b, d, e] : Fin 5 → Fin 5) =
      ![a, b, c, d, e] ∘ (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (0 : Fin 5) 2) := by
    funext w; fin_cases w <;> rfl
  rw [h, epsFive_comp_perm, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0:Fin 5) ≠ 1),
    Equiv.Perm.sign_swap (by decide : (0:Fin 5) ≠ 2)]
  norm_num

/-- Hodge-star-style reindexing from two-forms to three-forms, built from `eps5` weighted by
`tangentWeight`. -/
def star2to3 (a : TwoCoordinates) : ThreeCoordinates := fun i j k =>
  (1 / 2 : ℝ) • ∑ l : Fin 5, ∑ m : Fin 5,
    (eps5 i j k l m * tangentWeight l * tangentWeight m) • a l m

/-- The approximate inverse, from three-forms to two-forms. -/
def star3to2 (b : ThreeCoordinates) : TwoCoordinates := fun i j =>
  (1 / 6 : ℝ) • ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5,
    (eps5 i j k l m * tangentWeight k * tangentWeight l * tangentWeight m) • b k l m

theorem star2to3_swap01 (a : TwoCoordinates) (i j k : Fin 5) :
    star2to3 a i j k = - star2to3 a j i k := by
  show (1 / 2 : ℝ) • ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 i j k l m * tangentWeight l * tangentWeight m) • a l m
    = - ((1 / 2 : ℝ) • ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 j i k l m * tangentWeight l * tangentWeight m) • a l m)
  have hS : (∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 i j k l m * tangentWeight l * tangentWeight m) • a l m)
    = (-1 : ℝ) • ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 j i k l m * tangentWeight l * tangentWeight m) • a l m := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [smul_smul]
    congr 1
    rw [eps5_swap01 i j k l m]
    ring
  rw [hS]
  module

theorem star2to3_cycle (a : TwoCoordinates) (i j k : Fin 5) :
    star2to3 a i j k = star2to3 a k i j := by
  show (1 / 2 : ℝ) • ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 i j k l m * tangentWeight l * tangentWeight m) • a l m
    = (1 / 2 : ℝ) • ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 k i j l m * tangentWeight l * tangentWeight m) • a l m
  have hS : (∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 i j k l m * tangentWeight l * tangentWeight m) • a l m)
    = ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 k i j l m * tangentWeight l * tangentWeight m) • a l m := by
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro m _
    rw [eps5_cycle201 i j k l m]
  rw [hS]

/-- `star2to3` always lands in the alternating three-forms, regardless of whether its input is
alternating (the alternating structure comes entirely from `eps5`). -/
theorem star2to3_alternating (a : TwoCoordinates) : IsAlternatingThree (star2to3 a) :=
  ⟨star2to3_swap01 a, star2to3_cycle a⟩

theorem star3to2_antisymm (b : ThreeCoordinates) (i j : Fin 5) :
    star3to2 b i j = - star3to2 b j i := by
  show (1 / 6 : ℝ) • ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 i j k l m * tangentWeight k * tangentWeight l * tangentWeight m) • b k l m
    = - ((1 / 6 : ℝ) • ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 j i k l m * tangentWeight k * tangentWeight l * tangentWeight m) • b k l m)
  have hS : (∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 i j k l m * tangentWeight k * tangentWeight l * tangentWeight m) • b k l m)
    = (-1 : ℝ) • ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 j i k l m * tangentWeight k * tangentWeight l * tangentWeight m) • b k l m := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [smul_smul]
    congr 1
    rw [eps5_swap01 i j k l m]
    ring
  rw [hS]
  module

/-- `star3to2` always lands in the alternating two-forms. -/
theorem star3to2_alternating (b : ThreeCoordinates) : IsAlternatingTwo (star3to2 b) := by
  intro i j
  rw [star3to2_antisymm b i j]

theorem star2to3_isHomogeneous {n : ℕ} (a : TwoCoordinates)
    (ha : ∀ p q, (a p q).IsHomogeneous n) (i j k : Fin 5) :
    (star2to3 a i j k).IsHomogeneous n := by
  show ((1 / 2 : ℝ) • ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 i j k l m * tangentWeight l * tangentWeight m) • a l m).IsHomogeneous n
  apply (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).smul_mem
  apply MvPolynomial.IsHomogeneous.sum
  intro l _
  apply MvPolynomial.IsHomogeneous.sum
  intro m _
  exact (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).smul_mem _ (ha l m)

theorem star3to2_isHomogeneous {n : ℕ} (b : ThreeCoordinates)
    (hb : ∀ p q r, (b p q r).IsHomogeneous n) (i j : Fin 5) :
    (star3to2 b i j).IsHomogeneous n := by
  show ((1 / 6 : ℝ) • ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 i j k l m * tangentWeight k * tangentWeight l * tangentWeight m) •
        b k l m).IsHomogeneous n
  apply (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).smul_mem
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  apply MvPolynomial.IsHomogeneous.sum
  intro l _
  apply MvPolynomial.IsHomogeneous.sum
  intro m _
  exact (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).smul_mem _ (hb k l m)

end TernaryPeriodPolynomials.Argument.Coercivity
