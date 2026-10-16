module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Plane
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Std

@[expose] public section


/-!
# Lemma B.1, boundary route: orientation of triples of plane vectors, and the classes `G2`, `Eg`

`ob y z w = D(y,z) D(z,w) D(w,y)` (`D` the `2 × 2` determinant) is invariant under sign changes of the vectors,
changes sign under transpositions and is multiplied by `det(C)³` under `C ∈ GL₂`.  The class
`G2 a = sign(ob a) [(e₀, a₀, a₁, a₂)]` of the ordered hexagon, and `Eg a b = [(e₀, a, b)]` of the ordered
top cell, are then invariant (resp. antisymmetric) under sign changes and permutations of the vectors.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory Finsupp TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract

/-- The `2 × 2` determinant of two plane vectors. -/
def D2 (y z : Fin 2 → ℤ) : ℤ := y 0 * z 1 - y 1 * z 0

/-- The orientation of a triple of plane vectors. -/
def ob (y z w : Fin 2 → ℤ) : ℤ := D2 y z * D2 z w * D2 w y

theorem ob_neg_left (y z w : Fin 2 → ℤ) : ob (-y) z w = ob y z w := by
  simp only [ob, D2, Pi.neg_apply]; ring

theorem ob_neg_mid (y z w : Fin 2 → ℤ) : ob y (-z) w = ob y z w := by
  simp only [ob, D2, Pi.neg_apply]; ring

theorem ob_neg_right (y z w : Fin 2 → ℤ) : ob y z (-w) = ob y z w := by
  simp only [ob, D2, Pi.neg_apply]; ring

theorem ob_swap01 (y z w : Fin 2 → ℤ) : ob z y w = - ob y z w := by
  simp only [ob, D2]; ring

theorem ob_swap12 (y z w : Fin 2 → ℤ) : ob y w z = - ob y z w := by
  simp only [ob, D2]; ring

theorem ob_swap02 (y z w : Fin 2 → ℤ) : ob w z y = - ob y z w := by
  simp only [ob, D2]; ring

theorem ob_mulVec (C : Matrix (Fin 2) (Fin 2) ℤ) (y z w : Fin 2 → ℤ) :
    ob (C.mulVec y) (C.mulVec z) (C.mulVec w) = C.det ^ 3 * ob y z w := by
  simp only [ob, D2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring

theorem ob_sign (ε : Fin 3 → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (a : Fin 3 → Fin 2 → ℤ) :
    ob (ε 0 • a 0) (ε 1 • a 1) (ε 2 • a 2) = ob (a 0) (a 1) (a 2) := by
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2 | h2 <;>
    simp only [h0, h1, h2, one_smul, neg_one_smul, ob_neg_left, ob_neg_mid, ob_neg_right]

theorem ob_sw01 (a : Fin 3 → Fin 2 → ℤ) :
    ob (a (Equiv.swap (0 : Fin 3) 1 0)) (a (Equiv.swap (0 : Fin 3) 1 1)) (a (Equiv.swap (0 : Fin 3) 1 2)) =
      - ob (a 0) (a 1) (a 2) := by
  have h0 : Equiv.swap (0 : Fin 3) 1 0 = 1 := by decide
  have h1 : Equiv.swap (0 : Fin 3) 1 1 = 0 := by decide
  have h2 : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
  rw [h0, h1, h2, ob_swap01]

theorem ob_sw02 (a : Fin 3 → Fin 2 → ℤ) :
    ob (a (Equiv.swap (0 : Fin 3) 2 0)) (a (Equiv.swap (0 : Fin 3) 2 1)) (a (Equiv.swap (0 : Fin 3) 2 2)) =
      - ob (a 0) (a 1) (a 2) := by
  have h0 : Equiv.swap (0 : Fin 3) 2 0 = 2 := by decide
  have h1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := by decide
  have h2 : Equiv.swap (0 : Fin 3) 2 2 = 0 := by decide
  rw [h0, h1, h2, ob_swap02]

theorem ob_sw12 (a : Fin 3 → Fin 2 → ℤ) :
    ob (a (Equiv.swap (1 : Fin 3) 2 0)) (a (Equiv.swap (1 : Fin 3) 2 1)) (a (Equiv.swap (1 : Fin 3) 2 2)) =
      - ob (a 0) (a 1) (a 2) := by
  have h0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
  have h1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide
  have h2 : Equiv.swap (1 : Fin 3) 2 2 = 1 := by decide
  rw [h0, h1, h2, ob_swap12]

theorem ob_swap_apply (a : Fin 3 → Fin 2 → ℤ) (i j : Fin 3) (hij : i ≠ j) :
    ob (a (Equiv.swap i j 0)) (a (Equiv.swap i j 1)) (a (Equiv.swap i j 2)) = - ob (a 0) (a 1) (a 2) := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact ob_sw01 a
    | exact ob_sw02 a
    | exact ob_sw12 a

/-- The class of the ordered hexagon `(e₀, a₀, a₁, a₂)` with the sign of its orientation. -/
def G2 (a : Fin 3 → Fin 2 → ℤ) : (PhiX 2).V :=
  ((Int.sign (ob (a 0) (a 1) (a 2)) : ℤ) : ℚ) •
    clsU 2 (tupleVec 2 (Fin.cons e0L (fun i => pl (a i)) : Fin 4 → Line))

theorem G2_sign (ε : Fin 3 → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (a : Fin 3 → Fin 2 → ℤ) :
    G2 (fun i => ε i • a i) = G2 a := by
  unfold G2
  simp only [ob_sign ε hε a]
  have : ∀ i, pl (ε i • a i) = pl (a i) := by
    intro i
    rw [pl_eq_iff]
    rcases hε i with h | h
    · left; simp [h]
    · right; simp [h]
  simp only [this]

theorem G2_swap (a : Fin 3 → Fin 2 → ℤ) (i j : Fin 3) (hij : i ≠ j) :
    G2 (fun k => a (Equiv.swap i j k)) = G2 a := by
  unfold G2
  have hob : Int.sign (ob (a (Equiv.swap i j 0)) (a (Equiv.swap i j 1)) (a (Equiv.swap i j 2))) =
      - Int.sign (ob (a 0) (a 1) (a 2)) := by
    rw [ob_swap_apply a i j hij, Int.sign_neg]
  have htup : (Fin.cons e0L (fun k => pl (a (Equiv.swap i j k))) : Fin 4 → Line) =
      fun k => (Fin.cons e0L (fun k => pl (a k)) : Fin 4 → Line) (Equiv.swap i.succ j.succ k) := by
    funext k
    refine Fin.cases ?_ (fun m => ?_) k
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm]
      simp
    · rw [Fin.succ_injective _ |>.swap_apply]
      simp
  rw [hob, htup]
  by_cases hok : TupleOK 2 (Fin.cons e0L (fun k => pl (a k)) : Fin 4 → Line)
  · rw [tupleVec_perm hok, Equiv.Perm.sign_swap (fun h => hij (Fin.succ_injective _ h)), clsU_smul]
    simp
  · have : ¬ TupleOK 2 (fun k => (Fin.cons e0L (fun k => pl (a k)) : Fin 4 → Line)
        (Equiv.swap i.succ j.succ k)) := fun h => hok ((TupleOK.perm_iff _ _).mp h)
    rw [tupleVec_of_not_ok hok, tupleVec_of_not_ok this, clsU_zero]
    simp

theorem G2_perm (π : Equiv.Perm (Fin 3)) (a : Fin 3 → Fin 2 → ℤ) : G2 (fun k => a (π k)) = G2 a := by
  induction π using Equiv.Perm.swap_induction_on generalizing a with
  | one => rfl
  | swap_mul f x y hxy ih =>
    have h1 : (fun k => a ((Equiv.swap x y * f) k)) = fun k => (fun m => a (Equiv.swap x y m)) (f k) := by
      funext k; rfl
    rw [h1]
    exact (ih (fun m => a (Equiv.swap x y m))).trans (G2_swap a x y hxy)

/-- The class of the ordered top cell `(e₀, a, b)`. -/
def Eg (a b : Fin 2 → ℤ) : (PhiX 3).V := clsU 3 (tupleVec 3 ![e0L, pl a, pl b])

theorem Eg_swap (a b : Fin 2 → ℤ) : Eg b a = - Eg a b := by
  unfold Eg
  have htup : (![e0L, pl b, pl a] : Fin 3 → Line) = fun k => (![e0L, pl a, pl b] : Fin 3 → Line)
      (Equiv.swap (1 : Fin 3) 2 k) := by
    funext k
    have h0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
    have h1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide
    have h2 : Equiv.swap (1 : Fin 3) 2 2 = 1 := by decide
    fin_cases k
    · simp [h0]
    · simp [h1]
    · simp [h2]
  rw [htup]
  by_cases hok : TupleOK 3 (![e0L, pl a, pl b] : Fin 3 → Line)
  · rw [tupleVec_perm hok, Equiv.Perm.sign_swap (by decide), clsU_smul]
    simp
  · have : ¬ TupleOK 3 (fun k => (![e0L, pl a, pl b] : Fin 3 → Line) (Equiv.swap (1 : Fin 3) 2 k)) :=
      fun h => hok ((TupleOK.perm_iff _ _).mp h)
    rw [tupleVec_of_not_ok hok, tupleVec_of_not_ok this, clsU_zero]
    simp

theorem Eg_neg_left (a b : Fin 2 → ℤ) : Eg (-a) b = Eg a b := by
  unfold Eg
  have : pl (-a) = pl a := by rw [pl_eq_iff]; right; exact (neg_neg _).symm
  rw [this]

theorem Eg_neg_right (a b : Fin 2 → ℤ) : Eg a (-b) = Eg a b := by
  unfold Eg
  have : pl (-b) = pl b := by rw [pl_eq_iff]; right; exact (neg_neg _).symm
  rw [this]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
