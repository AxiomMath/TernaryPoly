module

public import Mathlib

@[expose] public section


/-!
# The Pasol–Popa matrix `U` and the binary three-term norms

Formalized by Claude Haiku 5.5.
Proof of Corollary
`cor:complete-periods`.

Convention (Pasol–Popa, arXiv:1202.5802v5, Section 2, as read from the arXiv HTML summary;
not verified against the paper text): `S = [[0,-1],[1,0]]`, `T = [[1,1],[0,1]]`,
`U = TS = [[1,-1],[1,0]]`, and `U³ = J = -I`. A matrix `M = [[a,b],[c,d]]` acts on a binary
form `q` by `(M·q)(X,Y) = q(aX+bY, cX+dY)`; this is the homogenization of the one-variable
action `P|g(z) = (cz+d)^n P(gz)` under `P(X) ↦ Y^n P(X/Y)`. With this convention `U²` acts as
`(X,Y) ↦ (-Y, X-Y)`, the substitution printed in the paper.

Proved here: `U³ = -1` as an integer matrix identity; the action of `U²`; `act (-1) q = (-1)^n q`
for a form of degree `n`; the homogenized one-variable formula; `T³ = id` for `T = act U²`;
and, for even `n`, the paper's third term `q(Y-X,-X)` equals the Pasol–Popa term `q|U`, so
the printed three-term norm agrees with the Pasol–Popa norm on even-degree forms.
-/

open MvPolynomial Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Section67Claims.PasolPopa

/-- `S = [[0,-1],[1,0]]`. -/
def PPS : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

/-- `T = [[1,1],[0,1]]`. -/
def PPT : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]

/-- `U = TS = [[1,-1],[1,0]]`, the Pasol–Popa matrix. -/
def PPU : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 1, 0]

theorem PPU_eq_TS : PPU = PPT * PPS := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PPU, PPT, PPS, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pasol–Popa: `U³ = J = -I`, as an integer matrix identity. -/
theorem PPU_cube : PPU ^ 3 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, PPU, Matrix.mul_apply, Fin.sum_univ_two]

/-- `U² = [[0,-1],[1,-1]]`. -/
theorem PPU_sq : PPU ^ 2 = !![0, -1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, PPU, Matrix.mul_apply, Fin.sum_univ_two]

variable {R : Type*} [CommRing R]

/-- The two substitutions of a matrix `M = [[a,b],[c,d]]`: `X ↦ aX+bY`, `Y ↦ cX+dY`. -/
def actSub (M : Matrix (Fin 2) (Fin 2) ℤ) : Fin 2 → MvPolynomial (Fin 2) R :=
  ![(M 0 0 : MvPolynomial (Fin 2) R) * X 0 + (M 0 1 : MvPolynomial (Fin 2) R) * X 1,
    (M 1 0 : MvPolynomial (Fin 2) R) * X 0 + (M 1 1 : MvPolynomial (Fin 2) R) * X 1]

/-- Action of `M` on binary forms: `(act M q)(X,Y) = q(aX+bY, cX+dY)`. -/
def act (M : Matrix (Fin 2) (Fin 2) ℤ) (q : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  bind₁ (actSub M) q

theorem actSub_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    bind₁ (actSub (R := R) N) (actSub (R := R) M i) = actSub (R := R) (M * N) i := by
  fin_cases i
  · simp [actSub, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_intCast,
      bind₁_X_right]
    ring
  · simp [actSub, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_intCast,
      bind₁_X_right]
    ring

/-- `act` is a right action: `act (M * N) q = act N (act M q)`. -/
theorem act_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) (q : MvPolynomial (Fin 2) R) :
    act (M * N) q = act N (act M q) := by
  unfold act
  rw [bind₁_bind₁]
  simp only [actSub_mul]

theorem act_one (q : MvPolynomial (Fin 2) R) : act 1 q = q := by
  have h : actSub (R := R) (1 : Matrix (Fin 2) (Fin 2) ℤ) = fun i => X i := by
    funext i
    fin_cases i <;> simp [actSub]
  unfold act
  rw [h, bind₁_X_left]
  rfl

/-- `U²` acts as the substitution `(X,Y) ↦ (-Y, X-Y)` printed in the paper. -/
theorem act_PPU_sq (q : MvPolynomial (Fin 2) R) :
    act (PPU ^ 2) q = bind₁ ![-X 1, X 0 - X 1] q := by
  have h : actSub (R := R) (PPU ^ 2) = ![-X 1, X 0 - X 1] := by
    rw [PPU_sq]
    funext i
    fin_cases i
    · simp [actSub]
    · simp [actSub, sub_eq_add_neg]
  unfold act
  rw [h]

/-- Product over the support of a Fin-2 exponent vector. -/
theorem prod_support_fin2 {M : Type*} [CommMonoid M] (f : Fin 2 → M) (d : Fin 2 →₀ ℕ) :
    ∏ i ∈ d.support, f i ^ d i = f 0 ^ d 0 * f 1 ^ d 1 := by
  have h2 : ∏ i : Fin 2, f i ^ d i = f 0 ^ d 0 * f 1 ^ d 1 := Fin.prod_univ_two _
  rw [← h2]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  have : d i = 0 := by simpa using hi
  simp [this]

/-- Degree of the exponents of a monomial of a homogeneous form. -/
theorem deg_of_mem {K : Type*} [CommRing K] {n : ℕ} {q : MvPolynomial (Fin 2) K}
    (hq : q.IsHomogeneous n) {d : Fin 2 →₀ ℕ} (hd : d ∈ q.support) : d 0 + d 1 = n := by
  have h := hq (MvPolynomial.mem_support_iff.mp hd)
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using h

/-- The action of `-1` on a form of degree `n` is multiplication by `(-1)^n`. -/
theorem act_neg_one {n : ℕ} {q : MvPolynomial (Fin 2) R} (hq : q.IsHomogeneous n) :
    act (-1) q = C ((-1 : R) ^ n) * q := by
  have hsub : actSub (-1) = fun i => C (-1 : R) * X i := by
    funext i
    fin_cases i <;> simp [actSub]
  unfold act
  rw [hsub]
  conv_lhs => rw [q.as_sum]
  conv_rhs => rw [q.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := deg_of_mem hq hd
  rw [bind₁_monomial, monomial_eq]
  simp only [Finsupp.prod]
  rw [prod_support_fin2, prod_support_fin2]
  simp only [mul_pow, ← map_pow]
  have hc : (C ((-1 : R) ^ d 0) * C ((-1 : R) ^ d 1) : MvPolynomial (Fin 2) R) =
      C ((-1 : R) ^ n) := by
    rw [← C_mul, ← pow_add, hdeg]
  linear_combination (C (q.coeff d) * X 0 ^ d 0 * X 1 ^ d 1) * hc

/-- Even-degree forms are fixed by `act (-1)`. -/
theorem act_neg_one_even {n : ℕ} (hn : Even n) {q : MvPolynomial (Fin 2) R}
    (hq : q.IsHomogeneous n) : act (-1) q = q := by
  rw [act_neg_one hq, hn.neg_one_pow, map_one, one_mul]

/-- The printed third term is the Pasol–Popa term `act (-U)`, and on even forms `act (-U) = act U`. -/
theorem third_term_eq_act_PPU {n : ℕ} (hn : Even n) {q : MvPolynomial (Fin 2) R}
    (hq : q.IsHomogeneous n) :
    bind₁ ![X 1 - X 0, -X 0] q = act PPU q := by
  have hneg : (-PPU : Matrix (Fin 2) (Fin 2) ℤ) = (-1) * PPU := by simp
  have hA : act (-PPU) q = act PPU q := by
    rw [hneg, act_mul, act_neg_one_even hn hq]
  have h : actSub (R := R) (-PPU) = ![X 1 - X 0, -X 0] := by
    funext i
    fin_cases i
    · simp [actSub, PPU, sub_eq_add_neg, add_comm]
    · simp [actSub, PPU, sub_eq_add_neg]
  rw [← hA]
  unfold act
  rw [h]

/-- `T = act U²` has order three: `T³ = id` on all binary forms. -/
theorem act_PPU_sq_cube (q : MvPolynomial (Fin 2) R) :
    act (PPU ^ 2) (act (PPU ^ 2) (act (PPU ^ 2) q)) = q := by
  rw [← act_mul, ← act_mul]
  have h6 : PPU ^ 2 * (PPU ^ 2 * PPU ^ 2) = 1 := by
    rw [← pow_add, ← pow_add, show 2 + (2 + 2) = 3 * 2 from rfl, pow_mul, PPU_cube, neg_one_sq]
  rw [h6, act_one]

/-- Evaluation of a bind along a point: `eval` of a substitution. -/
theorem eval_act_PPU_sq {K : Type*} [Field K] {n : ℕ} {q : MvPolynomial (Fin 2) K}
    (hq : q.IsHomogeneous n) {x : K} (hx : x ≠ 1) :
    eval ![x, 1] (act (PPU ^ 2) q) = (x - 1) ^ n * eval ![-1 / (x - 1), 1] q := by
  have hne : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  rw [act_PPU_sq]
  have h1 : eval ![x, 1] (bind₁ ![-X 1, X 0 - X 1] q) =
      eval (fun i => eval ![x, 1] (![-X 1, X 0 - X 1] i)) q :=
    eval₂Hom_bind₁ (RingHom.id K) ![x, 1] _ q
  rw [h1]
  have hfun : (fun i => eval ![x, 1] (![-X 1, X 0 - X 1] i)) =
      fun i => (x - 1) * (![-1 / (x - 1), 1] : Fin 2 → K) i := by
    funext i
    fin_cases i
    · simp
      field_simp
    · simp
  rw [hfun]
  have hs : ∀ (t : K) (v : Fin 2 → K), eval (fun i => t * v i) q = t ^ n * eval v q := by
    intro t v
    rw [eval_eq, eval_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdeg := deg_of_mem hq hd
    have hsub : ∑ i ∈ d.support, d i = ∑ i, d i := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simpa using hi
    have hsum : ∑ i ∈ d.support, d i = n := by
      rw [hsub, Fin.sum_univ_two, hdeg]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
    ring
  rw [hs]

/-- The printed binary three-term norm equals the Pasol–Popa norm
`q + q|U + q|U²` on even-degree forms: the two printed terms are `act (PPU^2)` and `act (-U)`,
and `act (-U) = act U` on even degree. -/
theorem printed_three_term_eq_pp_norm {n : ℕ} (hn : Even n) {q : MvPolynomial (Fin 2) R}
    (hq : q.IsHomogeneous n) :
    q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q =
      q + act PPU q + act (PPU ^ 2) q := by
  rw [third_term_eq_act_PPU hn hq, act_PPU_sq]
  ring

/-- Consequently, on even-degree forms the printed period relation and the Pasol–Popa relation
`q|(1+U+U²) = 0` coincide. -/
theorem printed_relation_iff_pp {n : ℕ} (hn : Even n) {q : MvPolynomial (Fin 2) R}
    (hq : q.IsHomogeneous n) :
    q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0 ↔
      q + act PPU q + act (PPU ^ 2) q = 0 := by
  rw [printed_three_term_eq_pp_norm hn hq]

end TernaryPeriodPolynomials.Argument.Section67Claims.PasolPopa
