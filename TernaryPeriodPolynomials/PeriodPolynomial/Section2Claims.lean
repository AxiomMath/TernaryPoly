module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.Definitions
public import TernaryPeriodPolynomials.Polynomial.Restriction

@[expose] public section


/-!
# Section 2 unnumbered polynomial claims

Formalized by Claude Haiku 5.5.

Standalone statements and proofs for the unnumbered polynomial claims of Section 2 of
the paper. Each theorem
docstring cites the paper lines carrying its claim.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.Statements.Section2Claims

/-- Substitution vectors in three variables (the arguments of `bind₁`). -/
abbrev Vec3 (F : Type*) [CommRing F] := Fin 3 → MvPolynomial (Fin 3) F

/-- Substitution vectors in two variables (the arguments of `bind₁`). -/
abbrev Vec2 (F : Type*) [CommRing F] := Fin 2 → MvPolynomial (Fin 2) F

/-- Composition of substitutions: if `u (v i) = w i` for every `i`, then
`u` applied after `v` on `f` is `w` applied to `f`. -/
theorem bind_bind_vec {F : Type*} [CommSemiring F] {n : ℕ} (u v w : Fin n → MvPolynomial (Fin n) F)
    (h : ∀ i, bind₁ u (v i) = w i) (f : MvPolynomial (Fin n) F) :
    bind₁ u (bind₁ v f) = bind₁ w f := by
  rw [bind₁_bind₁]
  have hfun : (fun i => bind₁ u (v i)) = w := funext h
  rw [hfun]

/-- Substitution by the coordinate vector `X` is the identity. -/
theorem bind_X_id {F : Type*} [CommSemiring F] {n : ℕ} (g : MvPolynomial (Fin n) F) :
    bind₁ (X : Fin n → MvPolynomial (Fin n) F) g = g := by
  rw [bind₁_X_left]
  rfl

/-! ### Claim 1: polynomial operators (`eq:polynomial-operators`) -/

/-- Paper: `A² f = f(y-x, -x, z)`, i.e. `A(A f) = bind₁ ![X 1 - X 0, -X 0, X 2] f`. -/
theorem section2_A_sq {F : Type*} [CommRing F] (f : MvPolynomial (Fin 3) F) :
    bind₁ (![-X 1, X 0 - X 1, X 2] : Vec3 F) (bind₁ (![-X 1, X 0 - X 1, X 2] : Vec3 F) f) =
      bind₁ (![X 1 - X 0, -X 0, X 2] : Vec3 F) f :=
  bind_bind_vec (n := 3) (![-X 1, X 0 - X 1, X 2] : Vec3 F) (![-X 1, X 0 - X 1, X 2] : Vec3 F)
    (![X 1 - X 0, -X 0, X 2] : Vec3 F) (fun i => by fin_cases i <;> first | (simp; done) | (simp; ring)) f

/-- Paper: `A³ = I`. -/
theorem section2_A_cube {F : Type*} [CommRing F] (f : MvPolynomial (Fin 3) F) :
    bind₁ (![-X 1, X 0 - X 1, X 2] : Vec3 F) (bind₁ (![-X 1, X 0 - X 1, X 2] : Vec3 F)
      (bind₁ (![-X 1, X 0 - X 1, X 2] : Vec3 F) f)) = f := by
  rw [section2_A_sq]
  rw [bind_bind_vec (n := 3) (![X 1 - X 0, -X 0, X 2] : Vec3 F)
    (![-X 1, X 0 - X 1, X 2] : Vec3 F) (X : Vec3 F)
    (fun i => by fin_cases i <;> simp) f]
  exact bind_X_id f

/-- Paper: `S A S = A²`, i.e. `S (A (S f)) = A (A f)`. -/
theorem section2_S_A_S {F : Type*} [CommRing F] (f : MvPolynomial (Fin 3) F) :
    bind₁ (![X 1, X 0, X 2] : Vec3 F) (bind₁ (![-X 1, X 0 - X 1, X 2] : Vec3 F)
      (bind₁ (![X 1, X 0, X 2] : Vec3 F) f)) =
      bind₁ (![-X 1, X 0 - X 1, X 2] : Vec3 F) (bind₁ (![-X 1, X 0 - X 1, X 2] : Vec3 F) f) := by
  rw [bind_bind_vec (n := 3) (![-X 1, X 0 - X 1, X 2] : Vec3 F) (![X 1, X 0, X 2] : Vec3 F)
    (![X 0 - X 1, -X 1, X 2] : Vec3 F) (fun i => by fin_cases i <;> simp) f]
  rw [section2_A_sq]
  rw [bind_bind_vec (n := 3) (![X 1, X 0, X 2] : Vec3 F) (![X 0 - X 1, -X 1, X 2] : Vec3 F)
    (![X 1 - X 0, -X 0, X 2] : Vec3 F) (fun i => by fin_cases i <;> simp) f]

/-- Paper: `S C S = C²`, i.e. `S (C (S f)) = C (C f)`. -/
theorem section2_S_C_S {F : Type*} [CommRing F] (f : MvPolynomial (Fin 3) F) :
    bind₁ (![X 1, X 0, X 2] : Vec3 F) (bind₁ (![X 1, X 2, X 0] : Vec3 F)
      (bind₁ (![X 1, X 0, X 2] : Vec3 F) f)) =
      bind₁ (![X 1, X 2, X 0] : Vec3 F) (bind₁ (![X 1, X 2, X 0] : Vec3 F) f) := by
  rw [bind_bind_vec (n := 3) (![X 1, X 2, X 0] : Vec3 F) (![X 1, X 0, X 2] : Vec3 F)
    (![X 2, X 1, X 0] : Vec3 F) (fun i => by fin_cases i <;> simp) f]
  rw [bind_bind_vec (n := 3) (![X 1, X 0, X 2] : Vec3 F) (![X 2, X 1, X 0] : Vec3 F)
    (![X 2, X 0, X 1] : Vec3 F) (fun i => by fin_cases i <;> simp) f]
  rw [bind_bind_vec (n := 3) (![X 1, X 2, X 0] : Vec3 F) (![X 1, X 2, X 0] : Vec3 F)
    (![X 2, X 0, X 1] : Vec3 F) (fun i => by fin_cases i <;> simp) f]

/-- Paper: `C³ = I`. -/
theorem section2_C_cube {F : Type*} [CommRing F] (f : MvPolynomial (Fin 3) F) :
    bind₁ (![X 1, X 2, X 0] : Vec3 F) (bind₁ (![X 1, X 2, X 0] : Vec3 F)
      (bind₁ (![X 1, X 2, X 0] : Vec3 F) f)) = f := by
  rw [bind_bind_vec (n := 3) (![X 1, X 2, X 0] : Vec3 F) (![X 1, X 2, X 0] : Vec3 F)
    (![X 2, X 0, X 1] : Vec3 F) (fun i => by fin_cases i <;> simp) f]
  rw [bind_bind_vec (n := 3) (![X 1, X 2, X 0] : Vec3 F) (![X 2, X 0, X 1] : Vec3 F)
    (X : Vec3 F) (fun i => by fin_cases i <;> simp) f]
  exact bind_X_id f

/-! ### Claim 2: low-degree norm values -/

/-- Paper: `N(1) = 3`. -/
theorem section2_norm_one {F : Type*} [CommRing F] :
    TernaryPeriodPolynomials.Argument.threeTermNorm (1 : MvPolynomial (Fin 3) F) = 3 := by
  simp [TernaryPeriodPolynomials.Argument.threeTermNorm]
  ring

/-- Paper: `N(x+y+z) = 3z`. -/
theorem section2_norm_linear {F : Type*} [CommRing F] :
    TernaryPeriodPolynomials.Argument.threeTermNorm (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) F) =
      3 * X 2 := by
  simp [TernaryPeriodPolynomials.Argument.threeTermNorm]
  ring

/-- Paper: `N(x²+y²+z²) = 4(x²-xy+y²) + 3z²`. -/
theorem section2_norm_sq_sum {F : Type*} [CommRing F] :
    TernaryPeriodPolynomials.Argument.threeTermNorm
        (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 : MvPolynomial (Fin 3) F) =
      4 * (X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2) + 3 * X 2 ^ 2 := by
  simp [TernaryPeriodPolynomials.Argument.threeTermNorm]
  ring

/-- Paper: `N(xy+yz+zx) = x²-xy+y²`. -/
theorem section2_norm_sq_pair {F : Type*} [CommRing F] :
    TernaryPeriodPolynomials.Argument.threeTermNorm
        (X 0 * X 1 + X 1 * X 2 + X 2 * X 0 : MvPolynomial (Fin 3) F) =
      X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2 := by
  simp [TernaryPeriodPolynomials.Argument.threeTermNorm]
  ring

/-- Paper: `N(x³+y³+z³) = 3z³`. -/
theorem section2_norm_cube_sum {F : Type*} [CommRing F] :
    TernaryPeriodPolynomials.Argument.threeTermNorm
        (X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 : MvPolynomial (Fin 3) F) =
      3 * X 2 ^ 3 := by
  simp [TernaryPeriodPolynomials.Argument.threeTermNorm]
  ring

/-- The norm of the degree-three form `m₂₁`. -/
theorem section2_norm_m21 {F : Type*} [CommRing F] :
    TernaryPeriodPolynomials.Argument.threeTermNorm
        (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 + X 0 * X 1 ^ 2 + X 0 * X 2 ^ 2 + X 1 ^ 2 * X 2 +
          X 1 * X 2 ^ 2 : MvPolynomial (Fin 3) F) =
      -((X 0 + X 1) * (2 * X 0 - X 1) * (X 0 - 2 * X 1)) +
        4 * X 2 * (X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2) := by
  simp [TernaryPeriodPolynomials.Argument.threeTermNorm]
  ring

/-- Paper: `N(xyz) = z(x²-xy+y²)`. -/
theorem section2_norm_xyz {F : Type*} [CommRing F] :
    TernaryPeriodPolynomials.Argument.threeTermNorm
        (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) F) =
      X 2 * (X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2) := by
  simp [TernaryPeriodPolynomials.Argument.threeTermNorm]
  ring

/-- The norm of the Vandermonde product. -/
theorem section2_norm_vandermonde {F : Type*} [CommRing F] :
    TernaryPeriodPolynomials.Argument.threeTermNorm
        ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2) : MvPolynomial (Fin 3) F) =
      3 * X 0 * X 1 * (X 0 - X 1) := by
  simp [TernaryPeriodPolynomials.Argument.threeTermNorm]
  ring


open TernaryPoly.Paper

/-! ### Claim 4: parity -/

/-- Scaling: a homogeneous binary form of degree `d` is multiplied by `t ^ d` under the
substitution `(X, Y) ↦ (t X, t Y)`. -/
theorem bind_scale_homog {F : Type*} [CommRing F] {d : ℕ} {q : MvPolynomial (Fin 2) F}
    (hq : q.IsHomogeneous d) (t : F) :
    bind₁ (fun i => C t * X i : Fin 2 → MvPolynomial (Fin 2) F) q = C (t ^ d) * q := by
  have hterm : ∀ e ∈ q.support,
      bind₁ (fun i => C t * X i : Fin 2 → MvPolynomial (Fin 2) F) (monomial e (q.coeff e)) =
        C (t ^ d) * monomial e (q.coeff e) := by
    intro e he
    have hd : d = ∑ i ∈ e.support, e i := hq.degree_eq_sum_deg_support he
    have hprod : ∏ i ∈ e.support, (C t * X i) ^ e i =
        C (t ^ d) * ∏ i ∈ e.support, X i ^ e i := by
      simp only [mul_pow]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← hd, map_pow]
    simp only [bind₁_monomial]
    rw [hprod, monomial_eq, Finsupp.prod]
    ring
  conv_lhs => rw [as_sum q]
  rw [map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← as_sum q]

/-- Under `ε = ±1` the parity relations give
`q(-X,-Y) = q(X,Y)`, and `q` vanishes when its degree is odd. -/
theorem section2_parity_neg {F : Type*} [Field F] [CharZero F] {ε : F} (hε : ε = 1 ∨ ε = -1)
    {q : MvPolynomial (Fin 2) F} {d : ℕ} (hq : q.IsHomogeneous d)
    (h1 : bind₁ (![-X 0, X 1] : Vec2 F) q = -(C ε * q))
    (h2 : bind₁ (![X 0, -X 1] : Vec2 F) q = -(C ε * q)) :
    bind₁ (![-X 0, -X 1] : Vec2 F) q = q ∧ (Odd d → q = 0) := by
  have hε2 : (C ε : MvPolynomial (Fin 2) F) * C ε = 1 := by
    rcases hε with rfl | rfl <;> simp
  have key : bind₁ (![-X 0, -X 1] : Vec2 F) q = q := by
    rw [← bind_bind_vec (n := 2) (![X 0, -X 1] : Vec2 F) (![-X 0, X 1] : Vec2 F)
      (![-X 0, -X 1] : Vec2 F) (fun i => by fin_cases i <;> simp) q, h1, map_neg, map_mul,
      bind₁_C_right, h2]
    linear_combination q * hε2
  refine ⟨key, fun hodd => ?_⟩
  have hv : (![-X 0, -X 1] : Vec2 F) = fun i => C (-1 : F) * X i := by
    funext i
    fin_cases i <;> simp
  have h3 := bind_scale_homog hq (-1 : F)
  rw [← hv, Odd.neg_one_pow hodd, key, map_neg, map_one] at h3
  have h4 : (2 : MvPolynomial (Fin 2) F) * q = 0 := by
    linear_combination h3
  exact (mul_eq_zero.mp h4).resolve_left two_ne_zero

/-- Axis form (`ε = 1`): the axes of a binary period vanish. -/
theorem section2_parity_axes {F : Type*} [Field F] [CharZero F] {q : MvPolynomial (Fin 2) F}
    (h1 : bind₁ (![-X 0, X 1] : Vec2 F) q = -q) (h2 : bind₁ (![X 0, -X 1] : Vec2 F) q = -q) :
    bind₁ (![X 0, 0] : Vec2 F) q = 0 ∧ bind₁ (![0, X 1] : Vec2 F) q = 0 := by
  constructor
  · have e := bind_bind_vec (n := 2) (![X 0, 0] : Vec2 F) (![X 0, -X 1] : Vec2 F)
      (![X 0, 0] : Vec2 F) (fun i => by fin_cases i <;> simp) q
    rw [h2, map_neg] at e
    have h4 : (2 : MvPolynomial (Fin 2) F) * bind₁ (![X 0, 0] : Vec2 F) q = 0 := by
      linear_combination -e
    exact (mul_eq_zero.mp h4).resolve_left two_ne_zero
  · have e := bind_bind_vec (n := 2) (![0, X 1] : Vec2 F) (![-X 0, X 1] : Vec2 F)
      (![0, X 1] : Vec2 F) (fun i => by fin_cases i <;> simp) q
    rw [h1, map_neg] at e
    have h4 : (2 : MvPolynomial (Fin 2) F) * bind₁ (![0, X 1] : Vec2 F) q = 0 := by
      linear_combination -e
    exact (mul_eq_zero.mp h4).resolve_left two_ne_zero

/-! ### Claims 5 and 6: binary addition and lifts -/

/-- Swap relation, shifted: `q(Y, X - Y) = ε q(X - Y, Y)`. -/
theorem bin_shift_swap {F : Type*} [CommRing F] {ε : F} {q : MvPolynomial (Fin 2) F}
    (hswap : bind₁ (![X 1, X 0] : Vec2 F) q = C ε * q) :
    bind₁ (![X 1, X 0 - X 1] : Vec2 F) q = C ε * bind₁ (![X 0 - X 1, X 1] : Vec2 F) q := by
  rw [← bind_bind_vec (n := 2) (![X 0 - X 1, X 1] : Vec2 F) (![X 1, X 0] : Vec2 F)
    (![X 1, X 0 - X 1] : Vec2 F) (fun i => by fin_cases i <;> simp) q, hswap, map_mul,
    bind₁_C_right]

/-- `q(-X, X - Y)` in terms of `q(X - Y, Y)`. -/
theorem bin_neg_first {F : Type*} [CommRing F] {ε : F} {q : MvPolynomial (Fin 2) F}
    (hswap : bind₁ (![X 1, X 0] : Vec2 F) q = C ε * q)
    (hneg1 : bind₁ (![-X 0, X 1] : Vec2 F) q = -(C ε * q)) :
    bind₁ (![-X 1, X 0 - X 1] : Vec2 F) q = -(C ε * (C ε * bind₁ (![X 0 - X 1, X 1] : Vec2 F) q)) := by
  rw [← bind_bind_vec (n := 2) (![X 1, X 0 - X 1] : Vec2 F) (![-X 0, X 1] : Vec2 F)
    (![-X 1, X 0 - X 1] : Vec2 F) (fun i => by fin_cases i <;> simp) q, hneg1, map_neg, map_mul,
    bind₁_C_right, bin_shift_swap hswap]

/-- `q(Y - X, -X)` in terms of `q(X, X - Y)`. -/
theorem bin_neg_second {F : Type*} [CommRing F] {ε : F} {q : MvPolynomial (Fin 2) F}
    (hswap : bind₁ (![X 1, X 0] : Vec2 F) q = C ε * q)
    (hneg1 : bind₁ (![-X 0, X 1] : Vec2 F) q = -(C ε * q))
    (hneg2 : bind₁ (![X 0, -X 1] : Vec2 F) q = -(C ε * q)) :
    bind₁ (![X 1 - X 0, -X 0] : Vec2 F) q =
      C ε * (C ε * (C ε * bind₁ (![X 0, X 0 - X 1] : Vec2 F) q)) := by
  have hb : bind₁ (![X 0 - X 1, X 0] : Vec2 F) q = C ε * bind₁ (![X 0, X 0 - X 1] : Vec2 F) q := by
    rw [← bind_bind_vec (n := 2) (![X 0, X 0 - X 1] : Vec2 F) (![X 1, X 0] : Vec2 F)
      (![X 0 - X 1, X 0] : Vec2 F) (fun i => by fin_cases i <;> simp) q, hswap, map_mul,
      bind₁_C_right]
  have ha : bind₁ (![X 0 - X 1, -X 0] : Vec2 F) q =
      -(C ε * bind₁ (![X 0 - X 1, X 0] : Vec2 F) q) := by
    rw [← bind_bind_vec (n := 2) (![X 0 - X 1, X 0] : Vec2 F) (![X 0, -X 1] : Vec2 F)
      (![X 0 - X 1, -X 0] : Vec2 F) (fun i => by fin_cases i <;> simp) q, hneg2, map_neg,
      map_mul, bind₁_C_right]
  rw [← bind_bind_vec (n := 2) (![X 0 - X 1, -X 0] : Vec2 F) (![-X 0, X 1] : Vec2 F)
    (![X 1 - X 0, -X 0] : Vec2 F) (fun i => by fin_cases i <;> simp) q, hneg1, map_neg,
    map_mul, bind₁_C_right]
  rw [ha, hb]
  ring

/-- The shifted-basis relation `q = ...` of claim 5: the two defining sums agree. -/
theorem bin_key {F : Type*} [CommRing F] {ε : F} (hε2 : C ε * C ε = (1 : MvPolynomial (Fin 2) F))
    {q : MvPolynomial (Fin 2) F}
    (hswap : bind₁ (![X 1, X 0] : Vec2 F) q = C ε * q)
    (hneg1 : bind₁ (![-X 0, X 1] : Vec2 F) q = -(C ε * q))
    (hneg2 : bind₁ (![X 0, -X 1] : Vec2 F) q = -(C ε * q)) :
    q + bind₁ (![-X 1, X 0 - X 1] : Vec2 F) q + bind₁ (![X 1 - X 0, -X 0] : Vec2 F) q =
      q - bind₁ (![X 0 - X 1, X 1] : Vec2 F) q + C ε * bind₁ (![X 0, X 0 - X 1] : Vec2 F) q := by
  rw [bin_neg_first hswap hneg1, bin_neg_second hswap hneg1 hneg2]
  linear_combination (-bind₁ (![X 0 - X 1, X 1] : Vec2 F) q +
    C ε * bind₁ (![X 0, X 0 - X 1] : Vec2 F) q) * hε2

/-- Paper: `eq:binary-addition`: the period sum relation is equivalent to
the shifted relation `q - q(X-Y,Y) + ε q(X,X-Y) = 0`. -/
theorem section2_binary_addition {F : Type*} [Field F] [CharZero F] {ε : F}
    (hε : ε = 1 ∨ ε = -1) {q : MvPolynomial (Fin 2) F}
    (hswap : bind₁ (![X 1, X 0] : Vec2 F) q = C ε * q)
    (hneg1 : bind₁ (![-X 0, X 1] : Vec2 F) q = -(C ε * q))
    (hneg2 : bind₁ (![X 0, -X 1] : Vec2 F) q = -(C ε * q)) :
    (q + bind₁ (![-X 1, X 0 - X 1] : Vec2 F) q + bind₁ (![X 1 - X 0, -X 0] : Vec2 F) q = 0) ↔
      (q - bind₁ (![X 0 - X 1, X 1] : Vec2 F) q + C ε * bind₁ (![X 0, X 0 - X 1] : Vec2 F) q =
        0) := by
  have hε2 : (C ε : MvPolynomial (Fin 2) F) * C ε = 1 := by
    rcases hε with rfl | rfl <;> simp
  rw [bin_key hε2 hswap hneg1 hneg2]

/-- The shifted composition `bind₁ ![X 0, X 0 + X 1] q` with the swap: `q(X+Y, X) = ε q(X, X+Y)`. -/
theorem bin_swap_sum {F : Type*} [CommRing F] {ε : F} {q : MvPolynomial (Fin 2) F}
    (hswap : bind₁ (![X 1, X 0] : Vec2 F) q = C ε * q) :
    bind₁ (![X 0 + X 1, X 0] : Vec2 F) q = C ε * bind₁ (![X 0, X 0 + X 1] : Vec2 F) q := by
  rw [← bind_bind_vec (n := 2) (![X 0, X 0 + X 1] : Vec2 F) (![X 1, X 0] : Vec2 F)
    (![X 0 + X 1, X 0] : Vec2 F) (fun i => by fin_cases i <;> simp) q, hswap, map_mul,
    bind₁_C_right]

/-- The lift identity `q = q(X+Y, Y) + q(X, X+Y)`. -/
theorem section2_lift_addition {F : Type*} [Field F] [CharZero F] {ε : F}
    (hε : ε = 1 ∨ ε = -1) {q : MvPolynomial (Fin 2) F}
    (hswap : bind₁ (![X 1, X 0] : Vec2 F) q = C ε * q)
    (hneg1 : bind₁ (![-X 0, X 1] : Vec2 F) q = -(C ε * q))
    (hneg2 : bind₁ (![X 0, -X 1] : Vec2 F) q = -(C ε * q))
    (hadd : q - bind₁ (![X 0 - X 1, X 1] : Vec2 F) q +
      C ε * bind₁ (![X 0, X 0 - X 1] : Vec2 F) q = 0) :
    q = bind₁ (![X 0 + X 1, X 1] : Vec2 F) q + bind₁ (![X 0, X 0 + X 1] : Vec2 F) q := by
  have hε2 : (C ε : MvPolynomial (Fin 2) F) * C ε = 1 := by
    rcases hε with rfl | rfl <;> simp
  have G1 : bind₁ (![X 0 + X 1, X 1] : Vec2 F) (bind₁ (![X 0 - X 1, X 1] : Vec2 F) q) = q := by
    rw [bind_bind_vec (n := 2) (![X 0 + X 1, X 1] : Vec2 F) (![X 0 - X 1, X 1] : Vec2 F)
      (X : Vec2 F) (fun i => by fin_cases i <;> simp) q, bind_X_id]
  have G2 : bind₁ (![X 0 + X 1, X 1] : Vec2 F) (bind₁ (![X 0, X 0 - X 1] : Vec2 F) q) =
      bind₁ (![X 0 + X 1, X 0] : Vec2 F) q := by
    rw [bind_bind_vec (n := 2) (![X 0 + X 1, X 1] : Vec2 F) (![X 0, X 0 - X 1] : Vec2 F)
      (![X 0 + X 1, X 0] : Vec2 F) (fun i => by fin_cases i <;> simp) q]
  have h1 := congrArg (bind₁ (![X 0 + X 1, X 1] : Vec2 F)) hadd
  simp only [map_add, map_sub, map_mul, map_zero, bind₁_C_right, G1, G2] at h1
  rw [bin_swap_sum hswap] at h1
  linear_combination -h1 + bind₁ (![X 0, X 0 + X 1] : Vec2 F) q * hε2


/-- Substitution composition with the outer ring allowed to differ from the inner one. -/
theorem bind_bind_gen {F : Type*} [CommSemiring F] {ρ : Type*} {n m : ℕ}
    (f : Fin n → MvPolynomial ρ F) (v : Fin m → MvPolynomial (Fin n) F)
    (w : Fin m → MvPolynomial ρ F) (h : ∀ i, bind₁ f (v i) = w i) (φ : MvPolynomial (Fin m) F) :
    bind₁ f (bind₁ v φ) = bind₁ w φ := by
  rw [bind₁_bind₁]
  have hfun : (fun i => bind₁ f (v i)) = w := funext h
  rw [hfun]

/-- The cycle identity on the binary side: the three pairs `(x,y)`, `(y,-x-y)`, `(-x-y,x)`
sum to zero, from the sign relation and the three-term relation. -/
theorem lift_cycle_identity {F : Type*} [CommRing F] {ε : F}
    (hε2 : C ε * C ε = (1 : MvPolynomial (Fin 2) F)) {q : MvPolynomial (Fin 2) F}
    (hneg1 : bind₁ (![-X 0, X 1] : Vec2 F) q = -(C ε * q))
    (T3 : q + bind₁ (![-X 1, X 0 - X 1] : Vec2 F) q + bind₁ (![X 1 - X 0, -X 0] : Vec2 F) q = 0) :
    q + bind₁ (![X 1, -X 0 - X 1] : Vec2 F) q + bind₁ (![-X 0 - X 1, X 0] : Vec2 F) q = 0 := by
  have h13 : bind₁ (![-X 0, X 1] : Vec2 F) q + bind₁ (![-X 1, -X 0 - X 1] : Vec2 F) q +
      bind₁ (![X 0 + X 1, X 0] : Vec2 F) q = 0 := by
    have T := congrArg (bind₁ (![-X 0, X 1] : Vec2 F)) T3
    rw [map_zero, map_add, map_add,
      bind_bind_vec (n := 2) (![-X 0, X 1] : Vec2 F) (![-X 1, X 0 - X 1] : Vec2 F)
        (![-X 1, -X 0 - X 1] : Vec2 F) (fun i => by fin_cases i <;> simp) q,
      bind_bind_vec (n := 2) (![-X 0, X 1] : Vec2 F) (![X 1 - X 0, -X 0] : Vec2 F)
        (![X 0 + X 1, X 0] : Vec2 F) (fun i => by fin_cases i <;> first | (simp; done) | (simp; ring)) q] at T
    exact T
  have h46 : bind₁ (![-X 1, -X 0 - X 1] : Vec2 F) q =
      -(C ε * bind₁ (![X 1, -X 0 - X 1] : Vec2 F) q) := by
    have T := congrArg (bind₁ (![X 1, -X 0 - X 1] : Vec2 F)) hneg1
    rw [map_neg, map_mul, bind₁_C_right,
      bind_bind_vec (n := 2) (![X 1, -X 0 - X 1] : Vec2 F) (![-X 0, X 1] : Vec2 F)
        (![-X 1, -X 0 - X 1] : Vec2 F) (fun i => by fin_cases i <;> simp) q] at T
    exact T
  have h51 : bind₁ (![X 0 + X 1, X 0] : Vec2 F) q =
      -(C ε * bind₁ (![-X 0 - X 1, X 0] : Vec2 F) q) := by
    have T := congrArg (bind₁ (![-X 0 - X 1, X 0] : Vec2 F)) hneg1
    rw [map_neg, map_mul, bind₁_C_right,
      bind_bind_vec (n := 2) (![-X 0 - X 1, X 0] : Vec2 F) (![-X 0, X 1] : Vec2 F)
        (![X 0 + X 1, X 0] : Vec2 F) (fun i => by fin_cases i <;> first | (simp; done) | (simp; ring)) q] at T
    exact T
  linear_combination (C ε) * hneg1 - (C ε) * h13 + (C ε) * h46 + (C ε) * h51 -
    (q + bind₁ (![X 1, -X 0 - X 1] : Vec2 F) q + bind₁ (![-X 0 - X 1, X 0] : Vec2 F) q) * hε2

/-- The cyclic lift `Φ q` vanishes on the plane `z = -x-y`. -/
theorem section2_lift_vanishes {F : Type*} [Field F] [CharZero F] {ε : F}
    (hε : ε = 1 ∨ ε = -1) {q : MvPolynomial (Fin 2) F}
    (hswap : bind₁ (![X 1, X 0] : Vec2 F) q = C ε * q)
    (hneg1 : bind₁ (![-X 0, X 1] : Vec2 F) q = -(C ε * q))
    (hneg2 : bind₁ (![X 0, -X 1] : Vec2 F) q = -(C ε * q))
    (hadd : q - bind₁ (![X 0 - X 1, X 1] : Vec2 F) q +
      C ε * bind₁ (![X 0, X 0 - X 1] : Vec2 F) q = 0) :
    bind₁ (![X 0, X 1, -X 0 - X 1] : Vec3 F) (cyclicLift q) = 0 := by
  have hε2 : (C ε : MvPolynomial (Fin 2) F) * C ε = 1 := by
    rcases hε with rfl | rfl <;> simp
  have T3 := (section2_binary_addition hε hswap hneg1 hneg2).mpr hadd
  have key := lift_cycle_identity hε2 hneg1 T3
  have hmap := congrArg (bind₁ (![X 0, X 1] : Fin 2 → MvPolynomial (Fin 3) F)) key
  rw [map_zero, map_add, map_add,
    bind_bind_gen (![X 0, X 1] : Fin 2 → MvPolynomial (Fin 3) F) (![X 1, -X 0 - X 1] : Vec2 F)
      (![X 1, -X 0 - X 1] : Fin 2 → MvPolynomial (Fin 3) F)
      (fun i => by fin_cases i <;> simp) q,
    bind_bind_gen (![X 0, X 1] : Fin 2 → MvPolynomial (Fin 3) F) (![-X 0 - X 1, X 0] : Vec2 F)
      (![-X 0 - X 1, X 0] : Fin 2 → MvPolynomial (Fin 3) F)
      (fun i => by fin_cases i <;> simp) q] at hmap
  rw [bind_cyclicLift]
  simp only [binaryEval]
  linear_combination hmap

/-- The substitution `z ↦ -x-y` has kernel generated by `x+y+z`, one-variable induction. -/
theorem section2_sub_dvd {F : Type*} [CommRing F] (G : MvPolynomial (Fin 3) F) :
    (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) F) ∣
      G - bind₁ (![X 0, X 1, -X 0 - X 1] : Vec3 F) G := by
  refine MvPolynomial.induction_on (motive := fun G : MvPolynomial (Fin 3) F =>
    (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) F) ∣
      G - bind₁ (![X 0, X 1, -X 0 - X 1] : Vec3 F) G) G ?_ ?_ ?_
  · intro a
    simp
  · intro p r hp hr
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hr
  · intro p n hp
    have hX : (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) F) ∣
        X n - bind₁ (![X 0, X 1, -X 0 - X 1] : Vec3 F) (X n) := by
      fin_cases n
      · simp
      · simp
      · exact ⟨1, by simp; ring⟩
    have e : p * X n - bind₁ (![X 0, X 1, -X 0 - X 1] : Vec3 F) (p * X n) =
        (p - bind₁ (![X 0, X 1, -X 0 - X 1] : Vec3 F) p) * X n +
          bind₁ (![X 0, X 1, -X 0 - X 1] : Vec3 F) p *
            (X n - bind₁ (![X 0, X 1, -X 0 - X 1] : Vec3 F) (X n)) := by
      rw [map_mul]
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hX _)

/-- The cyclic lift is divisible by `x+y+z`. -/
theorem section2_lift_divisible {F : Type*} [Field F] [CharZero F] {ε : F}
    (hε : ε = 1 ∨ ε = -1) {q : MvPolynomial (Fin 2) F}
    (hswap : bind₁ (![X 1, X 0] : Vec2 F) q = C ε * q)
    (hneg1 : bind₁ (![-X 0, X 1] : Vec2 F) q = -(C ε * q))
    (hneg2 : bind₁ (![X 0, -X 1] : Vec2 F) q = -(C ε * q))
    (hadd : q - bind₁ (![X 0 - X 1, X 1] : Vec2 F) q +
      C ε * bind₁ (![X 0, X 0 - X 1] : Vec2 F) q = 0) :
    (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) F) ∣ cyclicLift q := by
  have hv := section2_lift_vanishes hε hswap hneg1 hneg2 hadd
  have h := section2_sub_dvd (cyclicLift q)
  rw [hv, sub_zero] at h
  exact h


/-- Product over the support of a monomial exponent, written with two variables. -/
theorem prod_pair_support {F : Type*} [CommRing F] (g : Fin 2 → MvPolynomial (Fin 2) F)
    (e : Fin 2 →₀ ℕ) :
    (∏ i ∈ e.support, g i ^ e i) = g 0 ^ e 0 * g 1 ^ e 1 := by
  have h := Finsupp.prod_fintype e (fun i k => g i ^ k) (fun i => pow_zero _)
  rw [Fin.prod_univ_two] at h
  exact h

/-- Axis lemma: for a homogeneous binary form of degree `n`, substituting `(u, 0)` gives
`q(1,0) u^n`. -/
theorem bind_axis0_homog {F : Type*} [CommRing F] {n : ℕ} {q : MvPolynomial (Fin 2) F}
    (hq : q.IsHomogeneous n) (u : MvPolynomial (Fin 2) F) :
    bind₁ (![u, 0] : Fin 2 → MvPolynomial (Fin 2) F) q = C (eval ![1, 0] q) * u ^ n := by
  have hsum : ∀ e ∈ q.support, e 0 + e 1 = n := by
    intro e he
    have h := hq.degree_eq_sum_deg_support he
    rw [h, ← Fin.sum_univ_two]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)).symm
  have hterm : ∀ e ∈ q.support,
      bind₁ (![u, 0] : Fin 2 → MvPolynomial (Fin 2) F) (monomial e (q.coeff e)) =
        C (if e 1 = 0 then q.coeff e else 0) * u ^ n := by
    intro e he
    have hs := hsum e he
    rw [bind₁_monomial, prod_pair_support]
    by_cases h1 : e 1 = 0
    · have h0 : e 0 = n := by omega
      simp [h1, h0]
    · simp [h1, zero_pow h1]
  have hL : bind₁ (![u, 0] : Fin 2 → MvPolynomial (Fin 2) F) q =
      (∑ e ∈ q.support, C (if e 1 = 0 then q.coeff e else 0)) * u ^ n := by
    conv_lhs => rw [as_sum q]
    rw [map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl hterm
  have hR : eval (![1, 0] : Fin 2 → F) q = ∑ e ∈ q.support, (if e 1 = 0 then q.coeff e else 0) := by
    conv_lhs => rw [as_sum q]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [eval_monomial, Finsupp.prod_fintype e (fun i k => (![1, 0] : Fin 2 → F) i ^ k)
      (fun i => pow_zero _), Fin.prod_univ_two]
    by_cases h1 : e 1 = 0
    · simp [h1]
    · simp [h1, zero_pow h1]
  rw [hL, hR, map_sum]

/-- Axis lemma: for a homogeneous binary form of degree `n`, substituting `(0, u)` gives
`q(0,1) u^n`. -/
theorem bind_axis1_homog {F : Type*} [CommRing F] {n : ℕ} {q : MvPolynomial (Fin 2) F}
    (hq : q.IsHomogeneous n) (u : MvPolynomial (Fin 2) F) :
    bind₁ (![0, u] : Fin 2 → MvPolynomial (Fin 2) F) q = C (eval ![0, 1] q) * u ^ n := by
  have hsum : ∀ e ∈ q.support, e 0 + e 1 = n := by
    intro e he
    have h := hq.degree_eq_sum_deg_support he
    rw [h, ← Fin.sum_univ_two]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)).symm
  have hterm : ∀ e ∈ q.support,
      bind₁ (![0, u] : Fin 2 → MvPolynomial (Fin 2) F) (monomial e (q.coeff e)) =
        C (if e 0 = 0 then q.coeff e else 0) * u ^ n := by
    intro e he
    have hs := hsum e he
    rw [bind₁_monomial, prod_pair_support]
    by_cases h0 : e 0 = 0
    · have h1 : e 1 = n := by omega
      simp [h0, h1]
    · simp [h0, zero_pow h0]
  have hL : bind₁ (![0, u] : Fin 2 → MvPolynomial (Fin 2) F) q =
      (∑ e ∈ q.support, C (if e 0 = 0 then q.coeff e else 0)) * u ^ n := by
    conv_lhs => rw [as_sum q]
    rw [map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl hterm
  have hR : eval (![0, 1] : Fin 2 → F) q = ∑ e ∈ q.support, (if e 0 = 0 then q.coeff e else 0) := by
    conv_lhs => rw [as_sum q]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [eval_monomial, Finsupp.prod_fintype e (fun i k => (![0, 1] : Fin 2 → F) i ^ k)
      (fun i => pow_zero _), Fin.prod_univ_two]
    by_cases h0 : e 0 = 0
    · simp [h0]
    · simp [h0, zero_pow h0]
  rw [hL, hR, map_sum]

/-- Paper: `b5`: a homogeneous binary form of even degree `n` satisfying the
two-term and three-term relations, after subtracting its axis part `c (X^n - Y^n)`, satisfies
the full normalized period relations. -/
theorem section2_b5 {F : Type*} [Field F] {n : ℕ} (hn : 0 < n) (heven : Even n)
    {q : MvPolynomial (Fin 2) F} (hq : q.IsHomogeneous n)
    (h1 : q + bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) F) q = 0)
    (h2 : q + bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) F) q +
      bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) F) q = 0) :
    TernaryPoly.Paper.PeriodRelations
      (q - C (eval ![1, 0] q) * (X 0 ^ n - X 1 ^ n)) := by
  have hn' : n ≠ 0 := by omega
  -- the axis values are opposite: evaluate `h1` at `x = 0`
  have hcd : eval (![1, 0] : Fin 2 → F) q + eval (![0, 1] : Fin 2 → F) q = 0 := by
    have T := congrArg (bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) F)) h1
    rw [map_zero, map_add, bind_axis1_homog hq (X 1),
      bind_bind_vec (n := 2) (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) F)
        (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) F)
        (![-X 1, 0] : Fin 2 → MvPolynomial (Fin 2) F)
        (fun i => by fin_cases i <;> simp) q,
      bind_axis0_homog hq (-X 1), Even.neg_pow heven] at T
    have hm : (C (eval (![1, 0] : Fin 2 → F) q + eval (![0, 1] : Fin 2 → F) q) :
        MvPolynomial (Fin 2) F) * (X 1 : MvPolynomial (Fin 2) F) ^ n = 0 := by
      rw [map_add]
      linear_combination T
    rcases mul_eq_zero.mp hm with h | h
    · exact C_eq_zero.mp h
    · exact absurd h (pow_ne_zero _ (X_ne_zero 1))
  have hd : eval (![0, 1] : Fin 2 → F) q = -eval (![1, 0] : Fin 2 → F) q := by
    linear_combination hcd
  -- the basic polynomial `P = X^n - Y^n` and its transforms
  have hz : bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) F) (X 0 ^ n - X 1 ^ n) =
      -(X 1 ^ n) := by
    simp [zero_pow hn']
  have hz2 : bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) F) (X 0 ^ n - X 1 ^ n) = X 0 ^ n := by
    simp [zero_pow hn']
  have hP3 : bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) F) (X 0 ^ n - X 1 ^ n) =
      -(X 0 ^ n - X 1 ^ n) := by
    have e1 : bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) F) (X 0) = -X 1 := by simp
    have e2 : bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) F) (X 1) = X 0 := by simp
    rw [map_sub, map_pow, map_pow, e1, e2, Even.neg_pow heven]
    ring
  have hPsum : (X 0 ^ n - X 1 ^ n) +
      bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) F) (X 0 ^ n - X 1 ^ n) +
      bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) F) (X 0 ^ n - X 1 ^ n) = 0 := by
    have ha : bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) F) (X 0 ^ n - X 1 ^ n) =
        X 1 ^ n - (X 0 - X 1) ^ n := by
      have e1 : bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) F) (X 0) = -X 1 := by
        simp
      have e2 : bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) F) (X 1) =
          X 0 - X 1 := by simp
      rw [map_sub, map_pow, map_pow, e1, e2, Even.neg_pow heven]
    have hb : bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) F) (X 0 ^ n - X 1 ^ n) =
        (X 0 - X 1) ^ n - X 0 ^ n := by
      have e1 : bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) F) (X 0) =
          X 1 - X 0 := by simp
      have e2 : bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) F) (X 1) = -X 0 := by
        simp
      have e3 : (X 1 - X 0 : MvPolynomial (Fin 2) F) = -(X 0 - X 1) := by ring
      rw [map_sub, map_pow, map_pow, e1, e2, e3, Even.neg_pow heven, Even.neg_pow heven]
    rw [ha, hb]
    ring
  unfold TernaryPoly.Paper.PeriodRelations
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) F)
        (q - C (eval (![1, 0] : Fin 2 → F) q) * (X 0 ^ n - X 1 ^ n)) =
        bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) F) q -
          C (eval (![1, 0] : Fin 2 → F) q) *
            bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) F) (X 0 ^ n - X 1 ^ n) := by
      rw [map_sub, map_mul, bind₁_C_right]
    rw [e, hz, bind_axis1_homog hq (X 1), hd, map_neg]
    ring
  · have e : bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) F)
        (q - C (eval (![1, 0] : Fin 2 → F) q) * (X 0 ^ n - X 1 ^ n)) =
        bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) F) q -
          C (eval (![1, 0] : Fin 2 → F) q) *
            bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) F) (X 0 ^ n - X 1 ^ n) := by
      rw [map_sub, map_mul, bind₁_C_right]
    rw [e, hz2, bind_axis0_homog hq (X 0)]
    ring
  · have e : bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) F)
        (q - C (eval (![1, 0] : Fin 2 → F) q) * (X 0 ^ n - X 1 ^ n)) =
        bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) F) q -
          C (eval (![1, 0] : Fin 2 → F) q) *
            bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) F) (X 0 ^ n - X 1 ^ n) := by
      rw [map_sub, map_mul, bind₁_C_right]
    rw [e, hP3]
    linear_combination h1
  · have e2 : bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) F)
        (q - C (eval (![1, 0] : Fin 2 → F) q) * (X 0 ^ n - X 1 ^ n)) =
        bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) F) q -
          C (eval (![1, 0] : Fin 2 → F) q) *
            bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) F) (X 0 ^ n - X 1 ^ n) := by
      rw [map_sub, map_mul, bind₁_C_right]
    have e3 : bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) F)
        (q - C (eval (![1, 0] : Fin 2 → F) q) * (X 0 ^ n - X 1 ^ n)) =
        bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) F) q -
          C (eval (![1, 0] : Fin 2 → F) q) *
            bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) F) (X 0 ^ n - X 1 ^ n) := by
      rw [map_sub, map_mul, bind₁_C_right]
    rw [e2, e3]
    linear_combination h2 - C (eval (![1, 0] : Fin 2 → F) q) * hPsum

end TernaryPeriodPolynomials.Argument.Statements.Section2Claims
