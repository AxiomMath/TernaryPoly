module

public import TernaryPeriodPolynomials.PeriodPolynomial.CoefficientRing.Substitution
public import TernaryPeriodPolynomials.PeriodPolynomial.CoefficientRing.PasolPopaMatrix

@[expose] public section


/-!
# Section 6-7 unnumbered polynomial claims

Formalized by Claude Haiku 5.5.

Standalone statements and proofs for the displayed polynomial identities of Sections 6-7 of
the paper. Each theorem
docstring cites the paper label or line carrying the claim. Helpers live in
`TernaryPeriodPolynomials.Argument.Section67Claims.Substitution`.

Conventions: `PeriodRelations q` is the normalized binary period space of the paper
(`TernaryPoly.Paper`). The involution is `S q = q(-X,Y)`; the order-three substitution is
`T q = q(-Y,X-Y)`. The literal Pasol-Popa matrix `U = [[1,-1],[1,0]]` and its action are in
`TernaryPeriodPolynomials.Argument.Section67Claims.PasolPopaMatrix`; the exports
`printed_pasol_popa_cube`, `printed_U_sq_substitution` and `printed_three_term_norms_agree` state
the printed claim of the paper about that matrix.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.Statements.Section67Claims

open TernaryPeriodPolynomials.Argument.Section67Claims
open TernaryPoly.Paper

variable {F : Type*} [CommRing F]

/-! ### Lemma 7.1: the six-term expansion behind `eq:alternating-additivity` -/

/-- For an alternating binary polynomial `q`,
the three-term norm of its cyclic lift is the restriction-to-`z=0` norm `N_2 q(x,y)` plus the six
displayed terms in `z`. -/
theorem norm_cyclicLift_expansion (q : MvPolynomial (Fin 2) F) (hq : bind₁ ![X 1, X 0] q = -q) :
    threeTermNorm (cyclicLift q) =
      ((bind₁ ![X 0, X 1] q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q
        : MvPolynomial (Fin 3) F) +
      (bind₁ ![X 1, X 2] q - bind₁ ![X 0, X 2] q + bind₁ ![X 0 - X 1, X 2] q
        - bind₁ ![-X 1, X 2] q + bind₁ ![-X 0, X 2] q - bind₁ ![X 1 - X 0, X 2] q)
        : MvPolynomial (Fin 3) F) := by
  have h1 := alt_subst q hq (X 0 : MvPolynomial (Fin 3) F) (X 2)
  have h2 := alt_subst q hq (-X 1 : MvPolynomial (Fin 3) F) (X 2)
  have h3 := alt_subst q hq (X 1 - X 0 : MvPolynomial (Fin 3) F) (X 2)
  unfold threeTermNorm
  rw [bind_cyclicLift, bind_cyclicLift]
  simp only [cyclicLift, binaryEval]
  linear_combination h1 + h2 + h3

/-- If `q` is alternating, its cyclic
lift is a solution (`N Φ(q) = 0`), and `N_2 q = 0`, then the six-term sum vanishes. Here
`x,y,z` are `X 0, X 1, X 2`. -/
theorem alternating_additivity (q : MvPolynomial (Fin 2) F) (hq : bind₁ ![X 1, X 0] q = -q)
    (hN : threeTermNorm (cyclicLift q) = 0)
    (hN2 : (bind₁ ![X 0, X 1] q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q
      : MvPolynomial (Fin 3) F) = 0) :
    ((bind₁ ![X 1, X 2] q - bind₁ ![-X 1, X 2] q)
      - (bind₁ ![X 0, X 2] q - bind₁ ![-X 0, X 2] q)
      + (bind₁ ![X 0 - X 1, X 2] q - bind₁ ![X 1 - X 0, X 2] q) : MvPolynomial (Fin 3) F) = 0 := by
  have key := norm_cyclicLift_expansion q hq
  linear_combination hN - key - hN2

/-! ### Corollary 1.5: `eq:sharp-divisor-factorization` -/

/-- The alternating degree-ten
solution `f_a = Φ(q_a)` factors as `D (x-y)(x-z)(y-z)(x-y-z)(x-y+z)(x+y-z)` with
`D = (x+y+z)(x+y)(y+z)(z+x)`. Over any commutative ring. -/
theorem sharp_divisor_factorization (R : Type*) [CommRing R] :
    alternatingTenSolution R =
      universalDivisor R * (X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)
        * (X 0 - X 1 - X 2) * (X 0 - X 1 + X 2) * (X 0 + X 1 - X 2) := by
  simp only [alternatingTenSolution, universalDivisor, cyclicLift, binaryEval, alternatingTenPeriod]
  simp
  ring

/-! ### Symmetric restriction identities -/

/-- The symmetric period `q_s` has `q_s(X 0, X 0) = 0`. -/
theorem symmetricTenPeriod_diagonal (R : Type*) [CommRing R] :
    (bind₁ ![X 0, X 0] (symmetricTenPeriod R) : MvPolynomial (Fin 2) R) = 0 := by
  simp [symmetricTenPeriod]

/-- The symmetric period `q_s` is symmetric: `q_s(X 1, X 0) = q_s(X 0, X 1)`. -/
theorem symmetricTenPeriod_swap (R : Type*) [CommRing R] :
    bind₁ ![X 1, X 0] (symmetricTenPeriod R) = symmetricTenPeriod R := by
  simp [symmetricTenPeriod, bind_ofNat_four]
  ring

/-- With `u = X 0`, `v = X 1`. -/
theorem symmetric_restriction_diagonal (R : Type*) [CommRing R] :
    bind₁ ![X 0, X 0, X 1] (symmetricTenSolution R) = 2 * symmetricTenPeriod R := by
  unfold symmetricTenSolution
  rw [bind_cyclicLift]
  simp only [binaryEval]
  rw [symmetricTenPeriod_diagonal R, bind_id_pair (symmetricTenPeriod R),
    symmetricTenPeriod_swap R]
  ring

/-- With `u = X 0`, `v = X 1`. -/
theorem symmetric_restriction_shift (R : Type*) [CommRing R] :
    bind₁ ![X 0 + X 1, X 0, X 1] (symmetricTenSolution R) = 2 * symmetricTenPeriod R := by
  unfold symmetricTenSolution
  rw [bind_cyclicLift]
  simp only [binaryEval]
  simp [symmetricTenPeriod, bind_ofNat_four]
  ring

/-! ### Corollary 1.3: the parity-projection claims -/

open TernaryPeriodPolynomials.Argument.Section67Claims.PasolPopa in
/-- The matrix claim: the Pasol-Popa matrix `U = TS = [[1,-1],[1,0]]`
satisfies `U^3 = -I` as an integer matrix identity. -/
theorem printed_pasol_popa_cube : PPU ^ 3 = -1 := PPU_cube

open TernaryPeriodPolynomials.Argument.Section67Claims.PasolPopa in
/-- The substitution action of `U^2` is `(X,Y) ↦ (-Y, X-Y)`. -/
theorem printed_U_sq_substitution (q : MvPolynomial (Fin 2) F) :
    act (PPU ^ 2) q = bind₁ ![-X 1, X 0 - X 1] q :=
  act_PPU_sq q

open TernaryPeriodPolynomials.Argument.Section67Claims.PasolPopa in
/-- For even degree `n`, `-I` acts trivially and the printed three-term
norm agrees with the Pasol-Popa norm `q + q|U + q|U^2`. -/
theorem printed_three_term_norms_agree {n : ℕ} (hn : Even n) {q : MvPolynomial (Fin 2) F}
    (hq : q.IsHomogeneous n) :
    q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q =
      q + act PPU q + act (PPU ^ 2) q :=
  printed_three_term_eq_pp_norm hn hq

/-- The order-three substitution `T q = q(-Y, X-Y)` satisfies `T^3 q = q` for every binary form.
This is NOT the printed claim of the paper: the printed claim is the matrix identity `U^3 = -I`
for the Pasol-Popa matrix, exported as `printed_pasol_popa_cube`, and the even-degree agreement of
the norms, exported as `printed_three_term_norms_agree`. -/
theorem substitution_order_three (q : MvPolynomial (Fin 2) F) :
    bind₁ ![-X 1, X 0 - X 1] (bind₁ ![-X 1, X 0 - X 1] (bind₁ ![-X 1, X 0 - X 1] q)) = q :=
  bind_T_cube q

/-- The involution `q(X,Y) ↦ q(-X,Y)` maps normalized binary period
polynomials to normalized binary period polynomials (axis conditions and both period relations). -/
theorem involution_preserves_periodRelations (q : MvPolynomial (Fin 2) F)
    (hq : PeriodRelations q) : PeriodRelations (bind₁ ![-X 0, X 1] q) := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bind_involution, neg_zero]
    exact h1
  · rw [bind_involution]
    have e2 : (bind₁ ![X 0, 0] (bind₁ ![-X 0, -X 1] q) : MvPolynomial (Fin 2) F)
        = bind₁ ![-X 0, 0] q :=
      bind_bind_vec _ _ _ (fun i => by fin_cases i <;> simp) q
    exact e2.symm.trans ((congrArg (bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) F))
      (even_of_two_term q h3)).trans h2)
  · have e : (bind₁ ![-X 1, X 0] (bind₁ ![-X 0, X 1] q) : MvPolynomial (Fin 2) F)
        = bind₁ ![X 1, X 0] q := by
      rw [bind_involution, neg_neg]
    rw [e]
    linear_combination two_term_inst q h3 (X 1) (X 0)
  · have e1 : (bind₁ ![-X 1, X 0 - X 1] (bind₁ ![-X 0, X 1] q) : MvPolynomial (Fin 2) F)
        = bind₁ ![X 1, X 0 - X 1] q := by
      rw [bind_involution, neg_neg]
    have e2 : (bind₁ ![X 1 - X 0, -X 0] (bind₁ ![-X 0, X 1] q) : MvPolynomial (Fin 2) F)
        = bind₁ ![X 0 - X 1, -X 0] q := by
      rw [bind_involution, neg_sub]
    rw [e1, e2]
    have R2a := two_term_inst q h3 (X 1) (X 0 - X 1)
    have R2b := two_term_inst q h3 (-X 0) (X 1)
    have R2c := two_term_inst q h3 (X 0 - X 1) (-X 0)
    have R3 := three_term_inst q h4 (X 0) (X 0 - X 1)
    simp only [neg_sub, neg_neg, sub_sub_cancel, sub_sub_cancel_left] at R2a R2c R3
    linear_combination R2a + R2b + R2c - R3

/-- Both parity combinations `q ± q(-X,Y)` satisfy the normalized binary
period conditions. The scalar `(2)⁻¹` of the projection is the one in a field of characteristic
not two. -/
theorem parity_projections_periodRelations {K : Type*} [Field K] (q : MvPolynomial (Fin 2) K)
    (hq : PeriodRelations q) :
    PeriodRelations ((2 : K)⁻¹ • (q + bind₁ ![-X 0, X 1] q)) ∧
      PeriodRelations ((2 : K)⁻¹ • (q - bind₁ ![-X 0, X 1] q)) := by
  have hS := involution_preserves_periodRelations q hq
  obtain ⟨a1, a2, a3, a4⟩ := hq
  obtain ⟨b1, b2, b3, b4⟩ := hS
  have smul : ∀ (c : K) (p : MvPolynomial (Fin 2) K), PeriodRelations p →
      PeriodRelations (c • p) := by
    intro c p hp
    obtain ⟨p1, p2, p3, p4⟩ := hp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [map_smul, p1, smul_zero]
    · rw [map_smul, p2, smul_zero]
    · simp only [map_smul]
      rw [← smul_add, p3, smul_zero]
    · simp only [map_smul]
      rw [← smul_add, ← smul_add, p4, smul_zero]
  refine ⟨smul _ _ ⟨?_, ?_, ?_, ?_⟩, smul _ _ ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [map_add, a1, b1, zero_add]
  · rw [map_add, a2, b2, zero_add]
  · simp only [map_add]; linear_combination a3 + b3
  · simp only [map_add]; linear_combination a4 + b4
  · rw [map_sub, a1, b1, sub_zero]
  · rw [map_sub, a2, b2, sub_zero]
  · simp only [map_sub]; linear_combination a3 - b3
  · simp only [map_sub]; linear_combination a4 - b4

/-! ### Corollary 1.4: `eq:even-period-normalization` -/

/-- For even `n`, the normalizing polynomial `X^n - Y^n` satisfies both
period relations (two-term and three-term). -/
theorem even_power_difference_relations (n : ℕ) (hn : Even n) :
    ((X 0 ^ n - X 1 ^ n : MvPolynomial (Fin 2) F)
        + bind₁ ![-X 1, X 0] (X 0 ^ n - X 1 ^ n) = 0) ∧
      ((X 0 ^ n - X 1 ^ n : MvPolynomial (Fin 2) F)
        + bind₁ ![-X 1, X 0 - X 1] (X 0 ^ n - X 1 ^ n)
        + bind₁ ![X 1 - X 0, -X 0] (X 0 ^ n - X 1 ^ n) = 0) := by
  have e1 : ((-X 1 : MvPolynomial (Fin 2) F) ^ n) = X 1 ^ n := hn.neg_pow _
  have e0 : ((-X 0 : MvPolynomial (Fin 2) F) ^ n) = X 0 ^ n := hn.neg_pow _
  have e3 : ((X 1 - X 0 : MvPolynomial (Fin 2) F) ^ n) = (X 0 - X 1) ^ n := by
    rw [← neg_sub, hn.neg_pow]
  constructor
  · simp only [map_sub, map_pow, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination e1
  · simp only [map_sub, map_pow, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination e1 - e0 + e3

/-- Subtracting
`c (X^n - Y^n)` from a polynomial satisfying both period relations keeps both relations, for even
`n`. -/
theorem even_normalization_preserves_relations (n : ℕ) (hn : Even n) (r : MvPolynomial (Fin 2) F)
    (c : F) (h2 : r + bind₁ ![-X 1, X 0] r = 0)
    (h3 : r + bind₁ ![-X 1, X 0 - X 1] r + bind₁ ![X 1 - X 0, -X 0] r = 0) :
    ((r - C c * (X 0 ^ n - X 1 ^ n : MvPolynomial (Fin 2) F))
        + bind₁ ![-X 1, X 0] (r - C c * (X 0 ^ n - X 1 ^ n)) = 0) ∧
      ((r - C c * (X 0 ^ n - X 1 ^ n : MvPolynomial (Fin 2) F))
        + bind₁ ![-X 1, X 0 - X 1] (r - C c * (X 0 ^ n - X 1 ^ n))
        + bind₁ ![X 1 - X 0, -X 0] (r - C c * (X 0 ^ n - X 1 ^ n)) = 0) := by
  obtain ⟨p2, p3⟩ := even_power_difference_relations (F := F) n hn
  set D : MvPolynomial (Fin 2) F := X 0 ^ n - X 1 ^ n with hD
  constructor
  · simp only [map_sub, map_mul, bind₁_C_right]
    linear_combination h2 - C c * p2
  · simp only [map_sub, map_mul, bind₁_C_right]
    linear_combination h3 - C c * p3

/-! ### Corollary 1.4: the binomial core of `eq:period-critical-coefficients` -/

/-- Algebraic core of `eq:period-critical-coefficients`: the binomial expansion of
`(c Y - X)^n` in `X^{n-j} Y^j`, with coefficient `binom(n,j) (-1)^{n-j} c^j`. The Mellin
normalization and the integration along `τ = iy` are analytic and are not formalized here. -/
theorem period_integrand_expansion (c : F) (n : ℕ) :
    (C c * X 1 - X 0 : MvPolynomial (Fin 2) F) ^ n =
      ∑ j ∈ Finset.range (n + 1),
        C ((n.choose j : F) * (-1) ^ (n - j) * c ^ j) * X 0 ^ (n - j) * X 1 ^ j := by
  rw [sub_eq_add_neg, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, neg_pow]
  simp only [map_mul, map_pow, map_natCast, map_neg, map_one]
  ring

end TernaryPeriodPolynomials.Argument.Statements.Section67Claims
