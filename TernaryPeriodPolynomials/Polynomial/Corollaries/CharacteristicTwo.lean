module

public import TernaryPeriodPolynomials.Polynomial.Defs

@[expose] public section


/-! Proof pieces for the characteristic-two counterexample (Section 7.4). Feeds
`TernaryPeriodPolynomials.characteristic_two_counterexample`. -/


open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument

/-- Even numerals vanish in any `MvPolynomial` ring over `ZMod 2`; `ring` alone does not know
this, since it only proves identities valid in every commutative ring. -/
private theorem charTwo_two_eq_zero {σ : Type*} : (2 : MvPolynomial σ (ZMod 2)) = 0 := by
  rw [← map_ofNat (MvPolynomial.C (σ := σ)) 2, show (2 : ZMod 2) = 0 from by decide, map_zero]

/-- Clause 1: the universal divisor over `ZMod 2` is the cyclic lift of `X³Y+XY³`. -/
theorem charTwo_universalDivisor_eq :
    universalDivisor (ZMod 2) =
      cyclicLift (X 0 ^ 3 * X 1 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 2) (ZMod 2)) := by
  simp only [universalDivisor, cyclicLift, binaryEval, map_add, map_mul, map_pow,
    bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination
    (X 0 ^ 2 * X 1 ^ 2 + X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 2 * X 2 ^ 2 +
      2 * X 0 ^ 2 * X 1 * X 2 + 2 * X 0 * X 1 ^ 2 * X 2 + 2 * X 0 * X 1 * X 2 ^ 2) *
      charTwo_two_eq_zero

/-- The binary period `q₂ := X³Y+XY³` satisfies all four period relations over `ZMod 2`.

The `ring1` alternative must come before the `linear_combination` fallback: bare `ring`,
when it cannot close a goal, does not fail catchably inside `first` (it only emits an info
suggestion and leaves the normalized goal open), so `first | ring | ...` never reaches its
second branch. `ring1` fails properly and lets `first` fall through as intended. -/
theorem charTwo_periodRelations :
    PeriodRelations (X 0 ^ 3 * X 1 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 2) (ZMod 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [map_add, map_mul, map_pow, bind₁_X_right, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      first
        | ring1
        | linear_combination
            (X 0 ^ 4 + X 1 ^ 4 + 3 * X 0 ^ 2 * X 1 ^ 2 - 2 * X 0 ^ 3 * X 1 -
              2 * X 0 * X 1 ^ 3) * charTwo_two_eq_zero

/-- Clause 2: the universal divisor over `ZMod 2` is a `Solution`. -/
theorem charTwo_solution_universalDivisor : Solution (universalDivisor (ZMod 2)) := by
  rw [charTwo_universalDivisor_eq]
  exact cyclicLift_solution charTwo_periodRelations

/-- Clause 3: `X₀X₁X₂ · universalDivisor(ZMod 2)` is the product of all nonzero linear forms
over `ZMod 2` in three variables (there are `2³ - 1 = 7` of them, enumerated explicitly). -/
theorem charTwo_nonzeroProduct_eq :
    X 0 * X 1 * X 2 * universalDivisor (ZMod 2) = nonzeroLinearFormProduct 2 (ZMod 2) := by
  simp only [nonzeroLinearFormProduct, universalDivisor]
  rw [show (Finset.univ.filter fun v : Fin 3 → ZMod 2 => v ≠ 0) =
      ({![1,0,0], ![0,1,0], ![0,0,1], ![1,1,0], ![1,0,1], ![0,1,1], ![1,1,1]} :
        Finset (Fin 3 → ZMod 2)) from by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp [Fin.sum_univ_three, ZMod.castHom_self, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Clause 4: `X₀X₁X₂ · universalDivisor(ZMod 2)²` is a `Solution`.

Writing `D := universalDivisor (ZMod 2)`, `E := (X0+X1+X2)(X1+X2)(X2+X0)` (three of its four
factors), the two `Solution`-defining substitutions act on `D` as `A D = X0*E` and `A² D = X1*E`
up to a char-2 correction each (`hA`, `hA2`), while `D = (X0+X1)*E` exactly (`hD`, pure `ring1`,
just the associativity of `D`'s own definition). Substituting all three collapses the norm
identity to one clean, exactly-`ring1`-provable bracket identity
`L(X0+X1)² + (AL)X0² + (A²L)X1² = 4X0²X1²X2` (where `L := X0X1X2`), closed by a single final
char-2 cancellation since `4 = 2·2`. -/
theorem charTwo_solution_nonzeroProduct :
    Solution (X 0 * X 1 * X 2 * universalDivisor (ZMod 2) ^ 2) := by
  constructor
  · simp only [map_mul, map_pow, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [charTwo_solution_universalDivisor.cyclic]
    ring
  · have hA : bind₁ (![-X 1, X 0 - X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) (ZMod 2))
        (universalDivisor (ZMod 2))
        = X 0 * ((X 0 + X 1 + X 2) * (X 1 + X 2) * (X 2 + X 0)) := by
      simp only [universalDivisor, map_add, map_mul, bind₁_X_right, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      linear_combination
        (-5 * X 0 * X 1 * X 2 ^ 2 - 5 * X 0 ^ 2 * X 1 * X 2 - X 0 ^ 3 * X 1 - X 1 * X 2 ^ 3 +
          7 * X 0 * X 1 ^ 2 * X 2 + 2 * X 0 ^ 2 * X 1 ^ 2 + 4 * X 1 ^ 2 * X 2 ^ 2 -
          4 * X 0 * X 1 ^ 3 - 5 * X 1 ^ 3 * X 2 + 2 * X 1 ^ 4) * charTwo_two_eq_zero
    have hA2 : bind₁ (![X 1 - X 0, -X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) (ZMod 2))
        (universalDivisor (ZMod 2))
        = X 1 * ((X 0 + X 1 + X 2) * (X 1 + X 2) * (X 2 + X 0)) := by
      simp only [universalDivisor, map_add, map_mul, bind₁_X_right, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      linear_combination
        (-5 * X 0 * X 1 * X 2 ^ 2 + 7 * X 0 ^ 2 * X 1 * X 2 - 4 * X 0 ^ 3 * X 1 -
          5 * X 0 * X 1 ^ 2 * X 2 + 2 * X 0 ^ 2 * X 1 ^ 2 - X 0 * X 1 ^ 3 - X 0 * X 2 ^ 3 +
          4 * X 0 ^ 2 * X 2 ^ 2 - 5 * X 0 ^ 3 * X 2 + 2 * X 0 ^ 4) * charTwo_two_eq_zero
    have hD : universalDivisor (ZMod 2)
        = (X 0 + X 1) * ((X 0 + X 1 + X 2) * (X 1 + X 2) * (X 2 + X 0)) := by
      simp only [universalDivisor]; ring1
    simp only [map_mul, map_pow, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [hA, hA2, hD]
    linear_combination
      (2 * X 0 ^ 2 * X 1 ^ 2 * X 2 *
        ((X 0 + X 1 + X 2) * (X 1 + X 2) * (X 2 + X 0)) ^ 2) * charTwo_two_eq_zero

/-- The universal divisor over `ZMod 2`, expanded as a sum of six degree-four monomials
(each a product of a cube and a linear variable). -/
theorem charTwo_universalDivisor_expand :
    universalDivisor (ZMod 2) =
      X 0 ^ 3 * X 1 ^ 1 + X 0 ^ 3 * X 2 ^ 1 + X 0 ^ 1 * X 1 ^ 3 + X 1 ^ 3 * X 2 ^ 1 +
        X 0 ^ 1 * X 2 ^ 3 + X 1 ^ 1 * X 2 ^ 3 := by
  simp only [universalDivisor]
  linear_combination (X 0 * X 1 + X 0 * X 2 + X 1 * X 2) ^ 2 * charTwo_two_eq_zero

/-- Rewrites a product of two pure variable powers as a single monomial, to unfold `coeff`
against an explicit exponent via `coeff_monomial`. -/
private theorem charTwo_coeff_X_pow_mul_X_pow (i j : Fin 3) (a b : ℕ) :
    (X i ^ a * X j ^ b : MvPolynomial (Fin 3) (ZMod 2)) =
      monomial (Finsupp.single i a + Finsupp.single j b) 1 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, mul_one]

/-- Rewrites a product of three pure variable powers as a single monomial. -/
private theorem charTwo_coeff_X_pow_mul_X_pow_mul_X_pow (i j k : Fin 3) (a b c : ℕ) :
    (X i ^ a * X j ^ b * X k ^ c : MvPolynomial (Fin 3) (ZMod 2)) =
      monomial (Finsupp.single i a + Finsupp.single j b + Finsupp.single k c) 1 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, monomial_mul_monomial,
    mul_one, mul_one]

/-- The universal divisor over `ZMod 2` is nonzero, witnessed by the nonzero coefficient of
`X0³X1`. -/
theorem charTwo_universalDivisor_ne_zero : universalDivisor (ZMod 2) ≠ 0 := by
  intro h0
  have hc := congrArg
    (·.coeff (Finsupp.single 0 3 + Finsupp.single 1 1 : Fin 3 →₀ ℕ)) h0
  rw [charTwo_universalDivisor_expand] at hc
  have hne2 : (Finsupp.single 0 3 + Finsupp.single 2 1 : Fin 3 →₀ ℕ)
      ≠ (Finsupp.single 0 3 + Finsupp.single 1 1 : Fin 3 →₀ ℕ) := by
    intro heq
    have h1 := congrArg (fun g : Fin 3 →₀ ℕ => g 1) heq
    simp [Finsupp.add_apply] at h1
  have hne3 : (Finsupp.single 0 1 + Finsupp.single 1 3 : Fin 3 →₀ ℕ)
      ≠ (Finsupp.single 0 3 + Finsupp.single 1 1 : Fin 3 →₀ ℕ) := by
    intro heq
    have h1 := congrArg (fun g : Fin 3 →₀ ℕ => g 0) heq
    simp [Finsupp.add_apply] at h1
  have hne4 : (Finsupp.single 1 3 + Finsupp.single 2 1 : Fin 3 →₀ ℕ)
      ≠ (Finsupp.single 0 3 + Finsupp.single 1 1 : Fin 3 →₀ ℕ) := by
    intro heq
    have h1 := congrArg (fun g : Fin 3 →₀ ℕ => g 0) heq
    simp [Finsupp.add_apply] at h1
  have hne5 : (Finsupp.single 0 1 + Finsupp.single 2 3 : Fin 3 →₀ ℕ)
      ≠ (Finsupp.single 0 3 + Finsupp.single 1 1 : Fin 3 →₀ ℕ) := by
    intro heq
    have h1 := congrArg (fun g : Fin 3 →₀ ℕ => g 0) heq
    simp [Finsupp.add_apply] at h1
  have hne6 : (Finsupp.single 1 1 + Finsupp.single 2 3 : Fin 3 →₀ ℕ)
      ≠ (Finsupp.single 0 3 + Finsupp.single 1 1 : Fin 3 →₀ ℕ) := by
    intro heq
    have h1 := congrArg (fun g : Fin 3 →₀ ℕ => g 0) heq
    simp [Finsupp.add_apply] at h1
  simp only [charTwo_coeff_X_pow_mul_X_pow, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_monomial,
    AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, hne2, hne3, hne4, hne5, hne6, ite_true, ite_false] at hc
  norm_num at hc

/-- Clause 5: `X₀X₁X₂ · universalDivisor(ZMod 2)²` is nonzero. -/
theorem charTwo_f_ne_zero :
    X 0 * X 1 * X 2 * universalDivisor (ZMod 2) ^ 2 ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (X_ne_zero 0) (X_ne_zero 1)) (X_ne_zero 2))
    (pow_ne_zero 2 charTwo_universalDivisor_ne_zero)

/-- Clause 6: `X₀X₁X₂ · universalDivisor(ZMod 2)²` is homogeneous of degree eleven
(`3` from `X₀X₁X₂` plus `2 * 4` from the squared degree-four universal divisor). -/
theorem charTwo_f_isHomogeneous :
    (X 0 * X 1 * X 2 * universalDivisor (ZMod 2) ^ 2).IsHomogeneous 11 := by
  have h0 := MvPolynomial.isHomogeneous_X (ZMod 2) (0 : Fin 3)
  have h1 := MvPolynomial.isHomogeneous_X (ZMod 2) (1 : Fin 3)
  have h2 := MvPolynomial.isHomogeneous_X (ZMod 2) (2 : Fin 3)
  have hD : (universalDivisor (ZMod 2)).IsHomogeneous 4 := by
    have f1 : (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) (ZMod 2)).IsHomogeneous 1 :=
      (h0.add h1).add h2
    have f2 : (X 0 + X 1 : MvPolynomial (Fin 3) (ZMod 2)).IsHomogeneous 1 := h0.add h1
    have f3 : (X 1 + X 2 : MvPolynomial (Fin 3) (ZMod 2)).IsHomogeneous 1 := h1.add h2
    have f4 : (X 2 + X 0 : MvPolynomial (Fin 3) (ZMod 2)).IsHomogeneous 1 := h2.add h0
    simp only [universalDivisor]
    have hh := ((f1.mul f2).mul f3).mul f4
    norm_num at hh
    exact hh
  have hX : (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) (ZMod 2)).IsHomogeneous 3 := by
    have hh := (h0.mul h1).mul h2
    norm_num at hh
    exact hh
  have hD2 : (universalDivisor (ZMod 2) ^ 2).IsHomogeneous 8 := by
    have hh := hD.pow 2
    norm_num at hh
    exact hh
  have hh := hX.mul hD2
  norm_num at hh
  exact hh

/-- `universalDivisor(ZMod 2)` squared, expanded via the Frobenius identity `add_pow_char`. -/
theorem charTwo_universalDivisor_sq_expand :
    universalDivisor (ZMod 2) ^ 2 =
      X 0 ^ 6 * X 1 ^ 2 + X 0 ^ 6 * X 2 ^ 2 + X 0 ^ 2 * X 1 ^ 6 + X 1 ^ 6 * X 2 ^ 2 +
        X 0 ^ 2 * X 2 ^ 6 + X 1 ^ 2 * X 2 ^ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [charTwo_universalDivisor_expand,
    add_pow_char _ _ 2, add_pow_char _ _ 2, add_pow_char _ _ 2, add_pow_char _ _ 2,
    add_pow_char _ _ 2]
  ring1

/-- `X₀X₁X₂ · universalDivisor(ZMod 2)²`, expanded as a sum of six degree-eleven monomials
(all six permutations of exponent `(7,3,1)`). -/
theorem charTwo_f_expand :
    X 0 * X 1 * X 2 * universalDivisor (ZMod 2) ^ 2 =
      X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 1 + X 0 ^ 7 * X 1 ^ 1 * X 2 ^ 3 +
        X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 1 + X 0 ^ 1 * X 1 ^ 7 * X 2 ^ 3 +
        X 0 ^ 3 * X 1 ^ 1 * X 2 ^ 7 + X 0 ^ 1 * X 1 ^ 3 * X 2 ^ 7 := by
  rw [charTwo_universalDivisor_sq_expand]
  ring1

/-- Clause 7: `X₀X₁X₂ · universalDivisor(ZMod 2)²` is not `Pairwise` — it has a monomial
(witnessed by exponent `(7,3,1)`, i.e. all three variables occurring) with nonzero
coefficient. -/
theorem charTwo_not_pairwise :
    ¬ TernaryPoly.Paper.Pairwise (X 0 * X 1 * X 2 * universalDivisor (ZMod 2) ^ 2) := by
  intro hP
  have hpos : ∀ i : Fin 3,
      0 < (Finsupp.single 0 7 + Finsupp.single 1 3 + Finsupp.single 2 1 : Fin 3 →₀ ℕ) i := by
    intro i; fin_cases i <;> simp [Finsupp.add_apply]
  have hz := hP (Finsupp.single 0 7 + Finsupp.single 1 3 + Finsupp.single 2 1) hpos
  rw [charTwo_f_expand] at hz
  have hne2 : (Finsupp.single 0 7 + Finsupp.single 1 1 + Finsupp.single 2 3 : Fin 3 →₀ ℕ)
      ≠ (Finsupp.single 0 7 + Finsupp.single 1 3 + Finsupp.single 2 1 : Fin 3 →₀ ℕ) := by
    intro heq
    have h1 := congrArg (fun g : Fin 3 →₀ ℕ => g 1) heq
    simp [Finsupp.add_apply] at h1
  have hne3 : (Finsupp.single 0 3 + Finsupp.single 1 7 + Finsupp.single 2 1 : Fin 3 →₀ ℕ)
      ≠ (Finsupp.single 0 7 + Finsupp.single 1 3 + Finsupp.single 2 1 : Fin 3 →₀ ℕ) := by
    intro heq
    have h1 := congrArg (fun g : Fin 3 →₀ ℕ => g 0) heq
    simp [Finsupp.add_apply] at h1
  have hne4 : (Finsupp.single 0 1 + Finsupp.single 1 7 + Finsupp.single 2 3 : Fin 3 →₀ ℕ)
      ≠ (Finsupp.single 0 7 + Finsupp.single 1 3 + Finsupp.single 2 1 : Fin 3 →₀ ℕ) := by
    intro heq
    have h1 := congrArg (fun g : Fin 3 →₀ ℕ => g 0) heq
    simp [Finsupp.add_apply] at h1
  have hne5 : (Finsupp.single 0 3 + Finsupp.single 1 1 + Finsupp.single 2 7 : Fin 3 →₀ ℕ)
      ≠ (Finsupp.single 0 7 + Finsupp.single 1 3 + Finsupp.single 2 1 : Fin 3 →₀ ℕ) := by
    intro heq
    have h1 := congrArg (fun g : Fin 3 →₀ ℕ => g 0) heq
    simp [Finsupp.add_apply] at h1
  have hne6 : (Finsupp.single 0 1 + Finsupp.single 1 3 + Finsupp.single 2 7 : Fin 3 →₀ ℕ)
      ≠ (Finsupp.single 0 7 + Finsupp.single 1 3 + Finsupp.single 2 1 : Fin 3 →₀ ℕ) := by
    intro heq
    have h1 := congrArg (fun g : Fin 3 →₀ ℕ => g 0) heq
    simp [Finsupp.add_apply] at h1
  simp only [charTwo_coeff_X_pow_mul_X_pow_mul_X_pow, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    MvPolynomial.coeff_monomial, hne2, hne3, hne4, hne5, hne6, ite_true, ite_false] at hz
  norm_num at hz

end TernaryPeriodPolynomials.Argument
