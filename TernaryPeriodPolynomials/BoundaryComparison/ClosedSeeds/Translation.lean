module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs

@[expose] public section


/-! Clause (ii) of Lemma C.3 (`ar:lem:seed`): a radical translation `u ↦ u + (v, w, 0, 0, 0)`
acts on the seed by the coefficient substitution `(X, Y) ↦ (X - vZ, Y - wZ)`.
Feeds `TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- `seedTau` only reads coordinates `2, 3`, so it is invariant under a shift that only moves
coordinates `0, 1`. -/
theorem seedTau_add_shift (p : Fin 5 → ℝ) (v w : ℝ) :
    seedTau (p + ![v, w, 0, 0, 0]) = seedTau p := by
  simp [seedTau, Pi.add_apply]

/-- `seedBeta` is built purely from `seedTau`, so it inherits shift-invariance. -/
theorem seedBeta_add_shift (p : Fin 5 → ℝ) (v w : ℝ) :
    seedBeta (p + ![v, w, 0, 0, 0]) = seedBeta p := by
  simp only [seedBeta, seedTau_add_shift]

/-- The coefficient substitution `(X, Y) ↦ (X - vZ, Y - wZ)` pulls `seedLinear p` back to
`seedLinear` at the shifted point `p + (v, w, 0, 0, 0)`. -/
theorem seedLinear_bind_shift (p : Fin 5 → ℝ) (v w : ℝ) :
    bind₁ (![X 0 - C (v : ℂ) * X 2, X 1 - C (w : ℂ) * X 2, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)
        (seedLinear p)
      = seedLinear (p + ![v, w, 0, 0, 0]) := by
  have h0 : (p + ![v, w, (0 : ℝ), 0, 0]) 0 = p 0 + v := by simp [Pi.add_apply]
  have h1 : (p + ![v, w, (0 : ℝ), 0, 0]) 1 = p 1 + w := by simp [Pi.add_apply]
  simp only [seedLinear, seedTau_add_shift, h0, h1]
  push_cast
  simp only [map_add, map_sub, map_mul, bind₁_X_right, bind₁_C_right,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- Clause (ii) of Lemma C.3: the seed at a radically-translated point equals the pullback of
the seed at the original point under the coefficient substitution `(X, Y) ↦ (X - vZ, Y - wZ)`. -/
theorem lemma_C3_ii (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (v w : ℝ) (i j : Fin 5) :
    seedForm n h (p + ![v, w, 0, 0, 0]) i j =
      bind₁ (![X 0 - C (v : ℂ) * X 2, X 1 - C (w : ℂ) * X 2, X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ)
        (seedForm n h p i j) := by
  simp only [seedForm, seedTau_add_shift, seedBeta_add_shift, map_mul, map_pow, bind₁_C_right]
  rw [seedLinear_bind_shift]

end TernaryPeriodPolynomials.Argument
