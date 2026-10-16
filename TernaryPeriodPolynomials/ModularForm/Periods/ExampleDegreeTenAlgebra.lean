module

public import TernaryPeriodPolynomials.Polynomial.Defs

@[expose] public section



/-!
# Pure-algebra half of `example_degree_ten` (target (2))

Everything here is a literal ring identity about `symmetricTenPeriod`/`alternatingTenPeriod`
over an arbitrary `CommRing R`: homogeneity of degree 10, the six swap/parity identities that
are also literal conjuncts of the target statement, the four `PeriodRelations` clauses,
and (for a `Field`) membership in `oddPeriodSpace`/`evenPeriodSpace`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument

open MvPolynomial TernaryPoly.Paper

variable {R : Type*} [CommRing R]

/-! ## Swap and parity identities -/

theorem symmetricTenPeriod_swap :
    bind₁ (![X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) R) (symmetricTenPeriod R) =
      symmetricTenPeriod R := by
  simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, map_ofNat, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem symmetricTenPeriod_oddX :
    bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) R) (symmetricTenPeriod R) =
      -symmetricTenPeriod R := by
  simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, map_ofNat, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem symmetricTenPeriod_oddY :
    bind₁ (![X 0, -X 1] : Fin 2 → MvPolynomial (Fin 2) R) (symmetricTenPeriod R) =
      -symmetricTenPeriod R := by
  simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, map_ofNat, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem alternatingTenPeriod_antiswap :
    bind₁ (![X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) R) (alternatingTenPeriod R) =
      -alternatingTenPeriod R := by
  simp only [alternatingTenPeriod, map_mul, map_pow, map_sub, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem alternatingTenPeriod_evenX :
    bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) R) (alternatingTenPeriod R) =
      alternatingTenPeriod R := by
  simp only [alternatingTenPeriod, map_mul, map_pow, map_sub, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem alternatingTenPeriod_evenY :
    bind₁ (![X 0, -X 1] : Fin 2 → MvPolynomial (Fin 2) R) (alternatingTenPeriod R) =
      alternatingTenPeriod R := by
  simp only [alternatingTenPeriod, map_mul, map_pow, map_sub, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ## `PeriodRelations` -/

theorem symmetricTenPeriod_axis_first :
    bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) R) (symmetricTenPeriod R) = 0 := by
  simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, map_ofNat, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem symmetricTenPeriod_axis_second :
    bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) R) (symmetricTenPeriod R) = 0 := by
  simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, map_ofNat, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem alternatingTenPeriod_axis_first :
    bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) R) (alternatingTenPeriod R) = 0 := by
  simp only [alternatingTenPeriod, map_mul, map_pow, map_sub, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem alternatingTenPeriod_axis_second :
    bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) R) (alternatingTenPeriod R) = 0 := by
  simp only [alternatingTenPeriod, map_mul, map_pow, map_sub, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem symmetricTenPeriod_two_term :
    symmetricTenPeriod R +
      bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) R) (symmetricTenPeriod R) = 0 := by
  simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, map_ofNat, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem symmetricTenPeriod_three_term :
    symmetricTenPeriod R +
      bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) R) (symmetricTenPeriod R) +
      bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) R) (symmetricTenPeriod R) = 0 := by
  simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, map_ofNat, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem alternatingTenPeriod_two_term :
    alternatingTenPeriod R +
      bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) R) (alternatingTenPeriod R) = 0 := by
  simp only [alternatingTenPeriod, map_mul, map_pow, map_sub, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem alternatingTenPeriod_three_term :
    alternatingTenPeriod R +
      bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) R) (alternatingTenPeriod R) +
      bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) R) (alternatingTenPeriod R) = 0 := by
  simp only [alternatingTenPeriod, map_mul, map_pow, map_sub, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem symmetricTenPeriod_periodRelations :
    PeriodRelations (symmetricTenPeriod R) :=
  ⟨symmetricTenPeriod_axis_first, symmetricTenPeriod_axis_second, symmetricTenPeriod_two_term,
    symmetricTenPeriod_three_term⟩

theorem alternatingTenPeriod_periodRelations :
    PeriodRelations (alternatingTenPeriod R) :=
  ⟨alternatingTenPeriod_axis_first, alternatingTenPeriod_axis_second,
    alternatingTenPeriod_two_term, alternatingTenPeriod_three_term⟩

/-! ## Homogeneity -/

theorem symmetricTenPeriod_isHomogeneous :
    (symmetricTenPeriod R).IsHomogeneous 10 := by
  have hX0 : (X 0 : MvPolynomial (Fin 2) R).IsHomogeneous 1 := isHomogeneous_X R 0
  have hX1 : (X 1 : MvPolynomial (Fin 2) R).IsHomogeneous 1 := isHomogeneous_X R 1
  have hX0sq : (X 0 ^ 2 : MvPolynomial (Fin 2) R).IsHomogeneous 2 := isHomogeneous_X_pow 0 2
  have hX1sq : (X 1 ^ 2 : MvPolynomial (Fin 2) R).IsHomogeneous 2 := isHomogeneous_X_pow 1 2
  have hdiff : (X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) R).IsHomogeneous 2 := hX0sq.sub hX1sq
  have hdiffsq : ((X 0 ^ 2 - X 1 ^ 2) ^ 2 : MvPolynomial (Fin 2) R).IsHomogeneous 4 := hdiff.pow 2
  have h4X1sq : (4 * X 1 ^ 2 : MvPolynomial (Fin 2) R).IsHomogeneous 2 := by
    have heq : (4 : MvPolynomial (Fin 2) R) * X 1 ^ 2 = X 1 ^ 2 + X 1 ^ 2 + X 1 ^ 2 + X 1 ^ 2 := by
      ring
    rw [heq]; exact ((hX1sq.add hX1sq).add hX1sq).add hX1sq
  have h4X0sq : (4 * X 0 ^ 2 : MvPolynomial (Fin 2) R).IsHomogeneous 2 := by
    have heq : (4 : MvPolynomial (Fin 2) R) * X 0 ^ 2 = X 0 ^ 2 + X 0 ^ 2 + X 0 ^ 2 + X 0 ^ 2 := by
      ring
    rw [heq]; exact ((hX0sq.add hX0sq).add hX0sq).add hX0sq
  have hfac3 : (X 0 ^ 2 - 4 * X 1 ^ 2 : MvPolynomial (Fin 2) R).IsHomogeneous 2 := hX0sq.sub h4X1sq
  have hfac4 : (4 * X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) R).IsHomogeneous 2 := h4X0sq.sub hX1sq
  show (X 0 * X 1 * (X 0 ^ 2 - X 1 ^ 2) ^ 2 * (X 0 ^ 2 - 4 * X 1 ^ 2) * (4 * X 0 ^ 2 - X 1 ^ 2) :
    MvPolynomial (Fin 2) R).IsHomogeneous 10
  exact ((((hX0.mul hX1).mul hdiffsq).mul hfac3).mul hfac4)

theorem alternatingTenPeriod_isHomogeneous :
    (alternatingTenPeriod R).IsHomogeneous 10 := by
  have hX0sq : (X 0 ^ 2 : MvPolynomial (Fin 2) R).IsHomogeneous 2 := isHomogeneous_X_pow 0 2
  have hX1sq : (X 1 ^ 2 : MvPolynomial (Fin 2) R).IsHomogeneous 2 := isHomogeneous_X_pow 1 2
  have hdiff : (X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) R).IsHomogeneous 2 := hX0sq.sub hX1sq
  have hdiffcube : ((X 0 ^ 2 - X 1 ^ 2) ^ 3 : MvPolynomial (Fin 2) R).IsHomogeneous 6 := hdiff.pow 3
  show (X 0 ^ 2 * X 1 ^ 2 * (X 0 ^ 2 - X 1 ^ 2) ^ 3 :
    MvPolynomial (Fin 2) R).IsHomogeneous 10
  exact (hX0sq.mul hX1sq).mul hdiffcube

/-! ## Membership in `oddPeriodSpace` / `evenPeriodSpace` -/

theorem symmetricTenPeriod_mem_oddPeriodSpace :
    symmetricTenPeriod R ∈ oddPeriodSpace R 10 := by
  refine ⟨⟨symmetricTenPeriod_isHomogeneous, symmetricTenPeriod_periodRelations⟩, ?_⟩
  show bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) R) (symmetricTenPeriod R) +
      symmetricTenPeriod R = 0
  rw [symmetricTenPeriod_oddX]; ring

theorem alternatingTenPeriod_mem_evenPeriodSpace :
    alternatingTenPeriod R ∈ evenPeriodSpace R 10 := by
  refine ⟨⟨alternatingTenPeriod_isHomogeneous, alternatingTenPeriod_periodRelations⟩, ?_⟩
  show bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) R) (alternatingTenPeriod R) -
      alternatingTenPeriod R = 0
  rw [alternatingTenPeriod_evenX]; ring

end TernaryPeriodPolynomials.Argument
