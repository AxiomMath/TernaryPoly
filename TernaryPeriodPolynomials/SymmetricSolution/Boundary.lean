module

public import TernaryPeriodPolynomials.SymmetricSolution.Certificate
public import TernaryPeriodPolynomials.Polynomial.Shear
public import TernaryPeriodPolynomials.ArithmeticCohomology.Boundary
public import TernaryPeriodPolynomials.Polynomial.Parity

@[expose] public section


open MvPolynomial

namespace TernaryPoly

open SymmetricCertificate

private theorem bind_value {σ τ : Type*} (q : σ → MvPolynomial τ ℚ)
    (f : TernaryPolynomial) (a b c : MvPolynomial σ ℚ) :
    bind₁ q (value f a b c) = value f (bind₁ q a) (bind₁ q b) (bind₁ q c) := by
  unfold value
  rw [bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem value_axis_zero {σ : Type*} {f : TernaryPolynomial}
    (hf : PeriodRelations f) (t : MvPolynomial σ ℚ) : value f 0 0 t = 0 := by
  have h := congrArg (fun p => value p t 0 0) hf.axisZ_eq_zero
  rw [axisZ, value_bind] at h
  simpa [value] using h

/-- The opposite-plane certificate and translation rigidity imply genuine vanishing. -/
theorem symmetric_opposite_plane_zero {f : TernaryPolynomial}
    (hf : PeriodRelations f) (hs : S f = f) (ν : ℚ) (hν : ν ≠ 0)
    (hp : bind₁ ![-X 0, -X 1, -X 2] f = ν • f) :
    value f (X 0) (-X 0) (X 1) = (0 : MvPolynomial (Fin 2) ℚ) := by
  let g : MvPolynomial (Fin 2) ℚ := value f (X 0) (-X 0) (X 1)
  have hg : bind₁ ![X 0 + X 1, X 1] g = g := by
    dsimp [g]
    rw [bind_value]
    simpa using opposite_translation hf.1 hs hf.2 ν hν hp
      (X (0 : Fin 2)) (X (1 : Fin 2))
  have hr := shear_invariant_first_variable g hg
  change g = 0
  calc
    g = bind₁ ![0, X 1] g := hr.symm
    _ = value f 0 0 (X (1 : Fin 2)) := by simp [g, bind_value]
    _ = 0 := value_axis_zero hf _

theorem symmetric_opposite_value_zero {σ : Type*} {f : TernaryPolynomial}
    (hf : PeriodRelations f) (hs : S f = f) (ν : ℚ) (hν : ν ≠ 0)
    (hp : bind₁ ![-X 0, -X 1, -X 2] f = ν • f) (s t : MvPolynomial σ ℚ) :
    value f s (-s) t = 0 := by
  have h := congrArg (bind₁ ![s, t]) (symmetric_opposite_plane_zero hf hs ν hν hp)
  simpa only [bind_value, bind₁_X_right, map_neg, Matrix.cons_val_zero,
    Matrix.cons_val_one, map_zero] using h

/-- An even symmetric solution vanishes on the total-coordinate plane. -/
theorem symmetric_total_plane_zero {f : TernaryPolynomial}
    (hf : PeriodRelations f) (hs : S f = f)
    (hp : bind₁ ![-X 0, -X 1, -X 2] f = f) :
    value f (X 0) (X 1) (-(X 0 + X 1)) = (0 : MvPolynomial (Fin 2) ℚ) := by
  let g : MvPolynomial (Fin 2) ℚ := value f (X 0) (X 1) (-(X 0 + X 1))
  have hg : bind₁ ![X 0 + X 1, X 1] g = g := by
    dsimp [g]
    rw [bind_value]
    have harg : -((X 0 + X 1) + X 1 : MvPolynomial (Fin 2) ℚ) =
        -(X 0 + X 1) - X 1 := by abel
    simpa only [bind₁_X_right, map_neg, map_add, Matrix.cons_val_zero,
      Matrix.cons_val_one, harg] using total_translation_first hf.1 hs hf.2 hp
      (X (0 : Fin 2)) (X (1 : Fin 2))
  have hr := shear_invariant_first_variable g hg
  change g = 0
  calc
    g = bind₁ ![0, X 1] g := hr.symm
    _ = value f 0 (X (1 : Fin 2)) (-X 1) := by simp [g, bind_value]
    _ = value f (X (1 : Fin 2)) (-X 1) 0 := by
      rw [value_cyclic hf.1 0 (X (1 : Fin 2)) (-X 1)]
    _ = 0 := symmetric_opposite_value_zero hf hs 1 one_ne_zero (by simpa using hp) _ _

theorem symmetric_total_value_zero {σ : Type*} {f : TernaryPolynomial}
    (hf : PeriodRelations f) (hs : S f = f)
    (hp : bind₁ ![-X 0, -X 1, -X 2] f = f) (s t : MvPolynomial σ ℚ) :
    value f s t (-(s + t)) = 0 := by
  have h := congrArg (bind₁ ![s, t]) (symmetric_total_plane_zero hf hs hp)
  simpa only [bind_value, bind₁_X_right, map_neg, map_add, Matrix.cons_val_zero,
    Matrix.cons_val_one, map_zero] using h

/-- Homogeneity supplies the nonzero negation sign needed by the opposite-plane proof. -/
theorem homogeneous_symmetric_opposite_plane_zero {f : TernaryPolynomial} {n : ℕ}
    (hf : PeriodRelations f) (hs : S f = f) (hg : f.IsHomogeneous n) :
    value f (X 0) (-X 0) (X 1) = (0 : MvPolynomial (Fin 2) ℚ) :=
  symmetric_opposite_plane_zero hf hs ((-1 : ℚ) ^ n)
    (pow_ne_zero n (by norm_num)) (homogeneous_bind_neg hg)

/-- Every even homogeneous symmetric solution vanishes on the total-coordinate plane. -/
theorem homogeneous_symmetric_total_plane_zero {f : TernaryPolynomial} {n : ℕ}
    (hf : PeriodRelations f) (hs : S f = f) (hg : f.IsHomogeneous n) (hn : Even n) :
    value f (X 0) (X 1) (-(X 0 + X 1)) = (0 : MvPolynomial (Fin 2) ℚ) :=
  symmetric_total_plane_zero hf hs (homogeneous_bind_neg_even hg hn)

end TernaryPoly
