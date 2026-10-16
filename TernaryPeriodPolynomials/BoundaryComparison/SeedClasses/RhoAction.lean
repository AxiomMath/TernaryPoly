module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section


/-!
# The coefficient action `ρ(g)f(𝐗) = det(g)⁻¹ f(g⁻¹𝐗)` of Appendix C.3

Paper: §C.3 (`ar:sec:series`):
`E = Sym^n((ℂ³)*) ⊗ det⁻¹` with `ρ(g)f(𝐗) = det(g)⁻¹ f(g⁻¹𝐗)`, `𝐗 = (X, Y, Z)ᵗ`.

The definition `leviCoefficientAction` is this action only for `g = diag(A, t)`. Here the
literal action for an arbitrary invertible real `3 × 3` matrix is defined, and compared on the
group `Γ_P`-shaped matrices `[[A, w], [0, 1]]` with the Levi action composed with the
radical-translation substitution of the `seed_closed_equivariant`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

/-- The coefficient action `ρ(g) f (𝐗) = det(g)⁻¹ f(g⁻¹𝐗)` on `ℂ[X, Y, Z]`, for a real `3 × 3`
matrix `g` (the entries of `g⁻¹` being the real matrix inverse). -/
def rho (g : Matrix (Fin 3) (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℂ) : MvPolynomial (Fin 3) ℂ :=
  C ((g.det⁻¹ : ℝ) : ℂ) *
    bind₁ (fun i : Fin 3 => ∑ j : Fin 3, C (((g⁻¹) i j : ℝ) : ℂ) * X j) q

/-- The matrix `[[A, w], [0, 1]]` of the parabolic `Γ_P`-elements with trivial normal part, in the
block form `g = [[A, w], [0, 1]]` acting on plane coordinates by `u ↦ Au + w`. -/
def parabolicMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![A 0 0, A 0 1, w 0; A 1 0, A 1 1, w 1; 0, 0, 1]

/-- The plane-coordinate map `p ↦ (Au + w, Aτ, p₄)` of `[[A, w], [0, 1]]`: the Levi map with
`t = 1` followed by the radical translation by `w`. -/
def parabolicMap (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) (p : Fin 5 → ℝ) : Fin 5 → ℝ :=
  leviMap A 1 p + ![w 0, w 1, 0, 0, 0]

theorem det_parabolicMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) :
    (parabolicMatrix A w).det = A.det := by
  simp [parabolicMatrix, Matrix.det_fin_three, Matrix.det_fin_two]

/-- Explicit inverse of `parabolicMatrix A w`. -/
theorem inv_parabolicMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) (hA : A.det ≠ 0) :
    (parabolicMatrix A w)⁻¹ =
      !![A 1 1 / A.det, -A 0 1 / A.det, (-(A 1 1 * w 0) + A 0 1 * w 1) / A.det;
         -A 1 0 / A.det, A 0 0 / A.det, (A 1 0 * w 0 - A 0 0 * w 1) / A.det; 0, 0, 1] := by
  have hd : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
  have hA' : A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0 := hd ▸ hA
  have hA2 : -(A 1 0 * A 0 1) + A 0 0 * A 1 1 ≠ 0 := by intro h; apply hA'; linarith
  have hA3 : -(A 1 0 * A 0 1) + A 1 1 * A 0 0 ≠ 0 := by intro h; apply hA'; linarith
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parabolicMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;>
      (try rw [hd]) <;> ring_nf

theorem aux_row (p q w0 w1 : ℂ) :
    C p * X 0 + C q * X 1 + C (-(p * w0) - q * w1) * (X 2 : MvPolynomial (Fin 3) ℂ) =
      C p * (X 0 - C w0 * X 2) + C q * (X 1 - C w1 * X 2) := by
  rw [sub_eq_add_neg, C_add, C_neg, C_neg, C_mul, C_mul]
  ring

/-- Comparison: the literal action `ρ([[A, w], [0, 1]])` is the Levi coefficient action
`ρ(diag(A, 1))` followed by the radical-translation substitution `(X, Y) ↦ (X - w₁Z, Y - w₂Z)`
of the `seed_closed_equivariant`. -/
theorem rho_parabolicMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) (hA : A.det ≠ 0)
    (q : MvPolynomial (Fin 3) ℂ) :
    rho (parabolicMatrix A w) q =
      bind₁ (![X 0 - C (w 0 : ℂ) * X 2, X 1 - C (w 1 : ℂ) * X 2, X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) (leviCoefficientAction A 1 q) := by
  have hδ : (A.det : ℂ) ≠ 0 := by exact_mod_cast hA
  unfold rho leviCoefficientAction
  rw [det_parabolicMatrix, inv_parabolicMatrix A w hA, map_mul, bind₁_C_right, bind₁_bind₁]
  congr 1
  · simp
  · congr 2
    funext i
    fin_cases i
    · simp [Fin.sum_univ_three]
      convert aux_row (↑(A 1 1)/↑A.det) (-↑(A 0 1)/↑A.det) ↑(w 0) ↑(w 1) using 3
      ring_nf
    · simp [Fin.sum_univ_three]
      convert aux_row (-↑(A 1 0)/↑A.det) (↑(A 0 0)/↑A.det) ↑(w 0) ↑(w 1) using 3
      ring_nf
    · simp [Fin.sum_univ_three]

end TernaryPeriodPolynomials.Argument.SeedC3
