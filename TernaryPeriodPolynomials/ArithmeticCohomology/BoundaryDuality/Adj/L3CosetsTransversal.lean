module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3CosetsFricke

@[expose] public section


/-!
# An explicit transversal of `Γ₁'(3) ∩ Γ⁰(p)` in `Γ₁'(3)`

The stabilizer `H = Γ₁'(3) ∩ Γ⁰(p)` of the base coset `0` (representative `α₀ = diag(1, p)`) has
the transversal

  `transv (some i) = T^i`,   `transv none = s⁻¹ = [[-p, ε], [1 - ε p, 1]]`

(`transv`), where `s` is the Fricke element of `AdjL3CosetsFricke`: it carries the base coset to
the coset `j` (`levelNext_transv : α₀ r_j ∈ Γ₁'(3) α_j`).  The transitions are
`α₀ T^i = α_i` and `α₀ s⁻¹ = s α_∞` (`levelDelta_transv`: `δ(r_i, 0) = 1`,
`δ(r_∞, 0) = s`).  The determinant of `transv none` is `-ε_p`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets

section Transversal

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

theorem upper_val (n : ℤ) :
    (((upper n).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, n; 0, 1] := rfl

theorem lower_val (n : ℤ) :
    (((lower n).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 3 * n, 1] := rfl

/-- **The transversal of the stabilizer `Γ₁'(3) ∩ Γ⁰(p)`**: `T^i` for the coset `i`, and
`s⁻¹ = [[-p, ε], [1 - ε p, 1]]` for the coset `∞`. -/
def transv : Option (Fin p.val) → binaryArithmeticLevel
  | some i => upper (i.val : ℤ)
  | none => sInv p hp3

theorem transv_some (i : Fin p.val) : transv p hp3 (some i) = upper (i.val : ℤ) := rfl

theorem transv_none : transv p hp3 none = sInv p hp3 := rfl

/-- The transition of the transversal: `α₀ · transv j = deltaTransv j · α_j`. -/
def deltaTransv : Option (Fin p.val) → binaryArithmeticLevel
  | some _ => 1
  | none => sF p hp3

theorem deltaTransv_none : deltaTransv p hp3 none = sF p hp3 := rfl

theorem sF_mul_N :
    (((sF p hp3).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * N p none =
      N p (baseIdx p) * (((sInv p hp3).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) := by
  have he := eps_mul_self p
  rw [sF_val, sInv_val, N_none, N_baseIdx, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by linear_combination (-(p.val : ℤ)) * he) (by ring)
    (by linear_combination (p.val : ℤ) * he) (by linear_combination (p.val : ℤ) * he)

theorem deltaTransv_mul (j : Option (Fin p.val)) :
    (((deltaTransv p hp3 j).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * N p j =
      N p (baseIdx p) * (((transv p hp3 j).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) := by
  cases j with
  | none => exact sF_mul_N p hp3
  | some i =>
    have h1 : (((deltaTransv p hp3 (some i)).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
      rfl
    rw [h1, Matrix.one_mul, transv_some, upper_val, N_baseIdx, N_some, Matrix.mul_fin_two]
    exact mat2_eq (by ring) (by ring) (by ring) (by ring)

/-- **The transversal carries the base coset to the coset `j`.** -/
theorem levelNext_transv (j : Option (Fin p.val)) :
    levelNext p hp3 (transv p hp3 j) (baseIdx p) = j :=
  levelNext_eq_of_mul p hp3 _ (deltaTransv p hp3 j) _ _ (deltaTransv_mul p hp3 j)

/-- The transition `δ(transv j, 0)` of the transversal is `deltaTransv j`. -/
theorem levelDelta_transv (j : Option (Fin p.val)) :
    levelDelta p hp3 (transv p hp3 j) (baseIdx p) = deltaTransv p hp3 j :=
  levelDelta_eq_of_mul p hp3 _ _ _ _ (deltaTransv_mul p hp3 j)

/-- The determinant of `transv none = s⁻¹` is `-ε_p`. -/
theorem det_sInv : (((sInv p hp3).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ).det =
    -(eps p) := by
  have he := eps_mul_self p
  rw [sInv_val, Matrix.det_fin_two_of]
  linear_combination (p.val : ℤ) * he

/-- The determinant of `s` is `-ε_p`. -/
theorem det_sF : (((sF p hp3).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ).det =
    -(eps p) := by
  have he := eps_mul_self p
  rw [sF_val, Matrix.det_fin_two_of]
  linear_combination (-(p.val : ℤ)) * he

end Transversal

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets
