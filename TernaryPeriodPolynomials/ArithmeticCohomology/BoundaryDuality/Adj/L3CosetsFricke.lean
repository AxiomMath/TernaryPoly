module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3CosetsBasic

@[expose] public section


/-!
# The Fricke involution of `Γ₁'(3) ∩ Γ⁰(p)`

Let `ε = ε_p = ±1` with `ε ≡ p mod 3` and `α₀ = diag(1, p)`.  The element

  `s = [[-ε, 1], [ε - p, p ε]] ∈ Γ₁'(3)`  (`sF`, determinant `-ε`)

and its inverse `s⁻¹ = [[-p, ε], [1 - ε p, 1]]` (`sInv`) satisfy `α₀ s⁻¹ = s α_∞`
(`sInv` is therefore a representative of the coset `∞` for the transversal, see
`AdjL3CosetsTransversal`).  Put `g' = α₀⁻¹ s ∈ GL₂(ℚ)` (`gP`).  Then

* `g' = [[-ε, 1], [(ε - p)/p, ε]]` has trace zero and `g'² = (ε/p) · 1` is central
  (`gPinv_sq`, `gP_sq_central`); equivalently `g'⁻¹ = s⁻¹ α₀ = [[-p, p ε], [1 - ε p, p]]` has
  integral entries, determinant `-p ε`, and `(g'⁻¹)² = p ε · 1`;
* **conjugation by `g'` maps the stabilizer `H = Γ₁'(3) ∩ Γ⁰(p)` of the base coset to itself**
  (`fricke : H →* H`, `embed (fricke h) = g' * embed h * g'⁻¹`, `fricke_fricke`), by the explicit
  formula `fricke [[a, p b'], [c, d]] = [[A, p B], [C, D]]` of `fA, fB, fC, fD`;
* it exchanges the cusp elements: `fricke (T^p) = s⁻¹ T s`, `fricke (s⁻¹ T s) = T^p`,
  `fricke L = s⁻¹ L^p s` and `fricke (s⁻¹ L^p s) = L` (the four cusp generators of
  `Γ₁'(3) ∩ Γ⁰(p)`: `T^p`, `L` and the transits `r_∞ T r_∞⁻¹`, `r_∞ L^p r_∞⁻¹` at `r_∞ = s⁻¹`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed integralEmbed_val)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets

section Entries

variable (p e a bp c d : ℤ)

/-- The entries of the conjugate `g' [[a, p b'], [c, d]] g'⁻¹ = [[A, p B], [C, D]]`. -/
def fA : ℤ := e * p * a - p * c - e * p * bp + p ^ 2 * bp + d - e * p * d

/-- The entry `B` (the upper right entry of the conjugate is `p B`). -/
def fB : ℤ := -a + e * c - e * p * bp + d

/-- The lower left entry `C` of the conjugate. -/
def fC : ℤ := p * a - 2 * p * bp - p * d + e * (-a + p ^ 2 * bp + bp - p * c + d)

/-- The lower right entry `D` of the conjugate. -/
def fD : ℤ := a - p ^ 2 * bp + p * c + e * (-p * a + p * bp + p * d)

variable {p e a bp c d}

theorem fricke_det (he : e * e = 1) :
    fA p e a bp c d * fD p e a bp c d - p * fB p e a bp c d * fC p e a bp c d =
      a * d - p * bp * c := by
  unfold fA fB fC fD
  linear_combination (p * (-a ^ 2 * p + a * bp * p + a * c + 2 * a * d * p + bp ^ 2 * p ^ 3 -
    2 * bp * c * p ^ 2 - bp * c - bp * d * p + c ^ 2 * p - c * d - d ^ 2 * p)) * he

/-- **The conjugation identity** `Ĝ C = E Ĝ`, `Ĝ = g'⁻¹ = [[-p, p ε], [1 - ε p, p]]`. -/
theorem fricke_conj (he : e * e = 1) :
    (!![-p, p * e; 1 - e * p, p] : Matrix (Fin 2) (Fin 2) ℤ) *
        !![fA p e a bp c d, p * fB p e a bp c d; fC p e a bp c d, fD p e a bp c d] =
      !![a, p * bp; c, d] * !![-p, p * e; 1 - e * p, p] := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  unfold fA fB fC fD
  exact mat2_eq (by linear_combination (p * (-a + bp * p ^ 2 + bp - c * p + d)) * he)
    (by linear_combination (-p ^ 2 * (a - bp - d)) * he)
    (by linear_combination (-p ^ 2 * (a - bp - d)) * he)
    (by linear_combination (p ^ 2 * (bp * p - c)) * he)

end Entries

section Elements

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- The sign `ε_p` as an integer. -/
abbrev eps : ℤ := ((signP p : ℤˣ) : ℤ)

theorem eps_mul_self : eps p * eps p = 1 := signP_mul_self p

include hp3 in
theorem eps_cast : ((eps p : ℤ) : ZMod 3) = p.val := signP_cast p hp3

include hp3 in
/-- **The Fricke element** `s = [[-ε, 1], [ε - p, p ε]] ∈ Γ₁'(3)`. -/
def sF : binaryArithmeticLevel :=
  matLevel (-(eps p)) 1 (eps p - p.val) (p.val * eps p) (-(eps p))
    (by linear_combination eps_mul_self p)
    (by linear_combination (-(p.val : ℤ)) * eps_mul_self p)
    (by
      push_cast
      rw [eps_cast p hp3, sub_self])
    (by
      push_cast
      rw [eps_cast p hp3]
      exact cast_mul_self p hp3)

include hp3 in
/-- **The inverse** `s⁻¹ = [[-p, ε], [1 - ε p, 1]]` of the Fricke element. -/
def sInv : binaryArithmeticLevel :=
  matLevel (-(p.val : ℤ)) (eps p) (1 - eps p * p.val) 1 (-(eps p))
    (by linear_combination eps_mul_self p)
    (by linear_combination (p.val : ℤ) * eps_mul_self p)
    (by
      push_cast
      rw [eps_cast p hp3, cast_mul_self p hp3, sub_self])
    (by simp)

theorem sF_val :
    (((sF p hp3).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-(eps p), 1; eps p - p.val, p.val * eps p] := rfl

theorem sInv_val :
    (((sInv p hp3).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-(p.val : ℤ), eps p; 1 - eps p * p.val, 1] := rfl

theorem sF_mul_sInv : sF p hp3 * sInv p hp3 = 1 := by
  have he := eps_mul_self p
  apply Subtype.ext
  apply Units.ext
  change (((sF p hp3).val * (sInv p hp3).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
    ((1 : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [Units.val_mul, sF_val, sInv_val, Matrix.mul_fin_two, Units.val_one, Matrix.one_fin_two]
  exact mat2_eq (by ring) (by linear_combination (-1 : ℤ) * he)
    (by linear_combination (-(p.val : ℤ) ^ 2) * he) (by linear_combination he)

theorem sInv_eq_inv : sInv p hp3 = (sF p hp3)⁻¹ := eq_inv_of_mul_eq_one_right (sF_mul_sInv p hp3)

theorem sF_eq_inv : sF p hp3 = (sInv p hp3)⁻¹ := by
  rw [sInv_eq_inv, inv_inv]

theorem sInv_mul_sF : sInv p hp3 * sF p hp3 = 1 := by
  rw [sInv_eq_inv, inv_mul_cancel]

end Elements

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets
