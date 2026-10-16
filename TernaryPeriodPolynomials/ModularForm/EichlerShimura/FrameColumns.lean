module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.SymRep

@[expose] public section


/-!
# The extreme columns of the Hodge frame

Foundation file of the unconditional Eichler--Shimura route.  The last column of `frameE m z` is the coefficient vector of `(zX₁ - X₀)^m`
(`frameE_last_eq_coords`) and the first column is that of `(z̄X₁ - X₀)^m`
(`frameE_zero_eq_coords`), the coordinatewise conjugate of the last (`frameE_zero_eq_conj`,
`coords_conj_pow`, `conj_smul_frameE_zero`).

Formalized by Claude Sonnet 5.5.
-/

open Complex MvPolynomial
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame

variable (m : ℕ)

/-- The last column of the Hodge frame is the coefficient vector of `(zX₁ - X₀)^m`. -/
theorem frameE_last_eq_coords (z : ℂ) :
    (fun i => frameE m z i (Fin.last m)) = coords m ((C z * X 1 - X 0) ^ m) := by
  funext i
  rw [frameE_eq_coords]
  simp [ehom]

/-- The first column of the Hodge frame is the coefficient vector of `(z̄X₁ - X₀)^m`. -/
theorem frameE_zero_eq_coords (z : ℂ) :
    (fun i => frameE m z i 0) = coords m ((C (starRingEnd ℂ z) * X 1 - X 0) ^ m) := by
  funext i
  rw [frameE_eq_coords]
  simp [ehom]

/-- The coefficient vector of `(z̄X₁ - X₀)^m` is the coordinatewise conjugate of that of
`(zX₁ - X₀)^m`. -/
theorem coords_conj_pow (z : ℂ) :
    coords m ((C (starRingEnd ℂ z) * X 1 - X 0) ^ m) =
      fun i => starRingEnd ℂ (coords m ((C z * X 1 - X 0) ^ m) i) := by
  have h : (C (starRingEnd ℂ z) * X 1 - X 0 : MvPolynomial (Fin 2) ℂ) ^ m =
      MvPolynomial.map (starRingEnd ℂ) ((C z * X 1 - X 0) ^ m) := by
    simp [map_pow, map_sub, map_mul]
  funext i
  unfold coords
  rw [h, MvPolynomial.coeff_map]

/-- The first column of the Hodge frame is the coordinatewise conjugate of the last. -/
theorem frameE_zero_eq_conj (z : ℂ) :
    (fun i => frameE m z i 0) = fun i => starRingEnd ℂ (frameE m z i (Fin.last m)) := by
  rw [frameE_zero_eq_coords, coords_conj_pow]
  funext i
  have := congrFun (frameE_last_eq_coords m z) i
  rw [this]

/-- The `dz̄`-part of the decoupling is the conjugate of the `dz`-type vector. -/
theorem conj_smul_frameE_zero (c z : ℂ) :
    starRingEnd ℂ c • (fun i => frameE m z i 0) =
      fun i => starRingEnd ℂ (c • frameE m z i (Fin.last m)) := by
  rw [frameE_zero_eq_conj]
  funext i
  simp

end TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
