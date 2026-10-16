module

public import Mathlib

@[expose] public section


/-!
# The projection of `GL₃(ℝ)` to the plane symmetric space

For an invertible real `3 × 3` matrix `y`, the Gram matrix `S = y yᵀ` is positive definite and
depends only on the coset `y O(3)`. Writing `y = p k` with `p` in the plane parabolic and `k`
orthogonal, `S = p pᵀ`, and after normalizing the corner of `p` to `1` the radical part of `p` is
`x = S_{·2} / S₂₂` and the Levi part `A` satisfies `A Aᵀ ∝ M`, `M = S_{tl} - S_{·2} S_{·2}ᵀ / S₂₂`
(the Schur complement). The point `A · i` of the upper half plane is therefore
`z = (M₀₁ + i √det M) / M₁₁`. These formulas define a smooth map on all invertible matrices, with
no chart singularities.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

/-- The Gram matrix `y yᵀ`. -/
def gramMatrix (y : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := y * yᵀ

/-- The radical coordinate `S_{·2} / S₂₂` of the plane symmetric space. -/
def symmetricRadical (y : Matrix (Fin 3) (Fin 3) ℝ) : Fin 2 → ℝ :=
  fun i => gramMatrix y i.castSucc 2 / gramMatrix y 2 2

/-- The Schur complement `S_{tl} - S_{·2} S_{·2}ᵀ / S₂₂` of the Gram matrix. -/
def symmetricSchur (y : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => gramMatrix y i.castSucc j.castSucc -
    gramMatrix y i.castSucc 2 * gramMatrix y j.castSucc 2 / gramMatrix y 2 2

/-- The upper half plane point `(M₀₁ + i √det M) / M₁₁` of a positive definite `2 × 2` matrix. -/
def positivePoint (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ((M 0 1 : ℂ) + Complex.I * (Real.sqrt M.det : ℂ)) / (M 1 1 : ℂ)

/-- The Levi point of the plane symmetric space. -/
def symmetricPoint (y : Matrix (Fin 3) (Fin 3) ℝ) : ℂ := positivePoint (symmetricSchur y)

end TernaryPeriodPolynomials.AnalyticClasses
