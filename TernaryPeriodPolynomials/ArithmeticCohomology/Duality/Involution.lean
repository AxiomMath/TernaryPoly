module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.FullBoundary

@[expose] public section


/-!
# The level-preserving outer involution of `GL₃(ℚ)`

`dualInvolution g = a (g⁻¹)ᵀ a⁻¹` with `a = diag(1, 1, 3)`. The inverse transpose turns the
last-row condition defining the arithmetic level into a last-column condition, and conjugation by
`a` turns it back. The involution exchanges plane and line parabolics up to the long Weyl element,
and the coefficient system composed with it is the contragredient one.
-/

noncomputable section

open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.Duality

/-- The inverse transpose, an automorphism of `GL₃(ℚ)`. -/
def inverseTranspose : RationalGL3 →* RationalGL3 where
  toFun g :=
    ⟨(g⁻¹).val.transpose, g.val.transpose, by
      rw [← Matrix.transpose_mul]
      simpa only [Matrix.transpose_one] using congrArg Matrix.transpose g.mul_inv,
      by
      rw [← Matrix.transpose_mul]
      simpa only [Matrix.transpose_one] using congrArg Matrix.transpose g.inv_mul⟩
  map_one' := by
    apply Units.ext
    exact Matrix.transpose_one
  map_mul' g h := by
    apply Units.ext
    exact Matrix.transpose_mul (h⁻¹).val (g⁻¹).val

/-- The diagonal matrix `diag(1, 1, 3)`. -/
def levelScale : RationalGL3 :=
  ⟨Matrix.diagonal ![1, 1, 3], Matrix.diagonal ![1, 1, 1 / 3], by
    rw [Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> norm_num, by
    rw [Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> norm_num⟩

/-- The level-preserving involution `g ↦ a (g⁻¹)ᵀ a⁻¹`. -/
def dualInvolution : RationalGL3 →* RationalGL3 :=
  (MulAut.conj levelScale).toMonoidHom.comp inverseTranspose

theorem dualInvolution_apply (g : RationalGL3) :
    dualInvolution g = levelScale * inverseTranspose g * levelScale⁻¹ := rfl

end TernaryPeriodPolynomials.Duality
