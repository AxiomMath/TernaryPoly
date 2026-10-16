module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# R-e: Matrix identities for the equivariance of the entry integral

`weyl_inv_lineUnipotent_mul_lineLevi`: `w⁻¹ u(s,t) lineLevi(d,A) = planeLevi(A,d) · w⁻¹ u(d⁻¹(s,t)A)`.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- Moving a radical element across a line Levi element. -/
theorem lineUnipotent_mul_lineLevi {R : Type*} [CommRing R] (s t : R) (d : Rˣ)
    (A : GeneralLinearGroup (Fin 2) R) :
    lineUnipotent s t * lineLevi d A =
      lineLevi d A * lineUnipotent ((d⁻¹).val * (s * A.val 0 0 + t * A.val 1 0))
        ((d⁻¹).val * (s * A.val 0 1 + t * A.val 1 1)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lineLevi_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

/-- The key matrix identity of the equivariance of the entry integral: moving the line radical element
through a line parabolic element `lineLevi d A * u(s'', t'')` produces the plane Levi element `planeLevi A d`
on the left, and an affine change of the radical coordinates. -/
theorem weyl_inv_lineUnipotent_mul_lineParabolic {R : Type*} [CommRing R] (s t s'' t'' : R) (d : Rˣ)
    (A : GeneralLinearGroup (Fin 2) R) :
    weyl⁻¹ * lineUnipotent s t * (lineLevi d A * lineUnipotent s'' t'') =
      planeLevi A d * (weyl⁻¹ * lineUnipotent
        ((d⁻¹).val * (s * A.val 0 0 + t * A.val 1 0) + s'')
        ((d⁻¹).val * (s * A.val 0 1 + t * A.val 1 1) + t'')) := by
  rw [mul_assoc, ← mul_assoc (lineUnipotent s t), lineUnipotent_mul_lineLevi, mul_assoc (lineLevi d A),
    ← lineUnipotent_add, ← mul_assoc (weyl⁻¹), weyl_inverse_lineLevi, mul_assoc]

/-- The same identity with the Levi element only. -/
theorem weyl_inv_lineUnipotent_mul_lineLevi {R : Type*} [CommRing R] (s t : R) (d : Rˣ)
    (A : GeneralLinearGroup (Fin 2) R) :
    weyl⁻¹ * lineUnipotent s t * lineLevi d A =
      planeLevi A d * (weyl⁻¹ * lineUnipotent ((d⁻¹).val * (s * A.val 0 0 + t * A.val 1 0))
        ((d⁻¹).val * (s * A.val 0 1 + t * A.val 1 1))) := by
  rw [mul_assoc, lineUnipotent_mul_lineLevi, ← mul_assoc (weyl⁻¹), weyl_inverse_lineLevi, mul_assoc]

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
