module

public import TernaryPeriodPolynomials.ModularForm.BinaryCuspOuter
public import TernaryPeriodPolynomials.ModularForm.Hecke.Roots

@[expose] public section


noncomputable section
open Complex
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace TernaryPoly.BinaryCuspHecke
open BinaryCuspPeriod

/-- The literal point `p*z` of the upper half plane. -/
def dilate (p : ℕ) (hp : 0 < p) (z : ℍ) : ℍ :=
  ⟨(p : ℂ) * z, by simpa using mul_pos (show (0 : ℝ) < p by exact_mod_cast hp) z.im_pos⟩

/-- The literal point `(z+b)/p` of the upper half plane. -/
def divideTranslate (p : ℕ) (hp : 0 < p) (b : Fin p) (z : ℍ) : ℍ :=
  ⟨((z : ℂ) + b.val) / p, by
    simpa using div_pos z.im_pos (show (0 : ℝ) < p by exact_mod_cast hp)⟩

@[simp] theorem coe_dilate (p : ℕ) (hp : 0 < p) (z : ℍ) :
    (dilate p hp z : ℂ) = (p : ℂ) * z := rfl

@[simp] theorem coe_divideTranslate (p : ℕ) (hp : 0 < p) (b : Fin p) (z : ℍ) :
    (divideTranslate p hp b z : ℂ) = ((z : ℂ) + b.val) / p := rfl

/-- The standard weight-`d+2` prime Hecke expression, on actual cusp-form values. -/
def primeOperator {d : ℕ} (p : ℕ) (hp : 0 < p) (f : Forms d) (z : ℍ) : ℂ :=
  (p : ℂ) ^ (d+1) * f (dilate p hp z) +
    (1 / (p : ℂ)) * ∑ b : Fin p, f (divideTranslate p hp b z)

/-- Width-one Fourier parameter. -/
def q (z : ℍ) : ℂ := Function.Periodic.qParam 1 z

@[simp] theorem q_dilate (p : ℕ) (hp : 0 < p) (z : ℍ) :
    q (dilate p hp z) = q z ^ p := by
  simp only [q, Function.Periodic.qParam, ofReal_one, div_one, coe_dilate]
  rw [← exp_nat_mul]
  congr 1
  ring

/-- Translation decomposes into the base divided parameter and a literal root of unity. -/
theorem q_divideTranslate (p : ℕ) (hp : 0 < p) (b : Fin p) (z : ℍ) :
    q (divideTranslate p hp b z) =
      q (divideTranslate p hp ⟨0, hp⟩ z) * root p ^ b.val := by
  simp only [q, Function.Periodic.qParam, ofReal_one, div_one, coe_divideTranslate,
    Nat.cast_zero, add_zero, root, ← exp_nat_mul, ← exp_add]
  congr 1
  ring

/-- Raising the divided Fourier parameter to the p-th power restores the original parameter. -/
theorem q_divide_pow (p : ℕ) (hp : 0 < p) (z : ℍ) :
    q (divideTranslate p hp ⟨0, hp⟩ z) ^ p = q z := by
  simp only [q, Function.Periodic.qParam, ofReal_one, div_one, coe_divideTranslate,
    Nat.cast_zero, add_zero, ← exp_nat_mul]
  congr 1
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  field_simp

/-- The actual cusp q-expansion sums at every upper-half-plane point. -/
theorem hasSum_coefficients {d : ℕ} (f : Forms d) (z : ℍ) :
    HasSum (fun n => coefficients f n * q z ^ n) (f z) := by
  have h := ModularForm.hasSum_qExpansion f (Subgroup.strictWidthInfty_pos 𝒮ℒ)
    (Subgroup.strictWidthInfty_mem_strictPeriods 𝒮ℒ) z
  simpa [Subgroup.strictWidthInfty_SL2Z, coefficients, q, smul_eq_mul] using h

end TernaryPoly.BinaryCuspHecke
