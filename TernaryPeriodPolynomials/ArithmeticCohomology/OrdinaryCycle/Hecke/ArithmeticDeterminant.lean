module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.ArithmeticFiniteIndex
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHeckeArithmetic
open Matrix PolynomialGLAction ModThreeGoodAction

/-- For a conjugate of an integral unit, integral entries already force an integral inverse. -/
theorem conjugate_mem_iff_integralEntries (g : GL3) (k : IntegralGL) :
    g⁻¹*integral k*g ∈ Gamma ↔ IntegralEntries (g⁻¹*integral k*g).val := by
  constructor
  · intro h
    exact ((mem_Gamma_iff _).mp h).1
  · intro h
    obtain ⟨A,hA⟩ := (integralEntries_iff_matrix _).mp h
    have hd : A.det=k.val.det := by
      apply Int.cast_injective (α := ℚ)
      change (Int.castRingHom ℚ) A.det=(Int.castRingHom ℚ) k.val.det
      rw [(Int.castRingHom ℚ).map_det,(Int.castRingHom ℚ).map_det]
      change (matrixCast A).det=(integral k).val.det
      rw [hA,Units.val_mul,Units.val_mul,Matrix.det_mul,Matrix.det_mul]
      rw [mul_comm (g⁻¹).val.det (integral k).val.det,mul_assoc,←Matrix.det_mul]
      rw [show (g⁻¹).val*g.val=1 from g.inv_val,Matrix.det_one,mul_one]
    have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (hd ▸ Matrix.isUnits_det_units k)
    obtain ⟨u,hu⟩ := hu
    refine ⟨u,?_⟩
    apply Units.ext
    change matrixCast u.val=(g⁻¹*integral k*g).val
    rw [hu,hA]

/-- Rational division by a nonzero natural number is integral exactly at integer multiples. -/
theorem integer_div_iff (p : ℕ) (hp : p ≠ 0) (a : ℤ) :
    (∃ z : ℤ, (z : ℚ)=(a : ℚ)/(p : ℚ)) ↔ (p : ℤ) ∣ a := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    have he := (eq_div_iff hpq).mp hz
    rw [mul_comm] at he
    exact he.symm
  · rintro ⟨z,rfl⟩
    refine ⟨z,?_⟩
    push_cast
    field_simp

end TernaryPoly.OrdinaryHeckeArithmetic
