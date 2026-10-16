module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Coefficients
public import Mathlib.Data.ZMod.Basic

@[expose] public section


/-!
# The arithmetic congruence level

These are literal matrix groups and maps. The finite level fixes the last row
modulo three; its rational image acts in the cochain complexes below.
-/


noncomputable section

namespace GeneralEisenstein

open Matrix

abbrev IntegralGL3 := GeneralLinearGroup (Fin 3) ℤ
abbrev RationalGL3 := GeneralLinearGroup (Fin 3) ℚ

/-- Reduction of an invertible integral matrix modulo three. -/
def reductionThree : IntegralGL3 →* GeneralLinearGroup (Fin 3) (ZMod 3) :=
  GeneralLinearGroup.map (Int.castRingHom (ZMod 3))

/-- The covector `e₃*`, with zero-based coordinate indices. -/
def lastRow : Fin 3 → ZMod 3 := Pi.single 2 1

/-- The actual row stabilizer in `GL₃(ℤ/3ℤ)`. -/
def rowStabilizer : Subgroup (GeneralLinearGroup (Fin 3) (ZMod 3)) where
  carrier := {g | lastRow ᵥ* g.val = lastRow}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change lastRow ᵥ* (g.val * h.val) = lastRow
    rw [← vecMul_vecMul, hg, hh]
  inv_mem' {g} hg := by
    change lastRow ᵥ* (g⁻¹).val = lastRow
    have h := congrArg (fun v => v ᵥ* (g⁻¹).val) hg
    simpa only [vecMul_vecMul, ← GeneralLinearGroup.coe_mul,
      mul_inv_cancel, GeneralLinearGroup.coe_one, vecMul_one] using h.symm

/-- `Γ = {g ∈ GL₃(ℤ) | e₃*g = e₃* mod 3}`, the paper's finite level. -/
def arithmeticLevel : Subgroup IntegralGL3 := rowStabilizer.comap reductionThree

/-- The inclusion of the arithmetic level into rational matrices. -/
def rationalInclusion : arithmeticLevel →* RationalGL3 :=
  (GeneralLinearGroup.map (Int.castRingHom ℚ)).comp arithmeticLevel.subtype

end GeneralEisenstein

end
