module

public import TernaryPeriodPolynomials.ModularForm.Symbol.RationalMobius

@[expose] public section


noncomputable section
open Matrix

namespace TernaryPoly.BinaryCuspSymbol

/-- The two literal scalar-extension routes agree on actual integral special-linear matrices. -/
theorem complexify_slRational_val (g : SL2) :
    (complexify (slRational g)).val = g.val.map (Int.castRingHom ℂ) := by
  ext i j
  change (((g i j : ℤ) : ℚ) : ℂ) = (g i j : ℂ)
  norm_cast

/-- The genuine determinant-twisted function action reduces to inverse coordinates on SL2. -/
theorem functionAction_slRational (g : SL2) (F : Functions) (v : Coordinates) :
    functionAction (slRational g) F v = F (slCoordinates g⁻¹ v) := by
  change ((slRational g).det.val^(-1 : ℤ) : ℚ) •
    F (((complexify (slRational g))⁻¹).val.mulVec v) = _
  rw [slRational_det, _root_.one_zpow, one_smul, ←map_inv, ←map_inv, complexify_slRational_val]
  rfl

/-- The exact rational determinant-inverse factor in the actual function coefficient action. -/
theorem functionAction_apply (g : GL2) (F : Functions) (v : Coordinates) :
    functionAction g F v = ((g.det.val : ℂ)⁻¹) * F (((complexify g)⁻¹).val.mulVec v) := by
  change (g.det.val^(-1 : ℤ) : ℚ) • F (((complexify g)⁻¹).val.mulVec v) = _
  rw [_root_.zpow_neg_one, Algebra.smul_def, map_inv₀]
  rfl

end TernaryPoly.BinaryCuspSymbol
