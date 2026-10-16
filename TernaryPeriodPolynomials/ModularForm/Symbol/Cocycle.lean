module

public import TernaryPeriodPolynomials.Analysis.Scalar.EisensteinLevelThreeEichlerGeometry
public import TernaryPeriodPolynomials.ModularForm.Symbol.Primitive

@[expose] public section
noncomputable section
open Complex Matrix
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod

@[simp] theorem slConstant_one {d : ℕ} (f : Forms d) (v : Coordinates) :
    slConstant f 1 v = 0 := by
  simp [slConstant]

/-- The transformation constants satisfy the genuine coefficient-valued cocycle relation. -/
theorem slConstant_mul {d : ℕ} (f : Forms d) (g h : SL2) (v : Coordinates) :
    slConstant f (g*h) v = slConstant f g v + slConstant f h (slCoordinates g⁻¹ v) := by
  have hI : 0 < (I : ℂ).im := by simp
  unfold slConstant
  rw [slMobius_mul g h hI, eichlerIntegral_sl f g v (slMobius_im_pos h hI),
    _root_.mul_inv_rev, slCoordinates_mul]
  unfold slConstant
  ring

end TernaryPoly.BinaryCuspSymbol
