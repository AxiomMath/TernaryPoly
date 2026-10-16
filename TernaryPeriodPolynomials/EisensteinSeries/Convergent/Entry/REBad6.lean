module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBad1

@[expose] public section


/-!
# R-e: The other line orbit

`otherOrbit_support`: at the representative `g = 1` of the other line orbit the bad-plane weight along the radical is not supported on `(3ℤ₃)²` (the point `(0, 1/3)`), so the `1/9` computation of `g₀` does not apply there and nothing is asserted off the good-line orbit.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The lower unipotent `[[1,0,0],[0,1,0],[3,0,1]]` over `ℤ₃`; it lies in the level subgroup `K₁`. -/
def levelWitnessInt : GeneralLinearGroup (Fin 3) ℤ_[3] :=
  ⟨!![1,0,0;0,1,0;3,0,1], !![1,0,0;0,1,0;-3,0,1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def levelWitness : LocalThreeGL := GeneralLinearGroup.map PadicInt.Coe.ringHom levelWitnessInt

theorem levelWitness_level : InLocalThreeLevel levelWitness := by
  refine ⟨levelWitnessInt, ?_, rfl⟩
  funext j
  fin_cases j <;>
    simp [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three, levelWitnessInt, GeneralLinearGroup.map_apply]
  all_goals
    have h3 : (3 : ZMod 3) = 0 := by decide
    have := map_natCast (PadicInt.toZMod (p := 3)) 3
    simpa [h3] using this

theorem levelWitness_inv_val : (levelWitness⁻¹).val = !![1,0,0;0,1,0;-3,0,1] := by
  have : levelWitness⁻¹ = GeneralLinearGroup.map PadicInt.Coe.ringHom levelWitnessInt⁻¹ := by
    simp [levelWitness, map_inv]
  rw [this]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.map_apply, levelWitnessInt, map_ofNat, map_neg]

/-- **The other line orbit.**  At the representative `g = 1` of the other line orbit, the matrix `w⁻¹u(0, 1/3)`
lies in `P(ℚ₃)K₁`, although `(0, 1/3) ∉ 3ℤ₃ × 3ℤ₃`: the support of the bad-plane section along the radical is not
the box `(3ℤ₃)²` there (it is `{|t|₃ ≥ 3, |s|₃ ≤ |t|₃/3}`), so the computation of the value `1/9` at `g₀` does not
apply at that orbit. -/
theorem otherOrbit_support :
    badPlaneSet (weyl⁻¹ * lineUnipotent (0 : ℚ_[3]) (1 / 3) * 1) ∧ ¬ (‖(0 : ℚ_[3])‖ < 1 ∧ ‖(1 / 3 : ℚ_[3])‖ < 1) := by
  constructor
  · refine ⟨⟨weyl⁻¹ * lineUnipotent (0 : ℚ_[3]) (1 / 3) * levelWitness⁻¹, ?_⟩, levelWitness,
      levelWitness_level, ?_⟩
    · constructor
      · rw [Units.val_mul, levelWitness_inv_val]
        simp [weyl, lineUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]
      · rw [Units.val_mul, levelWitness_inv_val]
        simp [weyl, lineUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]
    · simp
  · rintro ⟨_, h⟩
    have : ‖(1 / 3 : ℚ_[3])‖ = 3 := by
      rw [norm_div, norm_one]
      have h := Padic.norm_p (p := 3)
      rw [Nat.cast_ofNat] at h
      rw [h]
      norm_num
    rw [this] at h
    norm_num at h

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
