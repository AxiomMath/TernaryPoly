module

public import TernaryPeriodPolynomials.ModularForm.Symbol.Endpoints

@[expose] public section


noncomputable section
open Complex Matrix MvPolynomial
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod BinaryModularSymbol RankTwoAugmentedFrames

/-- The integral chart of zero chosen to match the exact normalized inversion formula. -/
def zeroChart : SL2 := ⟨!![0,1;-1,0], by norm_num [Matrix.det_fin_two]⟩

theorem zeroChart_mobius (z : ℂ) : slMobius zeroChart z = -1/z := by
  simp [slMobius, zeroChart, div_neg, neg_div, one_div]

theorem zeroChart_inv_coordinates (v : Coordinates) :
    slCoordinates zeroChart⁻¹ v = ![-v 1,v 0] := by
  rw [slCoordinates_inv]
  simp [zeroChart]

theorem infinity_eq_augmentedLine : infinity = augmentedLine 1 0 := by
  apply Subtype.ext
  change Submodule.span ℚ {template 0} = Submodule.span ℚ {rationalRepresentation 1 (template 0)}
  simp

theorem zeroChart_line : lineAction (slRational zeroChart) infinity = augmentedLine 1 1 := by
  apply Subtype.ext
  rw [lineAction_infinity_val]
  change Submodule.span ℚ {fun i => (slRational zeroChart).val i 0} =
    Submodule.span ℚ {rationalRepresentation 1 (template 1)}
  simp only [map_one]
  change Submodule.span ℚ {fun i => (slRational zeroChart).val i 0} = Submodule.span ℚ {template 1}
  calc
    _ = Submodule.span ℚ {(-1 : ℚ) • template 1} := by
      apply congrArg (fun u : Fin 2 → ℚ => Submodule.span ℚ {u})
      funext i
      fin_cases i
      · change (0 : ℚ) = (-1)*0
        norm_num
      · change (-1 : ℚ) = (-1)*1
        norm_num
    _ = _ := Submodule.span_singleton_smul_eq (by norm_num) _

/-- The actual zero-cusp endpoint is the negative of the literal finite Mellin polynomial. -/
theorem endpoint_zero {d : ℕ} (hd : Even d) (f : Forms d) (v : Coordinates) :
    endpoint f (augmentedLine 1 1) v = -eval v (period f) := by
  rw [←zeroChart_line, endpoint_eq_slConstant, slConstant, zeroChart_mobius,
    zeroChart_inv_coordinates]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [eichlerIntegral_neg_inv hd f (v 0) (v 1) (by simp)]
  have hv : ![v 0,v 1] = v := by funext i; fin_cases i <;> rfl
  rw [hv]
  ring

end TernaryPoly.BinaryCuspSymbol
