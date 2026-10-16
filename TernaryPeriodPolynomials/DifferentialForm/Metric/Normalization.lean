module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.BaseFrame
public import TernaryPeriodPolynomials.DifferentialForm.Metric.Diagonal

@[expose] public section


/-! The exact basepoint exterior metric is the factorial-weighted Hodge metric. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open Matrix SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceRiemannian PolynomialCoefficientMetric SL3PolynomialCoercivity

/-- Frame formula in every degree, with the exact exterior factorial. -/
theorem formPairing_basepoint_frame (n k : ℕ) (a b : FormValue n k) :
    formPairing n k (coordinateChart basepoint) a b =
      (k.factorial : ℝ)⁻¹ * ∑ I : Fin k → Fin 5, (∏ r, tangentWeight (I r)) *
        factorialPairing (a (fun r => baseFrame (I r))).val (b (fun r => baseFrame (I r))).val := by
  have hG : (Matrix.diagonal (fun i => (tangentWeight i)⁻¹)).PosDef :=
    Matrix.PosDef.diagonal (fun i => inv_pos.mpr (tangentWeight_pos i))
  have h := contraction_isometry (coordinateCoefficientBilin n (coordinateChart basepoint))
    (Matrix.diagonal (fun i => (tangentWeight i)⁻¹)) (coordinateGram (coordinateChart basepoint)) hG
    baseFrameMap baseFrame_gram a b
  rw [inverse_diagonal_pos tangentWeight tangentWeight_pos, tensorMatrix_diagonal,
    matrixContraction_diagonal] at h
  unfold formPairing inverseGram
  rw [← h]
  apply congrArg ((k.factorial : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro I _
  apply congrArg ((∏ r, tangentWeight (I r)) * ·)
  change coordinateCoefficientMetric n (coordinateChart basepoint)
    (a (fun r => baseFrameMap (Pi.single (I r) 1)))
    (b (fun r => baseFrameMap (Pi.single (I r) 1))) = _
  simp only [baseFrameMap_single, coefficientMetric_coordinates, coefficientMetric_basepoint]

/-- The actual B=tr coordinates of an exterior-degree-two coefficient form. -/
def baseTwoCoordinates {n : ℕ} (a : FormValue n 2) : TwoCoordinates :=
  fun i j => (a ![baseFrame i, baseFrame j]).val

/-- Equality with the 1/2-normalized Hodge metric, with no hidden rescaling. -/
theorem formPairing_basepoint_two (n : ℕ) (a b : FormValue n 2) :
    formPairing n 2 (coordinateChart basepoint) a b = twoPairing (baseTwoCoordinates a) (baseTwoCoordinates b) := by
  rw [formPairing_basepoint_frame]
  have he := (finTwoArrowEquiv (Fin 5)).symm.sum_comp
    (fun I : Fin 2 → Fin 5 => (∏ r, tangentWeight (I r)) *
      factorialPairing (a (fun r => baseFrame (I r))).val (b (fun r => baseFrame (I r))).val)
  rw [← he, Fintype.sum_prod_type]
  norm_num only [Nat.factorial, Nat.cast_ofNat]
  unfold twoPairing baseTwoCoordinates
  apply congrArg ((1/2 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [finTwoArrowEquiv_symm_apply, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have hv : (fun r : Fin 2 => baseFrame (![i, j] r)) = ![baseFrame i, baseFrame j] := by
    funext r; fin_cases r <;> rfl
  rw [hv]

theorem baseTwoCoordinates_alternating {n : ℕ} (a : FormValue n 2) :
    IsAlternatingTwo (baseTwoCoordinates a) := by
  intro i j
  have h := a.toAlternatingMap.map_swap ![baseFrame j, baseFrame i]
    (show (0 : Fin 2) ≠ 1 by decide)
  have he : (![baseFrame j, baseFrame i] ∘ Equiv.swap (0 : Fin 2) 1) = ![baseFrame i, baseFrame j] := by
    funext r; fin_cases r <;> rfl
  rw [he] at h
  exact congrArg Subtype.val h

/-- Comparison with the actual domain of the homogeneous Hodge operator. -/
def baseTwoForm (n : ℕ) : FormValue n 2 →ₗ[ℝ] homogeneousTwoForms n where
  toFun a := ⟨baseTwoCoordinates a, baseTwoCoordinates_alternating a,
    fun i j => (a ![baseFrame i, baseFrame j]).property⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem baseTwoForm_injective (n : ℕ) : Function.Injective (baseTwoForm n) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  have hz : formPairing n 2 (coordinateChart basepoint) a a = 0 := by
    rw [formPairing_basepoint_two]
    change twoPairing (baseTwoForm n a).val (baseTwoForm n a).val = 0
    rw [ha]
    simp [twoPairing]
  exact (formPairing_self_eq_zero n 2 _ (extract_mem basepoint) a).mp hz

/-- The finite-dimensional Hodge coercivity uses exactly the newly induced basepoint norm. -/
theorem homogeneousHodgeTwo_basepoint_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : FormValue n 2,
      c * formPairing n 2 (coordinateChart basepoint) a a ≤
        twoPairing (homogeneousHodgeTwo n (baseTwoForm n a)).val (baseTwoForm n a).val := by
  obtain ⟨c, hc, h⟩ := homogeneousHodgeTwo_coercive hn
  refine ⟨c, hc, fun a => ?_⟩
  rw [formPairing_basepoint_two]
  exact h (baseTwoForm n a)

end TernaryPoly.PolynomialFormMetric
