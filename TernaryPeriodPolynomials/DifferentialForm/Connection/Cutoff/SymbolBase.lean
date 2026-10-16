module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.RealPullback
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingScalar
public import TernaryPeriodPolynomials.Analysis.PositiveBilinearFinite
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

@[expose] public section


/-! Quantitative scalar exterior symbols in the actual fixed basepoint form metric. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Matrix SmoothDeRhamGluing PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
  SymmetricSpaceRiemannian ContinuousAlternatingMap
open scoped Matrix.Norms.Elementwise

theorem scalarWedge_norm_le (n k : ℕ) (α : Coordinates →L[ℝ] ℝ) (a : FormValue n k) :
    ‖scalarWedge α a‖ ≤ ((k : ℝ) + 1) * ‖α‖ * ‖a‖ := by
  have h := norm_alternatizeUncurryFin_le (α.smulRight a)
  simpa only [scalarWedge, ContinuousLinearMap.norm_smulRight_apply, mul_assoc] using h

/-- Coordinate operator norm is bounded by the sum of values on the five coordinate vectors. -/
theorem covector_norm_le_sum (α : Coordinates →L[ℝ] ℝ) :
    ‖α‖ ≤ ∑ i : Fin 5, |α (Pi.single i 1)| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  intro v
  have hv : v = ∑ i : Fin 5, v i • Pi.single i 1 := by ext i; simp [Pi.single_apply]
  calc
    ‖α v‖ = |∑ i : Fin 5, v i * α (Pi.single i 1)| := by
      conv_lhs => rw [hv, _root_.map_sum]
      simp only [map_smul, smul_eq_mul, Real.norm_eq_abs]
    _ ≤ ∑ i : Fin 5, |v i * α (Pi.single i 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 5, ‖v‖ * |α (Pi.single i 1)| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
        (abs_nonneg _)
    _ = (∑ i : Fin 5, |α (Pi.single i 1)|) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]

/-- One fixed finite coordinate constant compares true metric covector bounds at the basepoint. -/
def baseCovectorConstant : ℝ :=
  ∑ i : Fin 5, Real.sqrt (coordinatePair (coordinateChart basepoint) (Pi.single i 1) (Pi.single i 1))

theorem baseCovectorConstant_nonneg : 0 ≤ baseCovectorConstant :=
  Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)

theorem base_covector_norm_bound (α : Coordinates →L[ℝ] ℝ) {B : ℝ}
    (hα : ∀ v, |α v| ≤ B * Real.sqrt (coordinatePair (coordinateChart basepoint) v v)) :
    ‖α‖ ≤ B * baseCovectorConstant := by
  apply (covector_norm_le_sum α).trans
  calc
    _ ≤ ∑ i : Fin 5, B * Real.sqrt
        (coordinatePair (coordinateChart basepoint) (Pi.single i 1) (Pi.single i 1)) :=
      Finset.sum_le_sum (fun i _ => hα (Pi.single i 1))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Fixed basepoint form norms give one genuine metric bound for scalar exterior multiplication. -/
theorem exists_base_scalarWedge_bound (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ), 0 ≤ B → ∀ (α : Coordinates →L[ℝ] ℝ),
      (∀ v, |α v| ≤ B * Real.sqrt (coordinatePair (coordinateChart basepoint) v v)) →
      ∀ a : FormValue n k,
        formPairing n (k + 1) (coordinateChart basepoint) (scalarWedge α a) (scalarWedge α a) ≤
          C * B ^ 2 * formPairing n k (coordinateChart basepoint) a a := by
  let y := coordinateChart basepoint
  obtain ⟨d, hd, hl⟩ := PositiveBilinearFinite.exists_pos_lower_bound (E := FormValue n k)
    (formContinuousBilin n k y) (fun a ha => formPairing_positive n k y (extract_mem basepoint) a ha)
  let M := ‖formContinuousBilin n (k + 1) y‖
  have hM : 0 ≤ M := norm_nonneg _
  let W : ℝ := ((k : ℝ) + 1) * baseCovectorConstant
  have hW : 0 ≤ W := mul_nonneg (by positivity) baseCovectorConstant_nonneg
  refine ⟨M * W ^ 2 / d, by positivity, fun B hB α hα a => ?_⟩
  have hn : ‖scalarWedge α a‖ ≤ W * B * ‖a‖ := by
    calc
      _ ≤ ((k : ℝ) + 1) * ‖α‖ * ‖a‖ := scalarWedge_norm_le n k α a
      _ ≤ ((k : ℝ) + 1) * (B * baseCovectorConstant) * ‖a‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (base_covector_norm_bound α hα)
          (by positivity)) (norm_nonneg a)
      _ = _ := by dsimp only [W]; ring
  calc
    _ ≤ |formPairing n (k + 1) y (scalarWedge α a) (scalarWedge α a)| := le_abs_self _
    _ ≤ M * ‖scalarWedge α a‖ * ‖scalarWedge α a‖ :=
      by simpa only [Real.norm_eq_abs, formContinuousBilin_apply] using
        (formContinuousBilin n (k + 1) y).le_opNorm₂ (scalarWedge α a) (scalarWedge α a)
    _ = M * ‖scalarWedge α a‖ ^ 2 := by ring
    _ ≤ M * (W * B * ‖a‖) ^ 2 :=
      mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn) hM
    _ = (M * W ^ 2 / d) * B ^ 2 * (d * ‖a‖ ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hl a) (by positivity)

end TernaryPoly.PolynomialFormConnection
