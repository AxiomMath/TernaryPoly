module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Differential.CommutatorFormula
public import TernaryPeriodPolynomials.DifferentialForm.DifferentialCoefficientExtension
public import TernaryPeriodPolynomials.DifferentialForm.Chart.InputBound
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.DoubleCutoffBound

@[expose] public section


/-! Uniform actual Hilbert-input bounds for every component of the differential chart commutator. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert CompactCoordinateIntegration
open scoped ContDiff Topology

theorem exists_differentialCommutator_component_bound (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (i : Index n (k+1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (hc : 0 < c) (w : Core n k),
      ∫ x, ‖components n (k+1) (globalChartRepresentative (deckRepresentation n) S (k+1)
        (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w).val).val i x‖^2 ≤
      C * ‖inclusion n k w‖^2 := by
  have HB := exists_chart_buffer S χ η hcχ hsχ hcη hsη
  let θ : Coordinates → ℝ := HB.choose
  have hθ : ContDiff ℝ ∞ θ := HB.choose_spec.1
  have hcθ : HasCompactSupport θ := HB.choose_spec.2.1
  have hsθ : tsupport θ ⊆ (quotientChart S).target := HB.choose_spec.2.2.1
  have hθone : ∀ x ∈ tsupport χ ∪ tsupport η, θ =ᶠ[𝓝 x] 1 := HB.choose_spec.2.2.2
  let K := tsupport θ ∪ tsupport η
  have hK : IsCompact K := hcθ.union hcη
  have hKpos : K ⊆ positiveCoordinates := (union_subset hsθ hsη).trans (quotientChart_target_subset S)
  have HE := exists_differential_coefficient_extensions n k hK hKpos
  let a := HE.choose
  let T := HE.choose_spec.choose
  have hT : IsCompact T := HE.choose_spec.choose_spec.1
  have ha := HE.choose_spec.choose_spec.2.2.1
  have he := HE.choose_spec.choose_spec.2.2.2
  let v := fun d : Fin 5 => (Pi.single d 1 : Coordinates)
  let B : Index n (k+1) → Index n k → Fin 5 → Coordinates → ℝ := fun _ _ _ _ => 0
  have HC := CompactScalarMollifier.matrix_double_cutoff_uniform volume χ η
    (hχ.of_le (by simp)) hcχ (hη.of_le (by simp)) hcη v a B
    (fun j t d => (ha j t d).1.of_le (by simp)) (fun _ _ _ => continuous_const)
    (fun j t d => hT.of_isClosed_subset (isClosed_tsupport _) (ha j t d).2)
    (fun _ _ _ => by simp [B, HasCompactSupport]) i
  let C : ℝ := HC.choose
  have hC : 0 ≤ C := HC.choose_spec.1
  have HI := exists_chart_input_bound n k S θ hθ hcθ hsθ
  let D : ℝ := HI.choose
  have hD : 0 ≤ D := HI.choose_spec.1
  refine ⟨C*D,mul_nonneg hC hD,fun c hc w => ?_⟩
  have hf (t : Index n k) := (contDiff_cutoffChartComponents n k S θ hθ hsθ w.val t).of_le
    (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hcf (t : Index n k) := compact_cutoffChartComponents n k S θ hcθ w.val t
  have H := HC.choose_spec.2 (components n k (cutoffChartRaw n k S θ w.val)) hf hcf c hc
  have HF := differentialCommutator_eq_matrix n k S χ η θ hχ hcχ hsχ hη hcη hsη hθ hsθ
    (fun x hx => hθone x (Or.inl hx)) K subset_union_right subset_union_left a
    (fun x hx j t d => (he x hx j t d).self_of_nhds) c hc w i
  have H0 := (congrArg (fun f : Coordinates → ℝ => ∫ x, ‖f x‖^2) HF).le.trans H
  exact H0.trans ((mul_le_mul_of_nonneg_left (HI.choose_spec.2 w) hC).trans_eq (mul_assoc C D _).symm)

end TernaryPoly.PolynomialFormCoordinates
