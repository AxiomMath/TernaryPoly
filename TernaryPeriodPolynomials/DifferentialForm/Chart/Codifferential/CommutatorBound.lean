module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Codifferential.CommutatorFormula
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientExtension
public import TernaryPeriodPolynomials.DifferentialForm.Chart.InputBound
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.DoubleCutoffBound

@[expose] public section

/-! Uniform actual Hilbert-input bounds for every scalar component of the chart codifferential commutator. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert CompactCoordinateIntegration
open scoped ContDiff Topology

theorem exists_codifferentialCommutator_component_bound (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (i : Index n k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (hc : 0 < c) (w : Core n (k+1)),
      ∫ x, ‖components n k (globalChartRepresentative (deckRepresentation n) S k
        (coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w).val).val i x‖^2 ≤
      C * ‖inclusion n (k+1) w‖^2 := by
  have HB := exists_chart_buffer S χ η hcχ hsχ hcη hsη
  let θ : Coordinates → ℝ := HB.choose
  have hθ : ContDiff ℝ ∞ θ := HB.choose_spec.1
  have hcθ : HasCompactSupport θ := HB.choose_spec.2.1
  have hsθ : tsupport θ ⊆ (quotientChart S).target := HB.choose_spec.2.2.1
  have hθone : ∀ x ∈ tsupport χ ∪ tsupport η, θ =ᶠ[𝓝 x] 1 := HB.choose_spec.2.2.2
  let K := tsupport θ ∪ tsupport η
  have hK : IsCompact K := hcθ.union hcη
  have hKpos : K ⊆ positiveCoordinates := (union_subset hsθ hsη).trans (quotientChart_target_subset S)
  have HE := exists_adjoint_coefficient_extensions n k hK hKpos
  let a := HE.choose
  let b := HE.choose_spec.choose
  let T := HE.choose_spec.choose_spec.choose
  have hT : IsCompact T := HE.choose_spec.choose_spec.choose_spec.1
  have hab := HE.choose_spec.choose_spec.choose_spec.2.2.1
  have he := HE.choose_spec.choose_spec.choose_spec.2.2.2
  let v := fun q : Index n k × Index n (k+1) × Fin 5 => (Pi.single q.2.2 1 : Coordinates)
  let A := fun i t (q : Index n k × Index n (k+1) × Fin 5) => a i t q.1 q.2.1 q.2.2
  let B := fun i t (q : Index n k × Index n (k+1) × Fin 5) => b i t q.1 q.2.1 q.2.2
  have HC := CompactScalarMollifier.matrix_double_cutoff_uniform volume χ η
    (hχ.of_le (by simp)) hcχ (hη.of_le (by simp)) hcη v A B
    (fun j t q => (hab j t q.1 q.2.1 q.2.2).1.of_le (by simp))
    (fun j t q => (hab j t q.1 q.2.1 q.2.2).2.1.continuous)
    (fun j t q => hT.of_isClosed_subset (isClosed_tsupport _) (hab j t q.1 q.2.1 q.2.2).2.2.1)
    (fun j t q => hT.of_isClosed_subset (isClosed_tsupport _) (hab j t q.1 q.2.1 q.2.2).2.2.2) i
  let C : ℝ := HC.choose
  have hC : 0 ≤ C := HC.choose_spec.1
  have HI := exists_chart_input_bound n (k+1) S θ hθ hcθ hsθ
  let D : ℝ := HI.choose
  have hD : 0 ≤ D := HI.choose_spec.1
  refine ⟨C*D,mul_nonneg hC hD,fun c hc w => ?_⟩
  have hf (t : Index n (k+1)) := (contDiff_cutoffChartComponents n (k+1) S θ hθ hsθ w.val t).of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hcf (t : Index n (k+1)) := compact_cutoffChartComponents n (k+1) S θ hcθ w.val t
  have H := HC.choose_spec.2 (components n (k+1) (cutoffChartRaw n (k+1) S θ w.val)) hf hcf c hc
  have HE := codifferentialCommutator_eq_matrix n k S χ η θ hχ hcχ hsχ hη hcη hsη hθ hsθ
    (fun x hx => hθone x (Or.inl hx)) K hKpos subset_union_right subset_union_left a b
    (fun x hx j t l j' d => ⟨(he x hx j t l j' d).1.self_of_nhds,(he x hx j t l j' d).2.self_of_nhds⟩)
    c hc w i
  have H0 := (congrArg (fun f : Coordinates → ℝ => ∫ x, ‖f x‖^2) HE).le.trans H
  exact H0.trans ((mul_le_mul_of_nonneg_left (HI.choose_spec.2 w) hC).trans_eq (mul_assoc C D _).symm)

end TernaryPoly.PolynomialFormCoordinates
