module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Differential.LimitFormula
public import TernaryPeriodPolynomials.DifferentialForm.DifferentialCoefficientExtension
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.DoubleCutoffConvergence

@[expose] public section

/-! Scalar-component convergence of the actual differential commutator to the full double-cutoff symbol. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert CompactCoordinateIntegration
open scoped ContDiff Topology

theorem differentialCommutator_component_tendsto (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : Core n k) (i : Index n (k+1)) :
    Tendsto (fun j : ℕ => ∫ x, ‖
      components n (k+1) (globalChartRepresentative (deckRepresentation n) S (k+1)
        (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) w).val).val i x -
      components n (k+1) (globalChartRepresentative (deckRepresentation n) S (k+1)
        (coreChartDifferentialLimit n k S χ η hχ hη hcη hsη w).val).val i x‖^2)
      atTop (nhds 0) := by
  have HB := exists_chart_buffer S χ η hcχ hsχ hcη hsη
  let θ : Coordinates → ℝ := HB.choose
  have hθ : ContDiff ℝ ∞ θ := HB.choose_spec.1
  have hcθ : HasCompactSupport θ := HB.choose_spec.2.1
  have hsθ : tsupport θ ⊆ (quotientChart S).target := HB.choose_spec.2.2.1
  have hθone : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1 := fun x hx => HB.choose_spec.2.2.2 x (Or.inl hx)
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
  let f := components n k (cutoffChartRaw n k S θ w.val)
  have hf (t : Index n k) : ContDiff ℝ 1 (f t) :=
    (contDiff_cutoffChartComponents n k S θ hθ hsθ w.val t).of_le (by simp)
  have H := CompactScalarMollifier.matrix_double_cutoff_tendsto volume χ η
    (hχ.of_le (by simp)) hcχ (hη.of_le (by simp)) hcη v a B
    (fun j t d => (ha j t d).1.of_le (by simp)) (fun _ _ _ => continuous_const)
    (fun j t d => hT.of_isClosed_subset (isClosed_tsupport _) (ha j t d).2)
    (fun _ _ _ => by simp [B, HasCompactSupport]) f hf i
  have hscale : Tendsto (fun j : ℕ => (j:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have HF (j : ℕ) := differentialCommutator_eq_matrix n k S χ η θ hχ hcχ hsχ hη hcη hsη hθ hsθ
    hθone K subset_union_right subset_union_left a
    (fun x hx l t d => (he x hx l t d).self_of_nhds) ((j:ℝ)+1) (by positivity) w i
  have HL := differentialLimit_eq_symbol n k S χ η θ hχ hsχ hη hcη hsη hθ hsθ
    hθone K subset_union_right subset_union_left a
    (fun x hx l t d => (he x hx l t d).self_of_nhds) w i
  exact (H.comp hscale).congr (fun j =>
    (congrArg₂ (fun p q : Coordinates → ℝ => ∫ x, ‖p x - q x‖^2) (HF j) HL).symm)

end TernaryPoly.PolynomialFormCoordinates
