module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Codifferential.LimitFormula
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientExtension
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.DoubleCutoffConvergence

@[expose] public section


/-! The true compact codifferential chart commutator converges in every scalar coordinate. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert CompactCoordinateIntegration
open scoped ContDiff Topology

theorem codifferentialCommutator_component_tendsto (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : Core n (k+1)) (i : Index n k) :
    Tendsto (fun j : ℕ => ∫ x, ‖components n k (globalChartRepresentative (deckRepresentation n) S k
      ((coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) w) -
        coreChartCodifferentialLimit n k S χ η hχ hη hcη hsη w).val).val i x‖^2) atTop (𝓝 0) := by
  have HB := exists_chart_buffer S χ η hcχ hsχ hcη hsη
  let θ : Coordinates → ℝ := HB.choose
  have hθ : ContDiff ℝ ∞ θ := HB.choose_spec.1
  have hcθ : HasCompactSupport θ := HB.choose_spec.2.1
  have hsθ : tsupport θ ⊆ (quotientChart S).target := HB.choose_spec.2.2.1
  have hθone : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1 := fun x hx => HB.choose_spec.2.2.2 x (Or.inl hx)
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
  let f := components n (k+1) (cutoffChartRaw n (k+1) S θ w.val)
  have hf (t : Index n (k+1)) : ContDiff ℝ 1 (f t) :=
    (contDiff_cutoffChartComponents n (k+1) S θ hθ hsθ w.val t).of_le (by simp)
  have HC := CompactScalarMollifier.matrix_double_cutoff_tendsto volume χ η
    (hχ.of_le (by simp)) hcχ (hη.of_le (by simp)) hcη v A B
    (fun j t q => (hab j t q.1 q.2.1 q.2.2).1.of_le (by simp))
    (fun j t q => (hab j t q.1 q.2.1 q.2.2).2.1.continuous)
    (fun j t q => hT.of_isClosed_subset (isClosed_tsupport _) (hab j t q.1 q.2.1 q.2.2).2.2.1)
    (fun j t q => hT.of_isClosed_subset (isClosed_tsupport _) (hab j t q.1 q.2.1 q.2.2).2.2.2) f hf i
  have hscale : Tendsto (fun j : ℕ => (j:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hL := codifferentialLimit_eq_matrix_symbol n k S χ η θ hχ hsχ hη hcη hsη hθ hsθ hθone
    K hKpos subset_union_right subset_union_left a b
    (fun x hx j t l j' d => ⟨(he x hx j t l j' d).1.self_of_nhds,(he x hx j t l j' d).2.self_of_nhds⟩) w i
  apply (HC.comp hscale).congr
  intro j
  have hC := codifferentialCommutator_eq_matrix n k S χ η θ hχ hcχ hsχ hη hcη hsη hθ hsθ hθone
    K hKpos subset_union_right subset_union_left a b
    (fun x hx j t l j' d => ⟨(he x hx j t l j' d).1.self_of_nhds,(he x hx j t l j' d).2.self_of_nhds⟩)
    ((j:ℝ)+1) (by positivity) w i
  have hsub := globalChartRepresentative_sub n k S
    (coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) w).val
    (coreChartCodifferentialLimit n k S χ η hχ hη hcη hsη w).val
  have hcomp := (congrArg (fun f => components n k f i) hsub).trans
    (congrFun (components_sub_function n k _ _) i)
  have H := hcomp.trans (congrArg₂ (fun u v : Coordinates → ℝ => u-v) hC hL)
  exact (congrArg (fun f : Coordinates → ℝ => ∫ x, ‖f x‖^2) H).symm

end TernaryPoly.PolynomialFormCoordinates
