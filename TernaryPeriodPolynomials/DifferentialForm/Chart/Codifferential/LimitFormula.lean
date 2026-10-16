module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Codifferential.Limit
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Codifferential.CommutatorFormula
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.CutoffSymbol

@[expose] public section


/-! The actual compact cutoff commutator equals both principal-symbol cutoff terms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert CompactCoordinateIntegration
open scoped ContDiff Topology

theorem codifferentialLimit_eq_matrix_symbol (n k : ℕ) (S : Space) (χ η θ : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (hθ : ContDiff ℝ ∞ θ) (hsθ : tsupport θ ⊆ (quotientChart S).target)
    (hθone : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1)
    (K : Set Coordinates) (hKpos : K ⊆ positiveCoordinates) (hηK : tsupport η ⊆ K) (hθK : tsupport θ ⊆ K)
    (a b : Index n k → Index n (k+1) → Index n k → Index n (k+1) → Fin 5 → Coordinates → ℝ)
    (hab : ∀ x ∈ K, ∀ i t l j d,
      a i t l j d x = adjointFirstCoefficient n k i t l j d x ∧
      b i t l j d x = adjointZeroCoefficient n k i t l j d x)
    (w : Core n (k+1)) (i : Index n k) :
    components n k (globalChartRepresentative (deckRepresentation n) S k
      (coreChartCodifferentialLimit n k S χ η hχ hη hcη hsη w).val).val i =
    fun x => ∑ t, ∑ q : Index n k × Index n (k+1) × Fin 5,
      ((a i t q.1 q.2.1 q.2.2 x * fderiv ℝ η x (Pi.single q.2.2 1)) *
        (χ x * components n (k+1) (cutoffChartRaw n (k+1) S θ w.val) t x) +
      η x * ((a i t q.1 q.2.1 q.2.2 x * fderiv ℝ χ x (Pi.single q.2.2 1)) *
        components n (k+1) (cutoffChartRaw n (k+1) S θ w.val) t x)) := by
  let : IsBoundedSMul ℝ (FormValue n (k+1)) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n (k+1)) _ _ inferInstance
  let v := fun q : Index n k × Index n (k+1) × Fin 5 => (Pi.single q.2.2 1 : Coordinates)
  let A := fun i t (q : Index n k × Index n (k+1) × Fin 5) => a i t q.1 q.2.1 q.2.2
  let B := fun i t (q : Index n k × Index n (k+1) × Fin 5) => b i t q.1 q.2.1 q.2.2
  let g := cutoffChartRaw n (k+1) S θ w.val
  let m := fun x => η x • cutoffChartRaw n (k+1) S χ w.val x
  have hg := contDiff_cutoffChartRaw n (k+1) S θ hθ hsθ w.val
  have hm : ContDiff ℝ ∞ m := hη.smul (contDiff_cutoffChartRaw n (k+1) S χ hχ hsχ w.val)
  have hdg : components n k (localAdjoint n k g) = matrixFirstOrder v A B (components n (k+1) g) := by
    funext j
    exact localAdjoint_eq_extended_matrix n k K hKpos a b hab g hg
      ((tsupport_cutoffChartRaw n (k+1) S θ w.val).trans hθK) j
  have hdm := localAdjoint_eq_extended_matrix n k K hKpos a b hab m hm
    ((tsupport_smul_subset_left η (cutoffChartRaw n (k+1) S χ w.val)).trans hηK) i
  have hmcomp : components n (k+1) m = fun t x => η x * (χ x * components n (k+1) g t x) :=
    (components_smul_function n (k+1) η (cutoffChartRaw n (k+1) S χ w.val)).trans
      (congrArg (fun f : Index n (k+1) → Coordinates → ℝ => fun t x => η x * f t x)
        (components_cutoffChartRaw_buffer n (k+1) S χ θ w.val hθone))
  have hleft := hdm.trans (congrArg (fun f => matrixFirstOrder v A B f i) hmcomp)
  have hinput := (components_cutoffChartRaw_adjoint_buffer n k S χ θ hsχ hθone w).trans
    (congrArg (fun f : Index n k → Coordinates → ℝ => fun j x => χ x * f j x) hdg)
  have hright' : components n (k) (fun x => η x • cutoffChartRaw n k S χ (compactAdjoint n k w).val x) i =
      fun x => η x * (χ x * matrixFirstOrder v A B (components n (k+1) g) i x) :=
    (congrFun (components_smul_function n k η (cutoffChartRaw n k S χ (compactAdjoint n k w).val)) i).trans
      (congrArg (fun f : Coordinates → ℝ => fun x => η x * f x) (congrFun hinput i))
  have hrep := globalChartRepresentative_coreChartCodifferentialLimit n k S χ η hχ hη hcη hsη w
  have hcomp := (congrArg (fun f => components n k f i) hrep).trans
    (congrFun (components_sub_function n k _ _) i)
  have he := hcomp.trans (congrArg₂ (fun u v : Coordinates → ℝ => u-v) hleft hright')
  refine he.trans (funext (fun x => ?_))
  exact matrixFirstOrder_two_cutoffs v A B χ η (components n (k+1) g) i x
    (hχ.differentiable (by simp) x) (hη.differentiable (by simp) x)
    (fun t => (contDiff_cutoffChartComponents n (k+1) S θ hθ hsθ w.val t).differentiable (by simp) x)

end TernaryPoly.PolynomialFormCoordinates
