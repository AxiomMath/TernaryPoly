module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.CommutatorRepresentative
public import TernaryPeriodPolynomials.DifferentialForm.BufferedComponents
public import TernaryPeriodPolynomials.DifferentialForm.AdjointExtensionFormula

@[expose] public section


/-! The genuine compact codifferential chart commutator is exactly the buffered matrix commutator. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert CompactCoordinateIntegration
open scoped ContDiff Topology

theorem components_sub_function (n k : ℕ) (u v : Coordinates → FormValue n k) :
    components n k (u-v) = components n k u - components n k v := by
  funext i x
  change (coordinates n k (u x - v x)) i = _
  rw [ContinuousLinearEquiv.map_sub]
  rfl

theorem codifferentialCommutator_eq_matrix (n k : ℕ) (S : Space) (χ η θ : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (hθ : ContDiff ℝ ∞ θ) (hsθ : tsupport θ ⊆ (quotientChart S).target)
    (hθone : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1)
    (K : Set Coordinates) (hKpos : K ⊆ positiveCoordinates) (hηK : tsupport η ⊆ K) (hθK : tsupport θ ⊆ K)
    (a b : Index n k → Index n (k+1) → Index n k → Index n (k+1) → Fin 5 → Coordinates → ℝ)
    (hab : ∀ x ∈ K, ∀ i t l j d,
      a i t l j d x = adjointFirstCoefficient n k i t l j d x ∧
      b i t l j d x = adjointZeroCoefficient n k i t l j d x)
    (c : ℝ) (hc : 0 < c) (w : Core n (k+1)) (i : Index n k) :
    components n k (globalChartRepresentative (deckRepresentation n) S k
      (coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w).val).val i =
    fun x =>
      matrixFirstOrder (fun q : Index n k × Index n (k+1) × Fin 5 => (Pi.single q.2.2 1 : Coordinates))
        (fun i t q => a i t q.1 q.2.1 q.2.2) (fun i t q => b i t q.1 q.2.1 q.2.2)
        (fun t y => η y * scalarConvolution volume (CompactScalarMollifier.kernel Coordinates volume c)
          (fun z => χ z * components n (k+1) (cutoffChartRaw n (k+1) S θ w.val) t z) y) i x -
      η x * scalarConvolution volume (CompactScalarMollifier.kernel Coordinates volume c)
        (fun z => χ z * matrixFirstOrder
          (fun q : Index n k × Index n (k+1) × Fin 5 => (Pi.single q.2.2 1 : Coordinates))
          (fun i t q => a i t q.1 q.2.1 q.2.2) (fun i t q => b i t q.1 q.2.1 q.2.2)
          (components n (k+1) (cutoffChartRaw n (k+1) S θ w.val)) i z) x := by
  let v := fun q : Index n k × Index n (k+1) × Fin 5 => (Pi.single q.2.2 1 : Coordinates)
  let A := fun i t (q : Index n k × Index n (k+1) × Fin 5) => a i t q.1 q.2.1 q.2.2
  let B := fun i t (q : Index n k × Index n (k+1) × Fin 5) => b i t q.1 q.2.1 q.2.2
  let g := cutoffChartRaw n (k+1) S θ w.val
  let m := mollifiedChartRaw n (k+1) S χ η c w.val
  have hg := contDiff_cutoffChartRaw n (k+1) S θ hθ hsθ w.val
  have hm := contDiff_mollifiedChartRaw n (k+1) S χ η c hc.ne' hχ hsχ hη w.val
  have hdg : components n k (localAdjoint n k g) = matrixFirstOrder v A B (components n (k+1) g) := by
    funext j
    exact localAdjoint_eq_extended_matrix n k K hKpos a b hab g hg
      ((tsupport_cutoffChartRaw n (k+1) S θ w.val).trans hθK) j
  have hdm := localAdjoint_eq_extended_matrix n k K hKpos a b hab m hm
    ((tsupport_mollifiedChartRaw n (k+1) S χ η c w.val).trans hηK) i
  have hleft := hdm.trans (congrArg (fun f => matrixFirstOrder v A B f i)
    (components_mollifiedChartRaw_buffer n (k+1) S χ η θ w.val hθone c))
  have hinput := (components_cutoffChartRaw_adjoint_buffer n k S χ θ hsχ hθone w).trans
    (congrArg (fun f : Index n k → Coordinates → ℝ => fun j x => χ x * f j x) hdg)
  have hright : components n k (mollifiedChartRaw n k S χ η c (compactAdjoint n k w).val) i =
      fun x => η x * scalarConvolution volume (CompactScalarMollifier.kernel Coordinates volume c)
        (fun z => χ z * matrixFirstOrder v A B (components n (k+1) g) i z) x := by
    funext x
    exact (components_mollifiedChartRaw n k S χ η c (compactAdjoint n k w).val i x).trans
      (congrArg (fun f : Coordinates → ℝ => η x * scalarConvolution volume
        (CompactScalarMollifier.kernel Coordinates volume c) f x) (congrFun hinput i))
  have hrep := globalChartRepresentative_codifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w
  have hcomp := (congrArg (fun f => components n k f i) hrep).trans
    (congrFun (components_sub_function n k _ _) i)
  exact hcomp.trans (congrArg₂ (fun u v : Coordinates → ℝ => u-v) hleft hright)

end TernaryPoly.PolynomialFormCoordinates
