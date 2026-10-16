module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.CommutatorRepresentative
public import TernaryPeriodPolynomials.DifferentialForm.BufferedComponents
public import TernaryPeriodPolynomials.DifferentialForm.DifferentialExtensionFormula

@[expose] public section



/-! The genuine compact differential chart commutator is exactly the buffered matrix commutator. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert CompactCoordinateIntegration
open scoped ContDiff Topology

theorem differentialCommutator_eq_matrix (n k : ℕ) (S : Space) (χ η θ : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (hθ : ContDiff ℝ ∞ θ) (hsθ : tsupport θ ⊆ (quotientChart S).target)
    (hθone : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1)
    (K : Set Coordinates) (hηK : tsupport η ⊆ K) (hθK : tsupport θ ⊆ K)
    (a : Index n (k+1) → Index n k → Fin 5 → Coordinates → ℝ)
    (ha : ∀ x ∈ K, ∀ j i d, a j i d x = differentialCoefficients n k j i d x)
    (c : ℝ) (hc : 0 < c) (w : Core n k) (i : Index n (k+1)) :
    components n (k+1) (globalChartRepresentative (deckRepresentation n) S (k+1)
      (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w).val).val i =
    fun x =>
      matrixFirstOrder (fun d : Fin 5 => (Pi.single d 1 : Coordinates)) a (fun _ _ _ _ => 0)
        (fun t y => η y * scalarConvolution volume (CompactScalarMollifier.kernel Coordinates volume c)
          (fun z => χ z * components n k (cutoffChartRaw n k S θ w.val) t z) y) i x -
      η x * scalarConvolution volume (CompactScalarMollifier.kernel Coordinates volume c)
        (fun z => χ z * matrixFirstOrder
          (fun d : Fin 5 => (Pi.single d 1 : Coordinates)) a (fun _ _ _ _ => 0)
          (components n k (cutoffChartRaw n k S θ w.val)) i z) x := by
  let v := fun d : Fin 5 => (Pi.single d 1 : Coordinates)
  let B : Index n (k+1) → Index n k → Fin 5 → Coordinates → ℝ := fun _ _ _ _ => 0
  let g := cutoffChartRaw n k S θ w.val
  let m := mollifiedChartRaw n k S χ η c w.val
  have hg := contDiff_cutoffChartRaw n k S θ hθ hsθ w.val
  have hm := contDiff_mollifiedChartRaw n k S χ η c hc.ne' hχ hsχ hη w.val
  have hdg : components n (k+1) (extDeriv g) = matrixFirstOrder v a B (components n k g) := by
    funext j
    exact extDeriv_eq_extended_matrix n k K a ha g hg
      ((tsupport_cutoffChartRaw n k S θ w.val).trans hθK) j
  have hdm := extDeriv_eq_extended_matrix n k K a ha m hm
    ((tsupport_mollifiedChartRaw n k S χ η c w.val).trans hηK) i
  have hleft := hdm.trans (congrArg (fun f => matrixFirstOrder v a B f i)
    (components_mollifiedChartRaw_buffer n k S χ η θ w.val hθone c))
  have hinput := (components_cutoffChartRaw_differential_buffer n k S χ θ hsχ hθone w).trans
    (congrArg (fun f : Index n (k+1) → Coordinates → ℝ => fun j x => χ x * f j x) hdg)
  have hright : components n (k+1) (mollifiedChartRaw n (k+1) S χ η c
      (compactDifferential (deckRepresentation n) isOpen_univ k w).val) i =
      fun x => η x * scalarConvolution volume (CompactScalarMollifier.kernel Coordinates volume c)
        (fun z => χ z * matrixFirstOrder v a B (components n k g) i z) x := by
    funext x
    exact (components_mollifiedChartRaw n (k+1) S χ η c
      (compactDifferential (deckRepresentation n) isOpen_univ k w).val i x).trans
      (congrArg (fun f : Coordinates → ℝ => η x * scalarConvolution volume
        (CompactScalarMollifier.kernel Coordinates volume c) f x) (congrFun hinput i))
  have hrep := globalChartRepresentative_differentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w
  have hsub (u v : Coordinates → FormValue n (k+1)) :
      components n (k+1) (u-v) i = components n (k+1) u i - components n (k+1) v i := by
    funext x
    change coordinates n (k+1) (u x - v x) i = _
    rw [ContinuousLinearEquiv.map_sub]
    rfl
  have hcomp := (congrArg (fun f => components n (k+1) f i) hrep).trans (hsub _ _)
  exact hcomp.trans (congrArg₂ (fun u v : Coordinates → ℝ => u-v) hleft hright)

end TernaryPoly.PolynomialFormCoordinates
