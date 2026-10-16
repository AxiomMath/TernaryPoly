module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Differential.Limit
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Differential.CommutatorFormula
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.CutoffSymbol

@[expose] public section



/-! The literal double-cutoff differential commutator retains both principal-symbol terms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert CompactCoordinateIntegration
open scoped ContDiff Topology

theorem differentialLimit_eq_symbol (n k : ℕ) (S : Space) (χ η θ : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (hθ : ContDiff ℝ ∞ θ) (hsθ : tsupport θ ⊆ (quotientChart S).target)
    (hθone : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1)
    (K : Set Coordinates) (hηK : tsupport η ⊆ K) (hθK : tsupport θ ⊆ K)
    (a : Index n (k+1) → Index n k → Fin 5 → Coordinates → ℝ)
    (ha : ∀ x ∈ K, ∀ j i d, a j i d x = differentialCoefficients n k j i d x)
    (w : Core n k) (i : Index n (k+1)) :
    components n (k+1) (globalChartRepresentative (deckRepresentation n) S (k+1)
      (coreChartDifferentialLimit n k S χ η hχ hη hcη hsη w).val).val i =
      fun x => ∑ t : Index n k, ∑ d : Fin 5,
        ((a i t d x * fderiv ℝ η x (Pi.single d 1)) *
          (χ x * components n k (cutoffChartRaw n k S θ w.val) t x) +
        η x * ((a i t d x * fderiv ℝ χ x (Pi.single d 1)) *
          components n k (cutoffChartRaw n k S θ w.val) t x)) := by
  let v := fun d : Fin 5 => (Pi.single d 1 : Coordinates)
  let B : Index n (k+1) → Index n k → Fin 5 → Coordinates → ℝ := fun _ _ _ _ => 0
  let g := cutoffChartRaw n k S θ w.val
  let m := fun x => η x • cutoffChartRaw n k S χ w.val x
  have hg := contDiff_cutoffChartRaw n k S θ hθ hsθ w.val
  let : IsBoundedSMul ℝ (FormValue n k) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
  have hm : ContDiff ℝ ∞ m := hη.smul (contDiff_cutoffChartRaw n k S χ hχ hsχ w.val)
  have hdg : components n (k+1) (extDeriv g) = matrixFirstOrder v a B (components n k g) := by
    funext j
    exact extDeriv_eq_extended_matrix n k K a ha g hg
      ((tsupport_cutoffChartRaw n k S θ w.val).trans hθK) j
  have hdm := extDeriv_eq_extended_matrix n k K a ha m hm
    ((tsupport_smul_subset_left η (cutoffChartRaw n k S χ w.val)).trans hηK) i
  have hmcomp : components n k m = fun t x => η x * (χ x * components n k g t x) :=
    (components_smul_function n k η (cutoffChartRaw n k S χ w.val)).trans
      (congrArg (fun f : Index n k → Coordinates → ℝ => fun t x => η x * f t x)
        (components_cutoffChartRaw_buffer n k S χ θ w.val hθone))
  have hleft := hdm.trans (congrArg (fun f => matrixFirstOrder v a B f i) hmcomp)
  have hinput := (components_cutoffChartRaw_differential_buffer n k S χ θ hsχ hθone w).trans
    (congrArg (fun f : Index n (k+1) → Coordinates → ℝ => fun j x => χ x * f j x) hdg)
  have hright : components n (k+1)
      (fun x => η x • cutoffChartRaw n (k+1) S χ
        (compactDifferential (deckRepresentation n) isOpen_univ k w).val x) i =
      fun x => η x * (χ x * matrixFirstOrder v a B (components n k g) i x) :=
    (congrFun (components_smul_function n (k+1) η
      (cutoffChartRaw n (k+1) S χ (compactDifferential (deckRepresentation n) isOpen_univ k w).val)) i).trans
      (congrArg (fun f : Coordinates → ℝ => fun x => η x * f x) (congrFun hinput i))
  have hrep := globalChartRepresentative_coreChartDifferentialLimit n k S χ η hχ hη hcη hsη w
  have hsub (u v : Coordinates → FormValue n (k+1)) :
      components n (k+1) (u-v) i = components n (k+1) u i - components n (k+1) v i := by
    funext x
    change coordinates n (k+1) (u x - v x) i = _
    rw [ContinuousLinearEquiv.map_sub]
    rfl
  have hcomp := (congrArg (fun f => components n (k+1) f i) hrep).trans (hsub _ _)
  apply (hcomp.trans (congrArg₂ (fun u v : Coordinates → ℝ => u-v) hleft hright)).trans
  funext x
  exact matrixFirstOrder_two_cutoffs v a B χ η (components n k g) i x
    (hχ.differentiable (by simp) x) (hη.differentiable (by simp) x)
    (fun t => (contDiff_cutoffChartComponents n k S θ hθ hsθ w.val t).differentiable (by simp) x)

end TernaryPoly.PolynomialFormCoordinates
