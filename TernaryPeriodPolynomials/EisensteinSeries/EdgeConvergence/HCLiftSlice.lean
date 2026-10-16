module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.TaylorBounds

@[expose] public section


/-!
# Taylor coefficients of the slices of a jointly smooth function

Original work by Claude Sonnet 5.5.

If `function : G × E → F` is smooth on an open set, the Taylor coefficients at a fixed point
`center` of the slices `e ↦ function (g, e)` depend continuously on `g`
(`continuousOn_sliceCoefficients`): the `k`-th iterated derivative of the slice is the `k`-th
iterated derivative of `function` restricted along the inclusion `e ↦ (0, e)` of the second factor.
-/

open Filter Topology
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactTaylorBounds

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCLift

/-- The inclusion `e ↦ (g, e)` of a slice, as a continuous affine map. -/
def sliceMap (G E : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : G) : E →ᴬ[ℝ] G × E where
  toFun := fun e => (g, e)
  linear := (ContinuousLinearMap.inr ℝ G E).toLinearMap
  map_vadd' := fun p v => by
    ext
    · simp
    · simp
  cont := by fun_prop

theorem sliceMap_contLinear (G E : Type) [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : G) :
    (sliceMap G E g).contLinear = ContinuousLinearMap.inr ℝ G E :=
  ContinuousLinearMap.ext fun _ => rfl

/-- The iterated derivative of a slice. -/
theorem iteratedFDeriv_slice {G E F : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (function : G × E → F) {set : Set (G × E)} (isOpen : IsOpen set)
    (smooth : ContDiffOn ℝ ⊤ function set) (g : G) (center : E) (membership : (g, center) ∈ set)
    (order : ℕ) :
    iteratedFDeriv ℝ order (fun e => function (g, e)) center =
      (iteratedFDerivWithin ℝ order function set (g, center)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ G E) := by
  have taylor := (smooth.of_le (show (order : WithTop ℕ∞) ≤ ⊤ from le_top)).ftaylorSeriesWithin
    isOpen.uniqueDiffOn
  have composed := taylor.comp_continuousAffineMap (sliceMap G E g)
  have sliceOpen : IsOpen ((sliceMap G E g) ⁻¹' set) :=
    isOpen.preimage (sliceMap G E g).cont
  have equality := composed.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := order) le_rfl
    sliceOpen.uniqueDiffOn (show center ∈ (sliceMap G E g) ⁻¹' set from membership)
  have openEquality := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := function ∘ (sliceMap G E g))
    order sliceOpen (show center ∈ (sliceMap G E g) ⁻¹' set from membership)
  rw [sliceMap_contLinear] at equality
  exact (equality.trans openEquality).symm

/-- The Taylor coefficients of the slices at a fixed point are continuous in the slice. -/
theorem continuousOn_sliceCoefficients {G E F : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (function : G × E → F) {set : Set (G × E)} (isOpen : IsOpen set)
    (smooth : ContDiffOn ℝ ⊤ function set) (center : E) (order : ℕ) :
    ContinuousOn (fun g : G => coefficients (fun e => function (g, e)) center order)
      {g | (g, center) ∈ set} := by
  have derivative : ContinuousOn (iteratedFDerivWithin ℝ order function set) set :=
    smooth.continuousOn_iteratedFDerivWithin le_top isOpen.uniqueDiffOn
  have along : ContinuousOn (fun g : G => iteratedFDerivWithin ℝ order function set (g, center))
      {g | (g, center) ∈ set} :=
    derivative.comp (continuous_id.prodMk continuous_const).continuousOn (fun g membership =>
      membership)
  have restrict : Continuous (fun ψ : ContinuousMultilinearMap ℝ (fun _ : Fin order => G × E) F =>
      ψ.compContinuousLinearMap (fun _ : Fin order => ContinuousLinearMap.inr ℝ G E)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin order => ContinuousLinearMap.inr ℝ G E)).continuous
  have scaled := (restrict.const_smul (order.factorial : ℝ)⁻¹).comp_continuousOn along
  refine scaled.congr (fun g membership => ?_)
  change (order.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ order (fun e => function (g, e)) center = _
  rw [iteratedFDeriv_slice function isOpen smooth g center membership order]
  rfl

end TernaryPeriodPolynomials.EdgeConvergence.HCLift
