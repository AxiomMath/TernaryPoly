module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Sheets

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham
open scoped ContDiff Topology

universe u
variable {D E F G : Type u}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ}

/-- Actual pullback composition, with the genuine chain-rule derivatives. -/
theorem pullRaw_comp {f : E → G} {g : D → E} (w : RawForm G F n) {x : D}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) :
    pullRaw g (pullRaw f w) x = pullRaw (f ∘ g) w x := by
  ext v
  simp only [pullRaw, compContinuousLinearMap_apply, Function.comp_apply,
    fderiv_comp x hf hg]
  rfl

theorem pullRaw_id (w : RawForm E F n) (x : E) : pullRaw id w x = w x := by
  ext v
  simp [pullRaw]

theorem pullRaw_eventuallyEq {f g : D → E} (w : RawForm E F n) {x : D}
    (hfg : f =ᶠ[𝓝 x] g) : pullRaw f w x = pullRaw g w x := by
  unfold pullRaw
  rw [hfg.self_of_nhds, hfg.fderiv_eq]

theorem coefficientRaw_pullRaw (L : F →L[ℝ] G) (f : D → E) (w : RawForm E F n) :
    coefficientRaw L (pullRaw f w) = pullRaw f (coefficientRaw L w) := by
  funext x
  ext v
  rfl

end TernaryPoly.SmoothCoveringDeRham
