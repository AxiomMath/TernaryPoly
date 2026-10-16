module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ProjectiveConvex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Matrix SymmetricSpacePositive SymmetricSpaceCharts SmoothCoveringDeRham SymmetricSpaceCovering

/-- Reconstructing trace-one coordinates preserves genuine affine combinations. -/
theorem reconstruct_affine_combination (x y : Coordinates) (a b : ℝ) (hab : a + b = 1) :
    reconstruct (a • x + b • y) = a • reconstruct x + b • reconstruct y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reconstruct]
  nlinarith

/-- Extracting independent matrix entries is literally linear. -/
theorem extract_linear_combination (S T : Mat) (a b : ℝ) :
    extract (a • S + b • T) = a • extract S + b • extract T := by
  ext i
  fin_cases i <;> rfl

/-- The actual unnormalized congruence numerator is affine in trace-one coordinates. -/
theorem congruencePair_affine_combination (g : Mat) (x y : Coordinates) (a b : ℝ)
    (hab : a + b = 1) :
    congruencePair (g, a • x + b • y) =
      a • congruencePair (g,x) + b • congruencePair (g,y) := by
  simp only [congruencePair, reconstruct_affine_combination x y a b hab,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- The actual normalization denominator is affine in trace-one coordinates. -/
theorem denominator_affine_combination (g : Mat) (x y : Coordinates) (a b : ℝ)
    (hab : a + b = 1) :
    denominator (g, a • x + b • y) = a * denominator (g,x) + b * denominator (g,y) := by
  simp only [denominator, congruencePair_affine_combination g x y a b hab,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]

/-- The coordinate action is the actual affine numerator divided by its positive trace. -/
theorem coordinateAction_fractional (g : RealGL) (x : Coordinates) :
    coordinateAction g x = (denominator (g.val,x))⁻¹ • extract (congruencePair (g.val,x)) := by
  ext i
  fin_cases i <;> rfl

/-- Every actual normalized congruence action sends convex subsets of positive coordinates
to convex subsets, although its coordinate formula need not be affine. -/
theorem coordinateAction_convex_image (g : RealGL) {S : Set Coordinates}
    (hS : Convex ℝ S) (hpos : S ⊆ positiveCoordinates) :
    Convex ℝ (coordinateAction g '' S) := by
  have he : coordinateAction g = fun x => (denominator (g.val,x))⁻¹ •
      extract (congruencePair (g.val,x)) := funext (coordinateAction_fractional g)
  rw [he]
  apply convex_image_fractional_affine hS
  · intro x hx
    exact denominator_pos g x (hpos hx)
  · intro x _ y _ a b hab
    rw [congruencePair_affine_combination g.val x y a b hab,
      extract_linear_combination]
  · intro x _ y _ a b hab
    exact denominator_affine_combination g.val x y a b hab

/-- Genuine deck translates of convex lifting sheets are convex in the fixed coordinates. -/
theorem deckMap_convex_image (g : DeckGroup) {S : Set Coordinates}
    (hS : Convex ℝ S) (hpos : S ⊆ positiveCoordinates) :
    Convex ℝ (deckMap g '' S) :=
  coordinateAction_convex_image _ hS hpos

end TernaryPoly.SmoothSingularGlobal
