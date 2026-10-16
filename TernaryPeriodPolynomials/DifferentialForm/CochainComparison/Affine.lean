module

public import TernaryPeriodPolynomials.DifferentialForm.CochainComparison.Basic

@[expose] public section


/-!
# Affine actions, pullback and coefficient twist of edge integrals

Formalized by Claude Sonnet 5.5.
-/

open Set MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormCochainBridge

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open TernaryPeriodPolynomials.Argument.SeedC3

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type} [Group G] {s : Set E}

/-- An action by (globally defined) affine maps fixing the identity: the case of the linear action of
`GL₃` on Gram matrices. -/
structure AffineAction (A : ZigZag.Action G s) where
  lin : G → E →L[ℝ] E
  off : G → E
  act_eq : ∀ g x, A.act g x = lin g x + off g
  one : ∀ x ∈ s, A.act 1 x = x

variable {A : ZigZag.Action G s}

theorem AffineAction.fderiv_act (𝔄 : AffineAction A) (g : G) (x : E) : fderiv ℝ (A.act g) x = 𝔄.lin g := by
  have : A.act g = fun x => 𝔄.lin g x + 𝔄.off g := funext (𝔄.act_eq g)
  rw [this]
  exact ((𝔄.lin g).hasFDerivAt.add_const (𝔄.off g)).fderiv

theorem AffineAction.act_segment (𝔄 : AffineAction A) (g : G) (x y : E) (t : ℝ) :
    A.act g (x + t • (y - x)) = A.act g x + t • (A.act g y - A.act g x) := by
  simp only [𝔄.act_eq, map_add, map_smul, map_sub]
  module

theorem AffineAction.lin_sub (𝔄 : AffineAction A) (g : G) (x y : E) : 𝔄.lin g (y - x) = A.act g y - A.act g x := by
  simp only [𝔄.act_eq, map_sub]
  abel

/-- The pullback of a chart `1`-form by an affine action evaluated on a constant vector. -/
theorem pullForm_one_apply [FiniteDimensional ℝ E] (𝔄 : AffineAction A) (hs : IsOpen s) (g : G) (η : Form (F := F) s 1) {x : E} (hx : x ∈ s) (v : E) :
    (ZigZag.pullForm hs A g 1 η : RawForm E F 1) x (fun _ => v) =
      (η : RawForm E F 1) (A.act g x) (fun _ => 𝔄.lin g v) := by
  rw [ZigZag.pullForm_apply hs A g η hx]
  simp only [pullRaw, ContinuousAlternatingMap.compContinuousLinearMap_apply, 𝔄.fderiv_act]
  rfl

/-- **Pullback of edge integrals under an affine action.** -/
theorem segInt_pullForm [FiniteDimensional ℝ E] [CompleteSpace F] (𝔄 : AffineAction A) (hs : IsOpen s) (hc : Convex ℝ s) (g : G)
    (η : Form (F := F) s 1) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    segInt (ZigZag.pullForm hs A g 1 η : RawForm E F 1) x y =
      segInt (η : RawForm E F 1) (A.act g x) (A.act g y) := by
  unfold segInt
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  show (ZigZag.pullForm hs A g 1 η : RawForm E F 1) (x + t • (y - x)) (fun _ => y - x) = _
  rw [pullForm_one_apply 𝔄 hs g η (segment_mem hc hx hy ht), 𝔄.act_segment, 𝔄.lin_sub]

/-- Twisting the coefficients commutes with edge integrals. -/
theorem segInt_twForm [CompleteSpace F] (hc : Convex ℝ s) (L : F →L[ℝ] F)
    (η : Form (F := F) s 1) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    segInt (ZigZag.twForm (s := s) L 1 η : RawForm E F 1) x y = L (segInt (η : RawForm E F 1) x y) := by
  unfold segInt
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm L (integrable_segInt hc η hx hy)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp [ZigZag.twForm_apply]

/-- Edge integrals are additive in the form. -/
theorem segInt_add [CompleteSpace F] (hc : Convex ℝ s) (η η' : Form (F := F) s 1) {x y : E}
    (hx : x ∈ s) (hy : y ∈ s) :
    segInt ((η + η' : Form (F := F) s 1) : RawForm E F 1) x y =
      segInt (η : RawForm E F 1) x y + segInt (η' : RawForm E F 1) x y := by
  unfold segInt
  rw [← intervalIntegral.integral_add (integrable_segInt hc η hx hy) (integrable_segInt hc η' hx hy)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp

end TernaryPeriodPolynomials.Argument.FormCochainBridge
