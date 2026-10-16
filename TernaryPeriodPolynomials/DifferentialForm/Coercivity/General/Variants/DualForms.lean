module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DualCoordinates
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Calculus.IntegrationByParts

@[expose] public section


/-!
# General coercivity, dual coefficients: forms with values in the dual bundle

The dual coefficient system `Sym^n((ℝ³)*)^* = Sym^n ℝ³` is the representation `ρ ∘ θ` of `Γ` on the
same space of polynomials, where `θ g = (g⁻¹)ᵀ`; its flat-bundle metric at `S = g gᵀ` is
`‖ρ*(g)⁻¹ p‖ = ‖ρ(g)ᵀ p‖`, that is, the standard coefficient metric at the Cartan point `ι S = S⁻¹/tr`.
This file defines the space `DForm Γ n k` of smooth compactly supported `Γ`-equivariant forms with
values in the dual bundle and the pullback `ioPull` along the Cartan involution, which is an
isomorphism of `DForm Γ n k` with the standard forms `CForm (θΓ) n k` commuting with `d`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.SmoothCoveringDeRham
  TernaryPoly.SmoothLocalDeRham TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.PolynomialFormMetric TernaryPoly.PolynomialFormConnection
open Set Filter
open scoped ContDiff Topology

/-! ### The Cartan pullback of raw forms -/

/-- Pull back a raw form along the Cartan involution, with zero extension. -/
def ioPull (n k : ℕ) (w : Coordinates → FormValue n k) : Coordinates → FormValue n k :=
  positiveCoordinates.indicator (pullRaw iotaC w)

theorem ioPull_apply (n k : ℕ) (w : Coordinates → FormValue n k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    ioPull n k w x = (w (iotaC x)).compContinuousLinearMap (fderiv ℝ iotaC x) :=
  indicator_of_mem hx _

theorem ioPull_of_notMem (n k : ℕ) (w : Coordinates → FormValue n k) {x : Coordinates}
    (hx : x ∉ positiveCoordinates) : ioPull n k w x = 0 :=
  indicator_of_notMem hx _

theorem contDiffOn_ioPull (n k : ℕ) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) :
    ContDiffOn ℝ ∞ (ioPull n k w) positiveCoordinates :=
  (pullRaw_smooth isOpen_positiveCoordinates contDiffOn_iotaC hw
    (fun _ hx => iotaC_mem hx)).congr (fun _ hx => ioPull_apply n k w hx)

/-- The derivative of the involution composed with itself is the identity. -/
theorem fderiv_iotaC_comp {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    (fderiv ℝ iotaC (iotaC x)).comp (fderiv ℝ iotaC x) = ContinuousLinearMap.id ℝ Coordinates := by
  have he : (iotaC ∘ iotaC) =ᶠ[𝓝 x] id := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    exact iotaC_iotaC hy
  have hg := ((contDiffOn_iotaC x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have hi := ((contDiffOn_iotaC (iotaC x) (iotaC_mem hx)).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds (iotaC_mem hx))).differentiableAt (by simp)
  rw [← fderiv_comp x hi hg, he.fderiv_eq, fderiv_id]

theorem ioPull_ioPull (n k : ℕ) (w : Coordinates → FormValue n k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) : ioPull n k (ioPull n k w) x = w x := by
  rw [ioPull_apply n k _ hx, ioPull_apply n k w (iotaC_mem hx), iotaC_iotaC hx]
  apply ContinuousAlternatingMap.ext
  intro v
  change w x (fun i => (fderiv ℝ iotaC (iotaC x)) ((fderiv ℝ iotaC x) (v i))) = w x v
  apply congrArg (w x)
  funext i
  exact congrArg (fun L : Coordinates →L[ℝ] Coordinates => L (v i)) (fderiv_iotaC_comp hx)

/-- The exterior differential commutes with the Cartan pullback on the positive coordinates. -/
theorem extDeriv_ioPull (n k : ℕ) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    extDeriv (ioPull n k w) x = ioPull n (k + 1) (extDeriv w) x := by
  have he : ioPull n k w =ᶠ[𝓝 x] pullRaw iotaC w := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    exact indicator_of_mem hy _
  rw [he.extDeriv_eq, extDeriv_pullRaw ((contDiffOn_iotaC x hx).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hx))
      (((hw _ (iotaC_mem hx)).contDiffAt
        (isOpen_positiveCoordinates.mem_nhds (iotaC_mem hx))).differentiableAt (by simp)),
    ioPull_apply n (k + 1) (extDeriv w) hx]
  rfl

theorem coefficientFormMap_compCLM {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →L[ℝ] F) (k : ℕ) (a : Coordinates [⋀^Fin k]→L[ℝ] F) (M : Coordinates →L[ℝ] Coordinates) :
    (coefficientFormMap L k a).compContinuousLinearMap M =
      coefficientFormMap L k (a.compContinuousLinearMap M) := by
  ext v
  simp [coefficientFormMap]

/-- Chain rule: pulling back `ioPull w` along the action of `g` is the Cartan pullback of the pullback
of `w` along the action of `θ g`. -/
theorem pullRaw_ioPull (n k : ℕ) (g : RealGL) (w : Coordinates → FormValue n k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    pullRaw (coordinateAction g) (ioPull n k w) x =
      (pullRaw (coordinateAction (thetaHom g)) w (iotaC x)).compContinuousLinearMap
        (fderiv ℝ iotaC x) := by
  have hgx := coordinateAction_mem g x hx
  have hix := iotaC_mem hx
  have hcomp : (fderiv ℝ iotaC (coordinateAction g x)).comp (fderiv ℝ (coordinateAction g) x) =
      (fderiv ℝ (coordinateAction (thetaHom g)) (iotaC x)).comp (fderiv ℝ iotaC x) := by
    have he : (iotaC ∘ coordinateAction g) =ᶠ[𝓝 x] (coordinateAction (thetaHom g) ∘ iotaC) := by
      filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
      exact iotaC_action g hy
    have d1 := ((contDiffOn_coordinateAction g x hx).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
    have d2 := ((contDiffOn_iotaC (coordinateAction g x) hgx).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hgx)).differentiableAt (by simp)
    have d3 := ((contDiffOn_iotaC x hx).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
    have d4 := ((contDiffOn_coordinateAction (thetaHom g) (iotaC x) hix).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hix)).differentiableAt (by simp)
    rw [← fderiv_comp x d2 d1, ← fderiv_comp x d4 d3, he.fderiv_eq]
  unfold pullRaw
  rw [ioPull_apply n k w hgx, iotaC_action g hx]
  apply ContinuousAlternatingMap.ext
  intro v
  change w (coordinateAction (thetaHom g) (iotaC x)) (fun i =>
      (fderiv ℝ iotaC (coordinateAction g x)) ((fderiv ℝ (coordinateAction g) x) (v i))) =
    w (coordinateAction (thetaHom g) (iotaC x)) (fun i =>
      (fderiv ℝ (coordinateAction (thetaHom g)) (iotaC x)) ((fderiv ℝ iotaC x) (v i)))
  apply congrArg
  funext i
  exact congrArg (fun L : Coordinates →L[ℝ] Coordinates => L (v i)) hcomp

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
