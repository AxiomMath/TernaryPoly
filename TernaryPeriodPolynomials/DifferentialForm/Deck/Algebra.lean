module

public import TernaryPeriodPolynomials.DifferentialForm.Deck.Pullback
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Extension
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.PullbackAlgebra

@[expose] public section


/-! Exact inverse, metric and exterior-differential laws of normalized deck pullback. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric PolynomialCoefficientMetric SymmetricSpaceCharts SymmetricSpaceCovering
open SmoothCoveringDeRham
open Set Filter
open scoped ContDiff Topology

theorem deckPull_equation (n k : ℕ) (g : DeckGroup) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coefficientFormMap (coefficientMap (deckRepresentation n) g) k (deckPull n k g w x) =
      (w (deckMap g x)).compContinuousLinearMap (fderiv ℝ (deckMap g) x) := by
  rw [deckPull_apply n k g w hx, ← coefficientFormMap_mul, mul_inv_cancel, coefficientFormMap_one]

theorem formPairing_deckPull (n k : ℕ) (g : DeckGroup) (w z : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    formPairing n k x (deckPull n k g w x) (deckPull n k g z x) =
      formPairing n k (deckMap g x) (w (deckMap g x)) (z (deckMap g x)) :=
  (formPairing_deck n k g x hx _ _ _ _
    (deckPull_equation n k g w hx).symm (deckPull_equation n k g z hx).symm).symm

theorem deckDerivative_inverse (g : DeckGroup) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    (fderiv ℝ (deckMap g⁻¹) (deckMap g x)).comp (fderiv ℝ (deckMap g) x) =
      ContinuousLinearMap.id ℝ Coordinates := by
  have he : (deckMap g⁻¹ ∘ deckMap g) =ᶠ[𝓝 x] id := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    change deckMap g⁻¹ (deckMap g y) = y
    rw [← deckMap_mul g⁻¹ g hy, inv_mul_cancel, deckMap_one hy]
  have hg := ((deckMap_smooth g x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have hi := ((deckMap_smooth g⁻¹ (deckMap g x) (deckMap_mem g hx)).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds (deckMap_mem g hx))).differentiableAt (by simp)
  rw [← fderiv_comp x hi hg, he.fderiv_eq, fderiv_id]

/-- A normalized deck pullback followed by its inverse recovers the actual form on the domain. -/
theorem deckPull_inverse (n k : ℕ) (g : DeckGroup) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    deckPull n k g (deckPull n k g⁻¹ w) x = w x := by
  rw [deckPull_apply n k g _ hx, deckPull_apply n k g⁻¹ w (deckMap_mem g hx), inv_inv]
  apply ContinuousAlternatingMap.ext
  intro v
  change (deckRepresentation n g⁻¹) ((deckRepresentation n g)
    (w (deckMap g⁻¹ (deckMap g x)) (fun i =>
      (fderiv ℝ (deckMap g⁻¹) (deckMap g x)) ((fderiv ℝ (deckMap g) x) (v i))))) = w x v
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    ← deckMap_mul g⁻¹ g hx, inv_mul_cancel, deckMap_one hx]
  apply congrArg (w x)
  funext i
  exact congrArg (fun L : Coordinates →L[ℝ] Coordinates => L (v i)) (deckDerivative_inverse g hx)

/-- The genuine exterior differential commutes with normalized deck pullback on the open domain. -/
theorem extDeriv_deckPull (n k : ℕ) (g : DeckGroup) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    extDeriv (deckPull n k g w) x = deckPull n (k + 1) g (extDeriv w) x := by
  have he : deckPull n k g w =ᶠ[𝓝 x]
      coefficientRaw (coefficientMap (deckRepresentation n) g⁻¹) (pullRaw (deckMap g) w) := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    exact deckPull_apply n k g w hy
  have hd := ((pullRaw_smooth isOpen_positiveCoordinates (deckMap_smooth g) hw
    (fun _ hy => deckMap_mem g hy)) x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)
  rw [he.extDeriv_eq, extDeriv_coefficientRaw _ (hd.differentiableAt (by simp)),
    extDeriv_pullRaw ((deckMap_smooth g x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx))
      (((hw _ (deckMap_mem g hx)).contDiffAt
        (isOpen_positiveCoordinates.mem_nhds (deckMap_mem g hx))).differentiableAt (by simp)),
    deckPull_apply n (k + 1) g (extDeriv w) hx]
  rfl

end TernaryPoly.PolynomialFormCoordinates
