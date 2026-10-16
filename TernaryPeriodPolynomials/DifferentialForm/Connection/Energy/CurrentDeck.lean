module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentDerivative

@[expose] public section

/-! Actual deck covariance of the symmetric-connection energy current. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy SymmetricSpaceCharts
open SymmetricSpaceCovering SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

theorem symmetricPart_form_deck (n k : ℕ) (g : DeckGroup) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (v : Coordinates) (a b : FormValue n k)
    (ha : a.compContinuousLinearMap (fderiv ℝ (deckMap g) x) =
      coefficientFormMap (coefficientMap (deckRepresentation n) g) k b) :
    (coefficientFormMap (symmetricPart n (deckMap g x) (fderiv ℝ (deckMap g) x v)) k a).compContinuousLinearMap
      (fderiv ℝ (deckMap g) x) =
      coefficientFormMap (coefficientMap (deckRepresentation n) g) k
        (coefficientFormMap (symmetricPart n x v) k b) := by
  apply ContinuousAlternatingMap.ext
  intro z
  have he := congrArg (fun c : FormValue n k => c z) ha
  change a (fun i => fderiv ℝ (deckMap g) x (z i)) = deckRepresentation n g (b z) at he
  change symmetricPart n (deckMap g x) (fderiv ℝ (deckMap g) x v)
      (a (fun i => fderiv ℝ (deckMap g) x (z i))) = deckRepresentation n g (symmetricPart n x v (b z))
  rw [he]
  exact symmetricPart_deck n g x hx v (b z)

theorem energyCovector_deck (n k : ℕ) (g : DeckGroup) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (v : Coordinates) (a b : FormValue n k)
    (ha : a.compContinuousLinearMap (fderiv ℝ (deckMap g) x) =
      coefficientFormMap (coefficientMap (deckRepresentation n) g) k b) :
    energyCovector n k (deckMap g x) a (fderiv ℝ (deckMap g) x v) = energyCovector n k x b v :=
  formPairing_deck n k g x hx _ _ _ _ ha (symmetricPart_form_deck n k g x hx v a b ha)

theorem covectorCoordinates_pullback (L : Coordinates →L[ℝ] Coordinates) (a : Coordinates →L[ℝ] ℝ) :
    (LinearMap.toMatrix' L.toLinearMap).transpose *ᵥ (fun i => a (Pi.single i 1)) =
      fun i => a (L (Pi.single i 1)) := by
  funext i
  rw [show L (Pi.single i 1) = ∑ j, (L (Pi.single i 1) j) • Pi.single j 1 from pi_eq_sum_univ' _]
  simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    LinearMap.toMatrix'_apply]
  rfl

theorem energyCurrent_isDeckVectorField (n k : ℕ)
    (w : EquivariantForm (deckRepresentation n) Set.univ k) :
    IsDeckVectorField (energyCurrent n k w.val.val) := by
  intro g x hx
  let L := fderiv ℝ (deckMap g) x
  let M := LinearMap.toMatrix' L.toLinearMap
  let a := energyCovectorCoordinates n k w.val.val x
  let b := energyCovectorCoordinates n k w.val.val (deckMap g x)
  have hab : M.transpose *ᵥ b = a := by
    rw [show b = fun i => energyCovector n k (deckMap g x) (w.val.val (deckMap g x)) (Pi.single i 1) from rfl]
    rw [covectorCoordinates_pullback]
    funext i
    exact energyCovector_deck n k g x hx (Pi.single i 1) _ _ (w.property g x ⟨hx, Set.mem_univ _⟩)
  change inverseGram (deckMap g x) *ᵥ b = L (inverseGram x *ᵥ a)
  rw [← inverseGram_deck g x hx]
  change (M * inverseGram x * M.transpose) *ᵥ b = L (inverseGram x *ᵥ a)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hab]
  exact LinearMap.toMatrix'_mulVec L.toLinearMap _

end TernaryPoly.PolynomialFormConnection
