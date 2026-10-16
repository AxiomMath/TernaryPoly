module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Regularity
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CompactSupport

@[expose] public section



/-! Smooth equivariant zero-order operators preserve genuine quotient compact support. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham SmoothLocalDeRham Set
open scoped ContDiff Matrix.Norms.Elementwise

/-- Literal covariance of a fiberwise operator under the actual deck convention. -/
def IsDeckOperator (n k l : ℕ) (A : Coordinates → FormValue n k →L[ℝ] FormValue n l) : Prop :=
  ∀ (g : DeckGroup) (x : Coordinates), x ∈ positiveCoordinates → ∀ a b : FormValue n k,
    a.compContinuousLinearMap (fderiv ℝ (deckMap g) x) = coefficientFormMap (coefficientMap (deckRepresentation n) g) k b →
    (A (deckMap g x) a).compContinuousLinearMap (fderiv ℝ (deckMap g) x) =
      coefficientFormMap (coefficientMap (deckRepresentation n) g) l (A x b)

/-- A genuine smooth covariant fiber operator on the genuine equivariant section space. -/
def equivariantZeroOrder (n k l : ℕ) (A : Coordinates → FormValue n k →L[ℝ] FormValue n l)
    (hA : ContDiffOn ℝ ∞ A positiveCoordinates) (hcov : IsDeckOperator n k l A) :
    EquivariantForm (deckRepresentation n) univ k →ₗ[ℝ] EquivariantForm (deckRepresentation n) univ l where
  toFun w := ⟨⟨fun x => A x (w.val.val x), by
    constructor
    · have hw : ContDiffOn ℝ ∞ w.val.val positiveCoordinates := by
        simpa only [liftedDomain_univ] using Form.smooth w.val
      simpa only [liftedDomain_univ] using hA.clm_apply hw
    · intro x hx
      change A x (w.val.val x) = 0
      rw [Form.outside w.val hx, PolynomialFormCoordinates.clm_map_zero]⟩, by
      intro g x hx
      exact hcov g x hx.1 _ _ (w.property g x hx)⟩
  map_add' w z := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact (A x).map_add (w.val.val x) (z.val.val x)
  map_smul' c w := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact (A x).map_smul c (w.val.val x)

@[simp] theorem equivariantZeroOrder_apply (n k l : ℕ) (A : Coordinates → FormValue n k →L[ℝ] FormValue n l)
    (hA : ContDiffOn ℝ ∞ A positiveCoordinates) (hcov : IsDeckOperator n k l A)
    (w : EquivariantForm (deckRepresentation n) univ k) (x : Coordinates) :
    (equivariantZeroOrder n k l A hA hcov w).val.val x = A x (w.val.val x) := rfl

theorem quotientSupport_equivariantZeroOrder (n k l : ℕ) (A : Coordinates → FormValue n k →L[ℝ] FormValue n l)
    (hA : ContDiffOn ℝ ∞ A positiveCoordinates) (hcov : IsDeckOperator n k l A)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    quotientSupport (equivariantZeroOrder n k l A hA hcov w) ⊆ quotientSupport w := by
  apply closure_mono
  apply image_mono
  intro x hx
  change A x (w.val.val x) ≠ 0 at hx
  change w.val.val x ≠ 0
  intro h
  rw [h, PolynomialFormCoordinates.clm_map_zero] at hx
  exact hx rfl

/-- Genuine compact support is preserved on the arithmetic quotient. -/
def compactZeroOrder (n k l : ℕ) (A : Coordinates → FormValue n k →L[ℝ] FormValue n l)
    (hA : ContDiffOn ℝ ∞ A positiveCoordinates) (hcov : IsDeckOperator n k l A) :
    CompactSupportForm (deckRepresentation n) univ k →ₗ[ℝ] CompactSupportForm (deckRepresentation n) univ l where
  toFun w := ⟨equivariantZeroOrder n k l A hA hcov w.val,
    w.property.1.of_isClosed_subset isClosed_closure (quotientSupport_equivariantZeroOrder n k l A hA hcov w.val),
    subset_univ _⟩
  map_add' w z := Subtype.ext ((equivariantZeroOrder n k l A hA hcov).map_add w.val z.val)
  map_smul' c w := Subtype.ext ((equivariantZeroOrder n k l A hA hcov).map_smul c w.val)

@[simp] theorem compactZeroOrder_apply (n k l : ℕ) (A : Coordinates → FormValue n k →L[ℝ] FormValue n l)
    (hA : ContDiffOn ℝ ∞ A positiveCoordinates) (hcov : IsDeckOperator n k l A)
    (w : CompactSupportForm (deckRepresentation n) univ k) (x : Coordinates) :
    (compactZeroOrder n k l A hA hcov w).val.val.val x = A x (w.val.val.val x) := rfl

end TernaryPoly.PolynomialFormGeometricEnergy
