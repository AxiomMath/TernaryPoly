module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.ZeroOrder

@[expose] public section


/-! Actual symmetric exterior and contraction operators on compact quotient forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham SmoothLocalDeRham Set
open scoped ContDiff Matrix.Norms.Elementwise

theorem realCoefficientMap_deck (n : ℕ) (g : DeckGroup) :
    realCoefficientMap n (deckMatrix g) = coefficientMap (deckRepresentation n) g := by
  apply ContinuousLinearMap.ext
  intro p
  exact (deckRepresentation_eq_substitution n g p).symm

theorem symmetricExteriorCLM_isDeckOperator (n k : ℕ) : IsDeckOperator n k (k + 1) (symmetricExteriorCLM n k) := by
  intro g x hx a b ha
  have hg : (deckMatrix g).val.det ^ 2 = 1 := by rw [deckMatrix_det_one]; norm_num
  have h := symmetricExterior_real n k (deckMatrix g) hg x hx a b
  rw [realCoefficientMap_deck] at h
  simp only [symmetricExteriorCLM_apply]
  convert! h ha using 1

theorem symmetricContractionCLM_isDeckOperator (n k : ℕ) :
    IsDeckOperator n (k + 1) k (symmetricContractionCLM n k) := by
  intro g x hx a b ha
  have hg : (deckMatrix g).val.det ^ 2 = 1 := by rw [deckMatrix_det_one]; norm_num
  have h := symmetricContraction_real n k (deckMatrix g) hg x hx a b
  rw [realCoefficientMap_deck] at h
  simp only [symmetricContractionCLM_apply]
  convert! h ha using 1

/-- The actual pointwise symmetric exterior term is a genuine compact-support section operator. -/
def compactSymmetricExterior (n k : ℕ) :
    CompactSupportForm (deckRepresentation n) univ k →ₗ[ℝ] CompactSupportForm (deckRepresentation n) univ (k + 1) :=
  compactZeroOrder n k (k + 1) (symmetricExteriorCLM n k) (contDiffOn_symmetricExteriorCLM n k)
    (symmetricExteriorCLM_isDeckOperator n k)

/-- The actual inverse-Gram contraction is a genuine compact-support section operator. -/
def compactSymmetricContraction (n k : ℕ) :
    CompactSupportForm (deckRepresentation n) univ (k + 1) →ₗ[ℝ] CompactSupportForm (deckRepresentation n) univ k :=
  compactZeroOrder n (k + 1) k (symmetricContractionCLM n k) (contDiffOn_symmetricContractionCLM n k)
    (symmetricContractionCLM_isDeckOperator n k)

@[simp] theorem compactSymmetricExterior_apply (n k : ℕ)
    (w : CompactSupportForm (deckRepresentation n) univ k) (x : Coordinates) :
    (compactSymmetricExterior n k w).val.val.val x = symmetricExterior n k x (w.val.val.val x) :=
  symmetricExteriorCLM_apply n k x (w.val.val.val x)

@[simp] theorem compactSymmetricContraction_apply (n k : ℕ)
    (w : CompactSupportForm (deckRepresentation n) univ (k + 1)) (x : Coordinates) :
    (compactSymmetricContraction n k w).val.val.val x = symmetricContraction n k x (w.val.val.val x) :=
  symmetricContractionCLM_apply n k x (w.val.val.val x)

/- Keep the large subtype construction behind its evaluation lemmas. -/
attribute [irreducible] compactSymmetricExterior compactSymmetricContraction

end TernaryPoly.PolynomialFormGeometricEnergy
