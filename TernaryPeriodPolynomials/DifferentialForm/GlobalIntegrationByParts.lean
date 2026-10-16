module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.IntegrationByParts
public import TernaryPeriodPolynomials.DifferentialForm.QuotientPairing
public import TernaryPeriodPolynomials.DifferentialForm.FiniteCharts
public import TernaryPeriodPolynomials.Analysis.Compact.FormChartLocalization

@[expose] public section


/-! Genuine global integration by parts on the arithmetic quotient. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialCoefficientMetric PolynomialFormMetric SymmetricSpaceCovering SymmetricSpaceRiemannian
open SmoothCoveringDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian

/-- Actual global integral defect, a linear functional in the compact first form. -/
def adjointDefect (n k : ℕ) (g : EquivariantForm (deckRepresentation n) univ (k + 1)) :
    CompactSupportForm (deckRepresentation n) univ k →ₗ[ℝ] ℝ :=
  (quotientPairingFunctional n (k + 1) g).comp (compactDifferential (deckRepresentation n) isOpen_univ k) -
    quotientPairingFunctional n k (equivariantAdjoint n k g)

/-- Genuine quotient integration by parts, proved by actual finite smooth chart decomposition. -/
theorem integral_differential_equivariantAdjoint (n k : ℕ)
    (f : CompactSupportForm (deckRepresentation n) univ k)
    (g : EquivariantForm (deckRepresentation n) univ (k + 1)) :
    ∫ q, scalarPairing n (k + 1) (compactDifferential (deckRepresentation n) isOpen_univ k f).val g q ∂orbitVolume =
      ∫ q, scalarPairing n k f.val (equivariantAdjoint n k g) q ∂orbitVolume := by
  have hz : adjointDefect n k g f = 0 :=
    CompactFormFiniteCharts.functional_eq_zero (deckRepresentation n) k (adjointDefect n k g)
      (fun S a ha => sub_eq_zero.mpr
        (integral_differential_equivariantAdjoint_chart n k S a g ha)) f
  exact sub_eq_zero.mp hz

/-- The actual compact exterior derivative and compact adjoint are formal adjoints for orbitVolume. -/
theorem integral_compactDifferential_compactAdjoint (n k : ℕ)
    (f : CompactSupportForm (deckRepresentation n) univ k)
    (g : CompactSupportForm (deckRepresentation n) univ (k + 1)) :
    ∫ q, scalarPairing n (k + 1) (compactDifferential (deckRepresentation n) isOpen_univ k f).val g.val q ∂orbitVolume =
      ∫ q, scalarPairing n k f.val (compactAdjoint n k g).val q ∂orbitVolume :=
  integral_differential_equivariantAdjoint n k f g.val

end TernaryPoly.PolynomialFormCoordinates
