module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Pairing
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Differential
public import TernaryPeriodPolynomials.DifferentialForm.Compact.Adjoint

@[expose] public section


/-! Genuine quotient integration by parts for a first form compactly supported in one chart. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialCoefficientMetric PolynomialFormMetric SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold SymmetricSpaceRiemannian SmoothCoveringDeRham SmoothLocalDeRham
open Set MeasureTheory
open scoped ContDiff SymmetricSpaceRiemannian

/-- Actual chartwise quotient identity, with no compact-support requirement on the second form. -/
theorem integral_differential_equivariantAdjoint_chart (n k : ℕ) (S : Space)
    (f : CompactSupportForm (deckRepresentation n) univ k)
    (g : EquivariantForm (deckRepresentation n) univ (k + 1))
    (hs : quotientSupport f.val ⊆ (quotientChart S).source) :
    ∫ q, scalarPairing n (k + 1) (compactDifferential (deckRepresentation n) isOpen_univ k f).val g q ∂orbitVolume =
      ∫ q, scalarPairing n k f.val (equivariantAdjoint n k g) q ∂orbitVolume := by
  let a := (globalChartRepresentative (deckRepresentation n) S k f.val).val
  have ha : ContDiffOn ℝ ∞ a positiveCoordinates := (contDiff_globalChartRepresentative n k S f hs).contDiffOn
  have hac : HasCompactSupport a := hasCompactSupport_globalChartRepresentative n k S f hs
  have has : tsupport a ⊆ positiveCoordinates :=
    (tsupport_globalChartRepresentative_target n k S f hs).trans (quotientChart_target_subset S)
  have hg : ContDiffOn ℝ ∞ g.val.val positiveCoordinates := by
    simpa only [liftedDomain_univ] using Form.smooth g.val
  calc
    _ = localIntegral n (k + 1) (extDeriv a) g.val.val := by
      have he := integral_scalarPairing_chart n (k + 1) S
        (compactDifferential (deckRepresentation n) isOpen_univ k f) g
        ((quotientSupport_differential isOpen_univ f.val).trans hs)
      exact he.trans (congrArg (fun z => localIntegral n (k + 1) z g.val.val)
        (globalChartRepresentative_compactDifferential n k S f hs))
    _ = localIntegral n k a (localAdjoint n k g.val.val) :=
      integral_extDeriv_localAdjoint_test n k a g.val.val ha hg hac has
    _ = localIntegral n k a (equivariantAdjoint n k g).val.val := by
      apply localIntegral_congr n k (fun _ _ => rfl)
        (fun _ hx => (equivariantAdjoint_apply n k g hx).symm)
      · intro x hx
        exact image_eq_zero_of_notMem_tsupport (fun ht => hx (has ht))
      · intro x hx
        exact image_eq_zero_of_notMem_tsupport (fun ht => hx (has ht))
    _ = _ := (integral_scalarPairing_chart n k S f (equivariantAdjoint n k g) hs).symm

end TernaryPoly.PolynomialFormCoordinates
