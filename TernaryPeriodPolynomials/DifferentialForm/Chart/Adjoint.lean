module

public import TernaryPeriodPolynomials.DifferentialForm.Compact.Chart
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Locality
public import TernaryPeriodPolynomials.DifferentialForm.Compact.Adjoint

@[expose] public section


/-! The actual compact adjoint has its exact globally zero-extended chart expression. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialCoefficientMetric PolynomialFormMetric SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
  SmoothCoveringDeRham SmoothLocalDeRham Set Filter
open scoped Topology

theorem globalChartRepresentative_compactAdjoint (n k : ℕ) (S : Space)
    (f : CompactSupportForm (deckRepresentation n) univ (k+1))
    (hs : quotientSupport f.val ⊆ (quotientChart S).source) :
    (globalChartRepresentative (deckRepresentation n) S k (compactAdjoint n k f).val).val =
      localAdjoint n k (globalChartRepresentative (deckRepresentation n) S (k+1) f.val).val := by
  funext x
  by_cases hx : x ∈ (quotientChart S).target
  · have he : (globalChartRepresentative (deckRepresentation n) S (k+1) f.val).val =ᶠ[𝓝 x] f.val.val.val := by
      filter_upwards [(quotientChart S).open_target.mem_nhds hx] with y hy
      exact globalChartRepresentative_apply (deckRepresentation n) S f.val hy
    calc
      _ = (compactAdjoint n k f).val.val.val x := globalChartRepresentative_apply (deckRepresentation n) S _ hx
      _ = localAdjoint n k f.val.val.val x := compactAdjoint_apply n k f (quotientChart_target_subset S hx)
      _ = _ := (localAdjoint_congr n k he).symm
  · rw [Form.outside _ hx]
    exact (image_eq_zero_of_notMem_tsupport
      (fun ht => hx (tsupport_globalChartRepresentative_target n (k+1) S f hs
        (tsupport_localAdjoint n k (globalChartRepresentative (deckRepresentation n) S (k+1) f.val).val ht)))).symm

end TernaryPoly.PolynomialFormCoordinates
