module

public import TernaryPeriodPolynomials.DifferentialForm.Compact.Chart
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Locality

@[expose] public section


/-! The actual differential commutes with the genuine compact chart representative globally. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialCoefficientMetric SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold SmoothCoveringDeRham SmoothLocalDeRham Set Filter
open scoped Topology

/-- For compact chart support, the zero-extended chart differential is literally extDeriv everywhere. -/
theorem globalChartRepresentative_compactDifferential (n k : ℕ) (S : Space)
    (f : CompactSupportForm (deckRepresentation n) univ k)
    (hs : quotientSupport f.val ⊆ (quotientChart S).source) :
    (globalChartRepresentative (deckRepresentation n) S (k + 1)
      (compactDifferential (deckRepresentation n) isOpen_univ k f).val).val =
        extDeriv (globalChartRepresentative (deckRepresentation n) S k f.val).val := by
  funext x
  by_cases hx : x ∈ (quotientChart S).target
  · have he : (globalChartRepresentative (deckRepresentation n) S k f.val).val =ᶠ[𝓝 x]
        f.val.val.val := by
      filter_upwards [(quotientChart S).open_target.mem_nhds hx] with y hy
      exact globalChartRepresentative_apply (deckRepresentation n) S f.val hy
    calc
      _ = (compactDifferential (deckRepresentation n) isOpen_univ k f).val.val.val x :=
        globalChartRepresentative_apply (deckRepresentation n) S _ hx
      _ = extDeriv f.val.val.val x :=
        d_apply (liftedDomain_isOpen isOpen_univ) f.val.val
          (by simpa only [liftedDomain_univ] using quotientChart_target_subset S hx)
      _ = _ := he.extDeriv_eq.symm
  · rw [Form.outside _ hx]
    exact (extDeriv_eq_zero_of_notMem_tsupport n k _
      (fun ht => hx (tsupport_globalChartRepresentative_target n k S f hs ht))).symm

end TernaryPoly.PolynomialFormCoordinates
