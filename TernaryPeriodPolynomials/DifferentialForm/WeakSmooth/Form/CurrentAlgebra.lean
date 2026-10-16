module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.Differential

@[expose] public section


/-! Additive algebra of the actual exterior differential on actual form-valued currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialFormMetric SymmetricSpaceCharts

/-- The actual weak exterior differential preserves differences. -/
theorem formWeakExterior_sub (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (W Z : FormWeak n k Ω) :
    formWeakExterior n k Ω (W - Z) = formWeakExterior n k Ω W - formWeakExterior n k Ω Z := by
  apply LinearMap.ext
  intro φ
  simp only [formWeakExterior_apply, LinearMap.sub_apply, map_neg, map_sub,
    neg_sub, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  abel

end TernaryPoly.PolynomialFormWeakSmooth
