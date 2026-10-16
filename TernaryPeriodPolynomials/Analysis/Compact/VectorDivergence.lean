module

public import TernaryPeriodPolynomials.Analysis.Compact.Weighted.Divergence
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence

@[expose] public section


/-! Locality and compact Euclidean integration for the literal quotient metric divergence. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Filter MeasureTheory SymmetricSpaceCharts SymmetricSpaceRiemannian CompactCoordinateIntegration
open scoped ContDiff Topology

theorem weightedDivergence_congr {V W : Coordinates → Coordinates} {x : Coordinates}
    (h : V =ᶠ[𝓝 x] W) : weightedDivergence V x = weightedDivergence W x := by
  unfold weightedDivergence
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => coordinateDensity y * V y i) =ᶠ[𝓝 x]
      (fun y => coordinateDensity y * W y i) := by
    filter_upwards [h] with y hy
    rw [hy]
  rw [he.fderiv_eq]

theorem weightedDivergence_zero_of_notMem_tsupport (V : Coordinates → Coordinates)
    (x : Coordinates) (hx : x ∉ tsupport V) : weightedDivergence V x = 0 := by
  have he := weightedDivergence_congr (notMem_tsupport_iff_eventuallyEq.mp hx)
  exact he.trans (by simp only [weightedDivergence, Pi.zero_apply, mul_zero, fderiv_const_apply,
    _root_.zero_apply, Finset.sum_const_zero])

theorem integral_compact_weightedDivergence (V : Coordinates → Coordinates)
    (hV : ContDiff ℝ ∞ V) (hcV : HasCompactSupport V) (hsV : tsupport V ⊆ positiveCoordinates) :
    ∫ x, coordinateDensity x * weightedDivergence V x = 0 := by
  have hs (i : Fin 5) : tsupport (fun x => V x i) ⊆ tsupport V := by
    apply closure_mono
    intro x hx hv
    exact hx (congrFun hv i)
  exact integral_weighted_divergence_eq_zero isOpen_positiveCoordinates coordinateDensity
    contDiffOn_coordinateDensity (fun x hx => (coordinateDensity_pos x hx).ne')
    (fun i x => V x i) (fun i => Pi.single i 1)
    (fun i => contDiff_pi.mp hV i)
    (fun i => hcV.of_isClosed_subset (isClosed_tsupport _) (hs i))
    (fun i => (hs i).trans hsV)

end TernaryPoly.PolynomialFormConnection
