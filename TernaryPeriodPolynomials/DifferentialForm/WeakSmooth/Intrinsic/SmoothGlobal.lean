module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothChart
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.FiniteCharts

@[expose] public section


/-! Actual global faithfulness and differentiation of genuine local smooth quotient currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialCoefficientMetric PolynomialFormCoordinates SymmetricSpaceCharts
  SymmetricSpacePositive SymmetricSpaceCovering SmoothCoveringDeRham SmoothLocalDeRham
  SymmetricSpaceQuotientManifold

/-- Genuine smooth equivariant forms on any actual quotient open are separated by their actual
intrinsic compact-test currents. -/
theorem intrinsicSmoothCurrent_injective (n k : ℕ) (U : Set OrbitSpace) (hU : IsOpen U) :
    Function.Injective (intrinsicSmoothCurrent n k U hU) := by
  intro a b hab
  have hl (S : Space) :
      restrictEquivariant (deckRepresentation n)
        (chartOpen_subset_of_chartDomain S (Subset.rfl : chartDomain S U ⊆ chartDomain S U)) k a =
      restrictEquivariant (deckRepresentation n)
        (chartOpen_subset_of_chartDomain S (Subset.rfl : chartDomain S U ⊆ chartDomain S U)) k b := by
    let Ω : TopologicalSpace.Opens Coordinates := ⟨chartDomain S U, chartDomain_isOpen S hU⟩
    let hVU := chartOpen_subset_of_chartDomain S (Subset.rfl : chartDomain S U ⊆ chartDomain S U)
    apply intrinsicSmoothCurrent_chart_injective n k S Ω inter_subset_left
    exact (intrinsicSmoothCurrent_restriction n k hU (chartOpen_isOpen S Ω.isOpen) hVU a).symm.trans
      ((congrArg (intrinsicCurrentRestriction n k hVU) hab).trans
        (intrinsicSmoothCurrent_restriction n k hU (chartOpen_isOpen S Ω.isOpen) hVU b))
  apply Subtype.ext
  apply Form.ext
  intro x hx
  let q := coordinateProjection x
  let S := q.out
  have hq : q ∈ (quotientChart S).source := mem_chart_source Coordinates q
  have hxV : x ∈ liftedDomain (chartOpen S (chartDomain S U)) := by
    refine ⟨hx.1, ?_⟩
    rw [intrinsicChartOpen_chartDomain]
    exact ⟨hx.2, hq⟩
  have he := congrArg (fun z : EquivariantForm (deckRepresentation n)
    (chartOpen S (chartDomain S U)) k => z.val.val x) (hl S)
  exact (restrictEquivariant_apply (deckRepresentation n) _ a hxV).symm.trans
    (he.trans (restrictEquivariant_apply (deckRepresentation n) _ b hxV))

/-- The genuine intrinsic smooth-current embedding commutes with the actual exterior differential
on every actual quotient open. -/
theorem intrinsicSmoothCurrent_differential (n k : ℕ) (U : Set OrbitSpace) (hU : IsOpen U)
    (a : EquivariantForm (deckRepresentation n) U k) :
    intrinsicCurrentDifferential n k U (intrinsicSmoothCurrent n k U hU a) =
      intrinsicSmoothCurrent n (k+1) U hU (differential (deckRepresentation n) hU k a) := by
  apply intrinsicCurrent_ext_chartDomains n (k+1) U
  intro S
  let Ω : TopologicalSpace.Opens Coordinates := ⟨chartDomain S U, chartDomain_isOpen S hU⟩
  let hVU := chartOpen_subset_of_chartDomain S (Subset.rfl : chartDomain S U ⊆ chartDomain S U)
  apply (intrinsicCurrentRestriction_differential n k hVU _).trans
  apply (congrArg (intrinsicCurrentDifferential n k (chartOpen S Ω))
    (intrinsicSmoothCurrent_restriction n k hU (chartOpen_isOpen S Ω.isOpen) hVU a)).trans
  apply (intrinsicSmoothCurrent_chart_differential n k S Ω inter_subset_left _).trans
  apply Eq.trans _ (intrinsicSmoothCurrent_restriction n (k+1) hU
    (chartOpen_isOpen S Ω.isOpen) hVU _).symm
  exact congrArg (intrinsicSmoothCurrent n (k+1) (chartOpen S Ω) (chartOpen_isOpen S Ω.isOpen))
    (restrictEquivariant_d (deckRepresentation n) hU (chartOpen_isOpen S Ω.isOpen) hVU a).symm

end TernaryPoly.PolynomialFormWeakSmooth
