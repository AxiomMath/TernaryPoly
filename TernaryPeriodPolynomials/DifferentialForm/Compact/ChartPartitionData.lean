module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.ScalarTransport
public import TernaryPeriodPolynomials.DifferentialForm.Chart.CutoffPair

@[expose] public section


/-! Genuine finite compact chart partition data, with an explicit neighborhood plateau. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
open scoped ContDiff Manifold

structure CompactChartPartitionData (K : Set OrbitSpace) where
  charts : Finset Space
  scalar : charts → OrbitSpace → ℝ
  smooth : ∀ i, ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ (scalar i)
  compact : ∀ i, HasCompactSupport (scalar i)
  support : ∀ i, tsupport (scalar i) ⊆ (quotientChart i.val).source
  cutoff : ∀ i : charts, ChartCutoffPair i.val
  inner_eq : ∀ i, (cutoff i).inner = coordinateScalar i.val (scalar i)
  outer_mul : ∀ i, (cutoff i).outer * (cutoff i).inner = (cutoff i).inner
  neighborhood : Set OrbitSpace
  neighborhood_open : IsOpen neighborhood
  subset_neighborhood : K ⊆ neighborhood
  sum_one : ∀ q ∈ neighborhood, ∑ i, scalar i q = 1

theorem exists_compactChartPartitionData (K : Set OrbitSpace) (hK : IsCompact K) :
    Nonempty (CompactChartPartitionData K) := by
  classical
  obtain ⟨s, ψ, hψ, hcψ, hsψ, _, U, hU, hKU, hsum⟩ :=
    exists_finite_compact_scalar_partition K hK
  have ho (i : s) := exists_coordinateScalar_outer_cutoff i.val (ψ i) (hψ i) (hcψ i) (hsψ i)
  choose η hη hcη hsη he using ho
  refine ⟨{
    charts := s
    scalar := ψ
    smooth := hψ
    compact := hcψ
    support := hsψ
    cutoff := fun i => {
      inner := coordinateScalar i.val (ψ i)
      outer := η i
      inner_smooth := (coordinateScalar_properties i.val (ψ i) (hψ i) (hcψ i) (hsψ i)).1
      inner_compact := (coordinateScalar_properties i.val (ψ i) (hψ i) (hcψ i) (hsψ i)).2.1
      inner_support := (coordinateScalar_properties i.val (ψ i) (hψ i) (hcψ i) (hsψ i)).2.2
      outer_smooth := hη i
      outer_compact := hcη i
      outer_support := hsη i
    }
    inner_eq := fun _ => rfl
    outer_mul := he
    neighborhood := U
    neighborhood_open := hU
    subset_neighborhood := hKU
    sum_one := hsum
  }⟩

end TernaryPoly.PolynomialFormCoordinates
