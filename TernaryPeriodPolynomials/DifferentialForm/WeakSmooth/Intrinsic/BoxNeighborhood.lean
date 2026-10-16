module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.ChartGeometry
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.BoxNeighborhood

@[expose] public section

/-! Genuine intrinsic coordinate-box neighborhoods subordinate to any quotient open. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothCoveringDeRham
  SymmetricSpaceQuotientManifold

/-- Every point of an actual quotient open has an actual coordinate-box neighborhood contained
in that open, in a genuine quotient chart. -/
theorem exists_intrinsic_coordinateTestBox (U : Set OrbitSpace) (hU : IsOpen U)
    (q : OrbitSpace) (hq : q ∈ U) :
    ∃ (S : Space) (b : WeakCubeFive ≃L[ℝ] Coordinates) (c : Coordinates),
      q ∈ chartOpen S (coordinateTestBox b c) ∧
      (coordinateTestBox b c : Set Coordinates) ⊆ chartDomain S U := by
  obtain ⟨S, hS⟩ := quotientCharts_cover q
  have hx : quotientChart S q ∈ chartDomain S U :=
    ⟨(quotientChart S).map_source hS, by
      change (quotientChart S).symm (quotientChart S q) ∈ U
      simpa only [(quotientChart S).left_inv hS] using hq⟩
  obtain ⟨b, c, hbc, hsub, _⟩ := exists_coordinateTestBox_in_open (chartDomain_isOpen S hU) hx
  exact ⟨S, b, c, ⟨hS, hbc⟩, hsub⟩

end TernaryPoly.PolynomialFormWeakSmooth
