module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CubeGeometry

@[expose] public section


/-! Actual relatively compact affine boxes form neighborhoods in the genuine coordinate model. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set SymmetricSpaceCharts
open scoped Topology Pointwise

/-- The genuine invertible scaling of the fixed product-to-coordinate linear identification. -/
def scaledWeakCubeCoordinateEquiv (r : ℝ) (hr : r ≠ 0) : WeakCubeFive ≃L[ℝ] Coordinates :=
  weakCubeCoordinateEquiv.trans ((LinearEquiv.smulOfNeZero ℝ Coordinates r hr).toContinuousLinearEquiv)

@[simp] theorem scaledWeakCubeCoordinateEquiv_apply (r : ℝ) (hr : r ≠ 0) (z : WeakCubeFive) :
    scaledWeakCubeCoordinateEquiv r hr z = r • weakCubeCoordinateEquiv z := rfl

/-- Every genuine coordinate neighborhood contains the compact closure of an actual affine
box containing the designated point. The test-current exactness and rigidity results therefore
apply inside arbitrarily small chart neighborhoods. -/
theorem exists_coordinateTestBox_closure_subset {U : Set Coordinates} {x : Coordinates}
    (hU : U ∈ 𝓝 x) :
    ∃ (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates),
      x ∈ coordinateTestBox e a ∧ closure (coordinateTestBox e a : Set Coordinates) ⊆ U := by
  let S : Set Coordinates := (fun z : WeakCubeFive => weakCubeCoordinateEquiv (z - weakCubeCenter)) ''
    closure (testCubeDomainFive : Set WeakCubeFive)
  have hS : Bornology.IsBounded S :=
    (testCubeDomainFive_isBounded.isCompact_closure.image
      (weakCubeCoordinateEquiv.continuous.comp (continuous_id.sub continuous_const))).isBounded
  have he := eventually_singleton_add_smul_subset (𝕜 := ℝ) hS hU
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp he
  let r : ℝ := δ / 2
  have hr : 0 < r := half_pos hδ
  have hrδ : r ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr]
    exact half_lt_self hδ
  have hsub : {x} + r • S ⊆ U := hδU hrδ
  let e := scaledWeakCubeCoordinateEquiv r hr.ne'
  let a := x - e weakCubeCenter
  refine ⟨e, a, ?_, ?_⟩
  · change x ∈ (coordinateTestBox e a : Set Coordinates)
    rw [coordinateTestBox_eq_image]
    refine ⟨weakCubeCenter, weakCubeCenter_mem, ?_⟩
    change e weakCubeCenter + (x - e weakCubeCenter) = x
    abel
  · rw [coordinateTestBox_closure]
    rintro y ⟨z, hz, rfl⟩
    apply hsub
    have hsum : (affineTestHomeomorph e a) z =
        x + r • weakCubeCoordinateEquiv (z - weakCubeCenter) := by
      change r • weakCubeCoordinateEquiv z + (x - r • weakCubeCoordinateEquiv weakCubeCenter) = _
      rw [map_sub, smul_sub]
      abel
    rw [hsum]
    exact Set.add_mem_add (mem_singleton x)
      (smul_mem_smul_set ⟨z, hz, rfl⟩)

/-- Actual coordinate boxes form a basis of open neighborhoods, with compact closure. -/
theorem exists_coordinateTestBox_in_open {U : Set Coordinates} (hU : IsOpen U)
    {x : Coordinates} (hx : x ∈ U) :
    ∃ (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates),
      x ∈ coordinateTestBox e a ∧ (coordinateTestBox e a : Set Coordinates) ⊆ U ∧
      IsCompact (closure (coordinateTestBox e a : Set Coordinates)) := by
  obtain ⟨e, a, hxe, heU⟩ := exists_coordinateTestBox_closure_subset (hU.mem_nhds hx)
  exact ⟨e, a, hxe, subset_closure.trans heU, coordinateTestBox_isCompact_closure e a⟩

end TernaryPoly.PolynomialFormWeakSmooth
