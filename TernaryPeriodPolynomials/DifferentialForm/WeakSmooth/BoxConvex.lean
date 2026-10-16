module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CubeGeometry

@[expose] public section


/-! Convexity and nonemptiness of actual affine coordinate test boxes. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set SymmetricSpaceCharts

theorem coordinateTestBox_convex (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates) :
    Convex ℝ (coordinateTestBox e a : Set Coordinates) := by
  rw [coordinateTestBox_eq_image]
  change Convex ℝ ((fun x => e x + a) '' (testCubeDomainFive : Set WeakCubeFive))
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ s t hs ht hst
  refine ⟨s • x + t • y, testCubeDomainFive_convex hx hy hs ht hst, ?_⟩
  change e (s • x + t • y) + a = s • (e x + a) + t • (e y + a)
  rw [map_add, map_smul, map_smul, smul_add, smul_add]
  have ha : s • a + t • a = a := by rw [← add_smul, hst, one_smul]
  calc
    _ = (s • e x + t • e y) + (s • a + t • a) := by rw [ha]
    _ = _ := by abel

theorem coordinateTestBox_nonempty (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates) :
    (coordinateTestBox e a : Set Coordinates).Nonempty := by
  rw [coordinateTestBox_eq_image]
  exact ⟨_, ⟨weakCubeCenter, weakCubeCenter_mem, rfl⟩⟩

end TernaryPoly.PolynomialFormWeakSmooth
