module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CoordinateBoxes
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Convex.Topology

@[expose] public section


/-! Geometric properties of the actual five-dimensional test box. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set

/-- The actual midpoint of the product box. -/
def weakCubeCenter : WeakCubeFive := (((((0, 1 / 2), 1 / 2), 1 / 2), 1 / 2), 1 / 2)

theorem weakCubeCenter_mem : weakCubeCenter ∈ testCubeDomainFive := by
  norm_num [weakCubeCenter, testCubeDomainFive, testCubeDomainFour, testCubeDomainThree,
    testCubeDomainTwo, testCubeDomainOne, testCubeDomainZero, testCylinder]

theorem testCubeDomainFive_isBounded : Bornology.IsBounded (testCubeDomainFive : Set WeakCubeFive) := by
  have h₀ : Bornology.IsBounded (testCubeDomainZero : Set WeakCubeZero) :=
    isCompact_univ.isBounded
  have hI : Bornology.IsBounded (Ioo (0 : ℝ) 1) := Metric.isBounded_Ioo _ _
  exact ((((h₀.prod hI).prod hI).prod hI).prod hI).prod hI

theorem testCubeDomainFive_convex : Convex ℝ (testCubeDomainFive : Set WeakCubeFive) := by
  have h₀ : Convex ℝ (testCubeDomainZero : Set WeakCubeZero) := convex_univ
  have hI : Convex ℝ (Ioo (0 : ℝ) 1) := convex_Ioo _ _
  exact ((((h₀.prod hI).prod hI).prod hI).prod hI).prod hI

/-- The literal affine image presentation of every coordinate test box. -/
theorem coordinateTestBox_eq_image (e : WeakCubeFive ≃L[ℝ] SymmetricSpaceCharts.Coordinates)
    (a : SymmetricSpaceCharts.Coordinates) :
    (coordinateTestBox e a : Set SymmetricSpaceCharts.Coordinates) =
      (affineTestHomeomorph e a) '' (testCubeDomainFive : Set WeakCubeFive) := by
  ext y
  change (affineTestHomeomorph e a).symm y ∈ (testCubeDomainFive : Set WeakCubeFive) ↔ _
  constructor
  · intro hy
    exact ⟨(affineTestHomeomorph e a).symm y, hy, (affineTestHomeomorph e a).apply_symm_apply y⟩
  · rintro ⟨z, hz, rfl⟩
    simpa only [(affineTestHomeomorph e a).symm_apply_apply] using hz

/-- Taking closure commutes with the actual affine box map. -/
theorem coordinateTestBox_closure (e : WeakCubeFive ≃L[ℝ] SymmetricSpaceCharts.Coordinates)
    (a : SymmetricSpaceCharts.Coordinates) :
    closure (coordinateTestBox e a : Set SymmetricSpaceCharts.Coordinates) =
      (affineTestHomeomorph e a) '' closure (testCubeDomainFive : Set WeakCubeFive) := by
  rw [coordinateTestBox_eq_image, (affineTestHomeomorph e a).image_closure]

/-- Every actual affine coordinate box has compact closure. -/
theorem coordinateTestBox_isCompact_closure
    (e : WeakCubeFive ≃L[ℝ] SymmetricSpaceCharts.Coordinates) (a : SymmetricSpaceCharts.Coordinates) :
    IsCompact (closure (coordinateTestBox e a : Set SymmetricSpaceCharts.Coordinates)) := by
  rw [coordinateTestBox_closure]
  exact testCubeDomainFive_isBounded.isCompact_closure.image (affineTestHomeomorph e a).continuous

end TernaryPoly.PolynomialFormWeakSmooth
