module

public import TernaryPeriodPolynomials.SymmetricSpace.ChartsHomeomorph
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.Compactness.LocallyCompact

@[expose] public section


noncomputable section
open Topology Set
namespace TernaryPoly.SymmetricSpaceCovering
open SymmetricSpacePositive SymmetricSpaceCharts

/-- Local compactness of the actual positive trace-one space follows from its open five-chart. -/
instance spaceLocallyCompact : LocallyCompactSpace Space := by
  let : LocallyCompactSpace PositiveCoordinates := isOpen_positiveCoordinates.locallyCompactSpace
  exact chartHomeomorph.locallyCompactSpace_iff.mpr inferInstance

/-- The literal five coordinates define an open embedding into R^5. -/
theorem coordinateEmbedding : IsOpenEmbedding (fun S : Space => extract S.val) :=
  isOpen_positiveCoordinates.isOpenEmbedding_subtypeVal.comp chartHomeomorph.isOpenEmbedding

/-- The actual global partial chart has all forms as its source and the positivity domain as target. -/
def coordinateChart : OpenPartialHomeomorph Space Coordinates :=
  coordinateEmbedding.toOpenPartialHomeomorph (fun S : Space => extract S.val)

@[simp] theorem coordinateChart_apply (S : Space) : coordinateChart S=extract S.val := rfl

@[simp] theorem coordinateChart_source : coordinateChart.source=Set.univ := rfl

@[simp] theorem coordinateChart_target : coordinateChart.target=positiveCoordinates := by
  rw [coordinateChart,IsOpenEmbedding.toOpenPartialHomeomorph_target]
  ext x
  constructor
  · rintro ⟨S,rfl⟩
    exact extract_mem S
  · intro hx
    refine ⟨chartHomeomorph.symm ⟨x,hx⟩,?_⟩
    exact congrArg Subtype.val (chartHomeomorph.apply_symm_apply ⟨x,hx⟩)

/-- The inverse chart reconstructs the exact symmetric trace-one matrix. -/
theorem coordinateChart_inverse (x : Coordinates) (hx : x∈positiveCoordinates) :
    (coordinateChart.symm x).val=reconstruct x := by
  have he : extract (coordinateChart.symm x).val=x :=
    coordinateChart.right_inv (coordinateChart_target.symm ▸ hx)
  calc
    _ = reconstruct (extract (coordinateChart.symm x).val) :=
      (reconstruct_extract _ (Matrix.isHermitian_iff_isSymm.mp
        (coordinateChart.symm x).property.1.isHermitian) (coordinateChart.symm x).property.2).symm
    _ = reconstruct x := congrArg reconstruct he

end TernaryPoly.SymmetricSpaceCovering
