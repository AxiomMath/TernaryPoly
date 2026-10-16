module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.AffineIncidence
public import TernaryPeriodPolynomials.Building.BoundaryApartments.CycleGeneration

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

def apartmentChainImage : Submodule ℂ EdgeChains :=
  LinearMap.range (goodCycleModule.subtype.comp apartmentPresentationMap)

theorem affineTriangle_mem_apartmentChainImage (first second third : AffinePoint)
    (first_good : GoodFlag .line (affineLine first))
    (second_good : GoodFlag .line (affineLine second))
    (third_good : GoodFlag .line (affineLine third)) :
    matrixApartment (affineTriangleMatrix first second third) ∈ apartmentChainImage := by
  by_cases singular : (affineTriangleMatrix first second third).det = 0
  · rw [matrixApartment_singular _ singular]
    exact apartmentChainImage.zero_mem
  let frame := GeneralLinearGroup.mkOfDetNeZero (affineTriangleMatrix first second third) singular
  have line_eq (column : Fin 3) :
      (QuotientGroup.mk (frame * Adelic.weyl ^ column.val) : Flags .line) =
        affineLine (![first,second,third] column) := by
    symm
    apply line_flag_eq_of_column 1
    intro row
    rw [one_mul, affineFrame_firstColumn, frame_weylPower_firstColumn]
    fin_cases column
    · exact (affineTriangleMatrix_columns first second third row).1
    · exact (affineTriangleMatrix_columns first second third row).2.1
    · exact (affineTriangleMatrix_columns first second third row).2.2
  obtain ⟨symbols, value⟩ := good_rational_apartment_in_presentation frame (by
    intro column
    rw [line_eq]
    fin_cases column
    · exact first_good
    · exact second_good
    · exact third_good)
  change matrixApartment frame.val ∈ apartmentChainImage
  rw [matrixApartment_frame]
  exact ⟨symbols, value⟩

def goodLinePoint (line : Flags .line) : AffinePoint := by
  classical
  exact if good : GoodFlag .line line then Classical.choose (good_line_affinePoint line good) else 0

theorem goodLinePoint_spec (line : Flags .line) (good : GoodFlag .line line) :
    affineLine (goodLinePoint line) = line := by
  rw [goodLinePoint, dite_eq_left good]
  exact Classical.choose_spec (good_line_affinePoint line good)

theorem goodLinePoint_good (line : Flags .line) (good : GoodFlag .line line) :
    GoodFlag .line (affineLine (goodLinePoint line)) := by
  rw [goodLinePoint_spec line good]
  exact good

def goodPlaneEdge (plane : Flags .plane) : Edges := by
  classical
  exact if good : GoodFlag .plane plane then Classical.choose (good_plane_incident_edge plane good)
    else baseEdge

theorem goodPlaneEdge_spec (plane : Flags .plane) (good : GoodFlag .plane plane) :
    endpoint .plane (goodPlaneEdge plane) = plane ∧ GoodFlag .line (endpoint .line (goodPlaneEdge plane)) := by
  rw [goodPlaneEdge, dite_eq_left good]
  exact Classical.choose_spec (good_plane_incident_edge plane good)

theorem affineZero_good : GoodFlag .line (affineLine 0) := by
  refine ⟨![0,0,1], ⟨affineFrame 0, rfl, ![1,0,0], ⟨rfl, rfl⟩, ?_⟩, ?_⟩
  · ext row
    fin_cases row <;> simp [affineFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · change (1 : ZMod 3) ≠ 0
    exact one_ne_zero

def affineVertexPaths : BuildingVertices → EdgeChains
  | .inr line => affinePair 0 (goodLinePoint line)
  | .inl plane => Finsupp.single (goodPlaneEdge plane) 1 +
      affinePair 0 (goodLinePoint (endpoint .line (goodPlaneEdge plane)))

theorem affineVertexPaths_defect (edge : Edges)
    (plane_good : GoodFlag .plane (endpoint .plane edge))
    (line_good : GoodFlag .line (endpoint .line edge)) :
    edgePathDefect affineVertexPaths edge = matrixApartment (affineTriangleMatrix
      (goodLinePoint (endpoint .line edge))
      (goodLinePoint (endpoint .line (goodPlaneEdge (endpoint .plane edge)))) 0) := by
  let first := goodLinePoint (endpoint .line edge)
  let second := goodLinePoint (endpoint .line (goodPlaneEdge (endpoint .plane edge)))
  have plane_edge := goodPlaneEdge_spec (endpoint .plane edge) plane_good
  have pair := affinePair_of_incident_edges edge (goodPlaneEdge (endpoint .plane edge))
    plane_edge.1.symm first second (goodLinePoint_spec _ line_good).symm
    (goodLinePoint_spec _ plane_edge.2).symm
  change edgePathDefect affineVertexPaths edge = matrixApartment (affineTriangleMatrix first second 0)
  rw [← affinePair_triangle]
  change Finsupp.single edge 1 - (Finsupp.single (goodPlaneEdge (endpoint .plane edge)) 1 +
    affinePair 0 second) + affinePair 0 first = _
  rw [pair, affinePair_reverse (0 : AffinePoint) second]
  abel

theorem apartmentPresentationMap_surjective : Function.Surjective apartmentPresentationMap := by
  intro cycle
  have cycle_mem : cycle.val ∈ apartmentChainImage := by
    apply goodCycle_mem_of_edgePathDefects apartmentChainImage affineVertexPaths _ cycle.property
    intro edge plane_good line_good
    rw [affineVertexPaths_defect edge plane_good line_good]
    apply affineTriangle_mem_apartmentChainImage
    · exact goodLinePoint_good _ line_good
    · exact goodLinePoint_good _ (goodPlaneEdge_spec _ plane_good).2
    · exact affineZero_good
  obtain ⟨symbols, value⟩ := cycle_mem
  refine ⟨symbols, ?_⟩
  apply Subtype.ext
  exact value

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
