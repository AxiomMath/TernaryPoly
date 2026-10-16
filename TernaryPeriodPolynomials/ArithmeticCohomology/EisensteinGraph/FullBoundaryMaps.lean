module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.FullBoundary

@[expose] public section


/-! Ported from the Sol reference implementation. -/

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.FullBoundaryMaps

open GeneralEisenstein GeneralEisenstein.Homogeneous

def restrictionCochain (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (count : ℕ) : cochains rationalLevel (rationalCoefficientComponent degree character) count →ₗ[ℂ]
      MaximalCochains degree character side count where
  toFun representative := ⟨fun vertices _ => representative.val vertices, by
    intro element vertices
    funext flag
    exact representative.property element vertices⟩
  map_add' first second := rfl
  map_smul' scalar representative := rfl

def globalBoundaryCycleMap (degree : ℕ) (character : RankOneCharacter) :
    cocycles rationalLevel (rationalCoefficientComponent degree character) →ₗ[ℂ]
      fullBoundaryCycles degree character where
  toFun := globalBoundaryCocycle degree character
  map_add' first second := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (zero_add _).symm
  map_smul' scalar representative := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (smul_zero scalar).symm

theorem globalBoundaryCocycle_boundary (degree : ℕ) (character : RankOneCharacter)
    (representative : cochains rationalLevel (rationalCoefficientComponent degree character) 1) :
    IsBoundaryCoboundary degree character
      (globalBoundaryCocycle degree character (boundaryMap _ _ representative)) := by
  refine ⟨restrictionCochain degree character .plane 1 representative,
    restrictionCochain degree character .line 1 representative, 0, rfl, rfl, ?_⟩
  intro vertices edge
  change 0 = representative.val vertices - representative.val vertices - (0 - 0)
  simp

def fullRestriction (degree : ℕ) (character : RankOneCharacter) :
    WholeGlobalH2 degree character →ₗ[ℂ] FullBoundaryH2 degree character :=
  (LinearMap.range (boundaryMap rationalLevel (rationalCoefficientComponent degree character))).liftQ
    ((fullBoundaryClass degree character).comp (globalBoundaryCycleMap degree character)) (by
      rintro representative ⟨incoming, rfl⟩
      rw [LinearMap.mem_ker]
      change fullBoundaryClass degree character
        (globalBoundaryCocycle degree character (boundaryMap _ _ incoming)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.subset_span (globalBoundaryCocycle_boundary degree character incoming)))

theorem fullRestriction_realizes (degree : ℕ) (character : RankOneCharacter) :
    RealizesFullRestriction degree character (fullRestriction degree character) := by
  intro representative
  exact Submodule.liftQ_apply
    (LinearMap.range (boundaryMap rationalLevel (rationalCoefficientComponent degree character)))
    ((fullBoundaryClass degree character).comp (globalBoundaryCycleMap degree character)) representative

def maximalCoordinates (degree : ℕ) (character : RankOneCharacter) :
    fullBoundaryCycles degree character →ₗ[ℂ] BoundaryCoordinates degree character where
  toFun representative :=
    (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree character) .plane)
        representative.val.1.1,
     classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree character) .line)
        representative.val.1.2)
  map_add' first second := by
    apply Prod.ext <;> exact map_add _ _ _
  map_smul' scalar representative := by
    apply Prod.ext <;> exact map_smul _ _ _

theorem maximalCoordinates_boundary (degree : ℕ) (character : RankOneCharacter)
    (representative : fullBoundaryCycles degree character)
    (boundary : IsBoundaryCoboundary degree character representative) :
    maximalCoordinates degree character representative = 0 := by
  obtain ⟨plane, line, _, plane_boundary, line_boundary, _⟩ := boundary
  apply Prod.ext
  · change classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .plane)
      representative.val.1.1 = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨plane, Subtype.ext plane_boundary.symm⟩
  · change classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .line)
      representative.val.1.2 = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨line, Subtype.ext line_boundary.symm⟩

def boundaryCoordinates (degree : ℕ) (character : RankOneCharacter) :
    FullBoundaryH2 degree character →ₗ[ℂ] BoundaryCoordinates degree character :=
  (fullBoundaryRelations degree character).liftQ (maximalCoordinates degree character) (by
    apply Submodule.span_le.mpr
    intro representative boundary
    exact maximalCoordinates_boundary degree character representative boundary)

theorem boundaryCoordinates_realizes (degree : ℕ) (character : RankOneCharacter) :
    RealizesBoundaryCoordinates degree character (boundaryCoordinates degree character) := by
  intro representative
  rfl

theorem fullRestriction_unique (degree : ℕ) (character : RankOneCharacter)
    (restriction : WholeGlobalH2 degree character →ₗ[ℂ] FullBoundaryH2 degree character)
    (actual : RealizesFullRestriction degree character restriction) :
    restriction = fullRestriction degree character := by
  apply LinearMap.ext
  intro coordinate
  obtain ⟨representative, rfl⟩ :=
    (LinearMap.range (boundaryMap rationalLevel
      (rationalCoefficientComponent degree character))).mkQ_surjective coordinate
  exact (actual representative).trans ((fullRestriction_realizes degree character representative).symm)

theorem boundaryCoordinates_unique (degree : ℕ) (character : RankOneCharacter)
    (coordinates : FullBoundaryH2 degree character →ₗ[ℂ] BoundaryCoordinates degree character)
    (actual : RealizesBoundaryCoordinates degree character coordinates) :
    coordinates = boundaryCoordinates degree character := by
  apply (fullBoundaryRelations degree character).linearMap_qext
  apply LinearMap.ext
  intro representative
  exact (actual representative).trans
    ((boundaryCoordinates_realizes degree character representative).symm)

def restriction (degree : ℕ) (character : RankOneCharacter) :
    WholeGlobalH2 degree character →ₗ[ℂ] BoundaryCoordinates degree character :=
  (boundaryCoordinates degree character).comp (fullRestriction degree character)

theorem restriction_realizes (degree : ℕ) (character : RankOneCharacter) :
    RealizesRestriction degree character (restriction degree character) := by
  intro representative
  change boundaryCoordinates degree character
    (fullRestriction degree character (classOf rationalLevel
      (rationalCoefficientComponent degree character) representative)) = _
  rw [fullRestriction_realizes]
  exact boundaryCoordinates_realizes degree character (globalBoundaryCocycle degree character representative)

end TernaryPeriodPolynomials.EisensteinGraph.FullBoundaryMaps
