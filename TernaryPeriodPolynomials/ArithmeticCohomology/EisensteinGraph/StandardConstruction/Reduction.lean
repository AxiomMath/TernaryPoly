module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BoundaryExactness

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

noncomputable section


namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.Reduction

def canonicalStratumHecke (degree : ℕ) (character : RankOneCharacter) :
    (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 degree character side) :=
  fun side => Helpers.canonicalHecke
    (flagRepresentation (rationalCoefficientComponent degree character) side)

theorem canonicalStratumHecke_realizes (degree : ℕ) (character : RankOneCharacter)
    (side : Side) :
    RealizesHecke (flagRepresentation (rationalCoefficientComponent degree character) side)
      (canonicalStratumHecke degree character side) :=
  Helpers.canonicalHecke_realizes _

theorem stratumHecke_unique (degree : ℕ) (character : RankOneCharacter)
    (hecke : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 degree character side))
    (realizes : ∀ side, RealizesHecke
      (flagRepresentation (rationalCoefficientComponent degree character) side) (hecke side)) :
    hecke = canonicalStratumHecke degree character := by
  funext side
  exact Helpers.canonicalHecke_unique _ _ (realizes side)

def projectedRestriction {degree : ℕ} (data : InducingData degree)
    (projection : Module.End ℂ (BoundaryCoordinates degree data.chi)) :
    WholeGlobalH2 degree data.chi →ₗ[ℂ] BoundaryCoordinates degree data.chi :=
  projection.comp ((Helpers.canonicalCoordinates degree data.chi).comp
    (Helpers.canonicalRestriction degree data.chi))

def spectralGraph {degree : ℕ} (data : InducingData degree)
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line) :
    Set (BoundaryCoordinates degree data.chi) :=
  {coordinates | ∃ planeClass : boundarySummand data .plane,
    coordinates = (planeClass.val, (standard planeClass).val)}

def spectralGraphSubmodule {degree : ℕ} (data : InducingData degree)
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line) :
    Submodule ℂ (BoundaryCoordinates degree data.chi) where
  carrier := spectralGraph data standard
  zero_mem' := by
    refine ⟨0, ?_⟩
    apply Prod.ext <;> simp
  add_mem' := by
    rintro first second ⟨firstClass, rfl⟩ ⟨secondClass, rfl⟩
    refine ⟨firstClass + secondClass, ?_⟩
    simp
  smul_mem' := by
    rintro scalar coordinates ⟨planeClass, rfl⟩
    refine ⟨scalar • planeClass, ?_⟩
    simp

noncomputable def planeGraphEquiv {degree : ℕ} (data : InducingData degree)
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line) :
    boundarySummand data .plane ≃ₗ[ℂ] spectralGraphSubmodule data standard where
  toFun planeClass := ⟨(planeClass.val, (standard planeClass).val), ⟨planeClass, rfl⟩⟩
  invFun graphClass := Classical.choose graphClass.property
  left_inv planeClass := by
    apply Subtype.ext
    change (Classical.choose
      (show ∃ candidate : boundarySummand data .plane,
        (planeClass.val, (standard planeClass).val) =
          (candidate.val, (standard candidate).val) from ⟨planeClass, rfl⟩)).val =
        planeClass.val
    have selected := Classical.choose_spec
      (show ∃ candidate : boundarySummand data .plane,
        (planeClass.val, (standard planeClass).val) =
          (candidate.val, (standard candidate).val) from ⟨planeClass, rfl⟩)
    exact (congrArg Prod.fst selected).symm
  right_inv graphClass := by
    apply Subtype.ext
    exact (Classical.choose_spec graphClass.property).symm
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar planeClass := by
    apply Subtype.ext
    simp

theorem spectralGraph_finrank_eq_plane {degree : ℕ} (data : InducingData degree)
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    :
    Module.finrank ℂ ↥(spectralGraphSubmodule data standard) =
      Module.finrank ℂ ↥(boundarySummand data .plane) := by
  let equivalence := planeGraphEquiv data standard
  exact equivalence.finrank_eq.symm

theorem spectralGraph_finiteDimensional {degree : ℕ} (data : InducingData degree)
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    [FiniteDimensional ℂ ↥(boundarySummand data .plane)] :
    FiniteDimensional ℂ ↥(spectralGraphSubmodule data standard) := by
  let equivalence := planeGraphEquiv data standard
  exact FiniteDimensional.of_injective equivalence.symm.toLinearMap
    equivalence.symm.injective

theorem range_eq_spectralGraph_of_finrank
    {degree : ℕ} (data : InducingData degree)
    (projection : Module.End ℂ (BoundaryCoordinates degree data.chi))
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    [FiniteDimensional ℂ ↥(spectralGraphSubmodule data standard)]
    (imageInGraph : LinearMap.range (projectedRestriction data projection) ≤
      spectralGraphSubmodule data standard)
    (dimensionEquality : Module.finrank ℂ ↥(LinearMap.range
      (projectedRestriction data projection)) =
      Module.finrank ℂ ↥(spectralGraphSubmodule data standard)) :
    (LinearMap.range (projectedRestriction data projection) :
      Set (BoundaryCoordinates degree data.chi)) = spectralGraph data standard := by
  have equality := Submodule.eq_of_le_of_finrank_eq imageInGraph dimensionEquality
  change (LinearMap.range (projectedRestriction data projection) :
    Set (BoundaryCoordinates degree data.chi)) =
      (spectralGraphSubmodule data standard : Set (BoundaryCoordinates degree data.chi))
  exact congrArg (fun submodule : Submodule ℂ (BoundaryCoordinates degree data.chi) =>
    (submodule : Set (BoundaryCoordinates degree data.chi))) equality

theorem range_eq_spectralGraph_of_finrank_eq_plane
    {degree : ℕ} (data : InducingData degree)
    (projection : Module.End ℂ (BoundaryCoordinates degree data.chi))
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    [FiniteDimensional ℂ ↥(spectralGraphSubmodule data standard)]
    (imageInGraph : LinearMap.range (projectedRestriction data projection) ≤
      spectralGraphSubmodule data standard)
    (imageFinrank : Module.finrank ℂ ↥(LinearMap.range
      (projectedRestriction data projection)) =
      Module.finrank ℂ ↥(boundarySummand data .plane)) :
    (LinearMap.range (projectedRestriction data projection) :
      Set (BoundaryCoordinates degree data.chi)) = spectralGraph data standard := by
  apply range_eq_spectralGraph_of_finrank data projection standard imageInGraph
  calc
    Module.finrank ℂ ↥(LinearMap.range (projectedRestriction data projection)) =
        Module.finrank ℂ ↥(boundarySummand data .plane) := imageFinrank
    _ = Module.finrank ℂ ↥(spectralGraphSubmodule data standard) :=
      (spectralGraph_finrank_eq_plane data standard).symm

theorem graphConclusion_iff {degree : ℕ} (data : InducingData degree) :
    GraphConclusion data ↔
      SourceComparisonExists data ∧
      (boundarySummand data .plane ≤
          LinearMap.ker (BoundaryExactness.endpointPullH2 degree data.chi .plane) ∧
        boundarySummand data .line ≤
          LinearMap.ker (BoundaryExactness.endpointPullH2 degree data.chi .line)) ∧
      ∃ (projection : Module.End ℂ (BoundaryCoordinates degree data.chi))
        (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line),
        IsIsotypicalProjection data (canonicalStratumHecke degree data.chi) projection ∧
        (∀ alternative, IsIsotypicalProjection data
          (canonicalStratumHecke degree data.chi) alternative → alternative = projection) ∧
        RealizesStandard data standard ∧
        (LinearMap.range (projectedRestriction data projection) :
          Set (BoundaryCoordinates degree data.chi)) = spectralGraph data standard := by
  constructor
  · rintro ⟨comparison, restriction, coordinates, hecke, projection, standard,
      restrictionRealizes, coordinatesRealizes, lifts, heckeRealizes, projects,
      projectionUnique, standardRealizes, graphEquality⟩
    have restrictionEquality := Helpers.canonicalRestriction_unique degree data.chi
      restriction restrictionRealizes
    have coordinatesEquality := Helpers.canonicalCoordinates_unique degree data.chi
      coordinates coordinatesRealizes
    have heckeEquality := stratumHecke_unique degree data.chi hecke heckeRealizes
    subst restriction coordinates hecke
    exact ⟨comparison, (BoundaryExactness.associatePair_lifts_iff data).mp lifts,
      projection, standard, projects, projectionUnique, standardRealizes, graphEquality⟩
  · rintro ⟨comparison, edgeVanishes, projection, standard, projects, projectionUnique,
      standardRealizes, graphEquality⟩
    exact ⟨comparison, Helpers.canonicalRestriction degree data.chi,
      Helpers.canonicalCoordinates degree data.chi, canonicalStratumHecke degree data.chi,
      projection, standard, Helpers.canonicalRestriction_realizes degree data.chi,
      Helpers.canonicalCoordinates_realizes degree data.chi,
      (BoundaryExactness.associatePair_lifts_iff data).mpr edgeVanishes,
      canonicalStratumHecke_realizes degree data.chi,
      projects, projectionUnique, standardRealizes, graphEquality⟩

theorem isotypicalProjection_idempotent {degree : ℕ} (data : InducingData degree)
    (hecke : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 degree data.chi side))
    (projection : Module.End ℂ (BoundaryCoordinates degree data.chi))
    (projects : IsIsotypicalProjection data hecke projection) :
    projection.comp projection = projection := by
  apply LinearMap.ext
  intro coordinates
  exact projects.2.1 (projection coordinates)
    (projects.1 ▸ LinearMap.mem_range_self projection coordinates)

theorem isotypicalProjection_pairStable {degree : ℕ} (data : InducingData degree)
    (hecke : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 degree data.chi side))
    (projection : Module.End ℂ (BoundaryCoordinates degree data.chi))
    (projects : IsIsotypicalProjection data hecke projection)
    (correspondence : HeckeCorrespondence) (coordinates : BoundaryCoordinates degree data.chi)
    (membership : coordinates ∈ associatePair data) :
    pairHecke data hecke correspondence coordinates ∈ associatePair data := by
  rw [← projects.1]
  refine ⟨pairHecke data hecke correspondence coordinates, ?_⟩
  have commutes := congrArg (fun operator => operator coordinates) (projects.2.2 correspondence)
  change projection (pairHecke data hecke correspondence coordinates) =
    pairHecke data hecke correspondence (projection coordinates) at commutes
  rw [projects.2.1 coordinates membership] at commutes
  exact commutes

theorem projectedRestriction_hecke {degree : ℕ} (data : InducingData degree)
    (projection : Module.End ℂ (BoundaryCoordinates degree data.chi))
    (projects : IsIsotypicalProjection data (canonicalStratumHecke degree data.chi) projection)
    (correspondence : HeckeCorrespondence) :
    (projectedRestriction data projection).comp
        (Helpers.canonicalHecke (rationalCoefficientComponent degree data.chi) correspondence) =
      (pairHecke data (canonicalStratumHecke degree data.chi) correspondence).comp
        (projectedRestriction data projection) := by
  have restrictHecke := Helpers.canonicalCoordinates_restriction_hecke degree data.chi
    correspondence
  have commutes := projects.2.2 correspondence
  exact ((LinearMap.comp_assoc _ _ _).trans
    (congrArg projection.comp restrictHecke)).trans
    ((LinearMap.comp_assoc _ _ _).symm.trans
    ((congrArg (fun operator => operator.comp
      ((Helpers.canonicalCoordinates degree data.chi).comp
        (Helpers.canonicalRestriction degree data.chi))) commutes).trans
    (LinearMap.comp_assoc _ _ _)))

theorem graph_equality_iff {degree : ℕ} (data : InducingData degree)
    (projection : Module.End ℂ (BoundaryCoordinates degree data.chi))
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line) :
    (LinearMap.range (projectedRestriction data projection) :
      Set (BoundaryCoordinates degree data.chi)) = spectralGraph data standard ↔
      (∀ globalClass, ∃ planeClass : boundarySummand data .plane,
        projectedRestriction data projection globalClass =
          (planeClass.val, (standard planeClass).val)) ∧
      (∀ planeClass : boundarySummand data .plane, ∃ globalClass,
        projectedRestriction data projection globalClass =
          (planeClass.val, (standard planeClass).val)) := by
  constructor
  · intro graphEquality
    constructor
    · intro globalClass
      have membership : projectedRestriction data projection globalClass ∈
          (LinearMap.range (projectedRestriction data projection) :
            Set (BoundaryCoordinates degree data.chi)) :=
        LinearMap.mem_range_self (projectedRestriction data projection) globalClass
      rw [graphEquality] at membership
      exact membership
    · intro planeClass
      have membership : (planeClass.val, (standard planeClass).val) ∈ spectralGraph data standard :=
        ⟨planeClass, rfl⟩
      rw [← graphEquality] at membership
      exact membership
  · rintro ⟨imageInGraph, graphInImage⟩
    apply Set.ext
    intro coordinates
    constructor
    · rintro ⟨globalClass, rfl⟩
      exact imageInGraph globalClass
    · rintro ⟨planeClass, rfl⟩
      exact graphInImage planeClass

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.Reduction
