module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ParabolicInvariance

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

noncomputable section


namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BoundaryExactness

abbrev EdgeH2 (degree : ℕ) (character : RankOneCharacter) :=
  H2 rationalLevel (functionRepresentation (rationalCoefficientComponent degree character) Edges)

def endpointPullCochain (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (count : ℕ) : MaximalCochains degree character side count →ₗ[ℂ]
      EdgeCochains degree character count where
  toFun representative :=
    ⟨fun vertices edge => representative.val vertices (endpoint side edge), by
      intro element vertices
      funext edge
      have equivariant := congrFun (representative.property element vertices) (endpoint side edge)
      change representative.val (fun index => element.val * vertices index) (endpoint side edge) =
        rationalCoefficientComponent degree character element.val
          (representative.val vertices (endpoint side (element.val⁻¹ • edge)))
      rw [endpoint_smul]
      exact equivariant⟩
  map_add' first second := rfl
  map_smul' scalar representative := rfl

theorem endpointPull_differentialOne (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (representative : MaximalCochains degree character side 1) :
    endpointPullCochain degree character side 2 (differentialOne _ _ representative) =
      differentialOne _ _ (endpointPullCochain degree character side 1 representative) := by
  rfl

def endpointPullCocycle (degree : ℕ) (character : RankOneCharacter) (side : Side) :
    MaximalCycles degree character side →ₗ[ℂ]
      cocycles rationalLevel
        (functionRepresentation (rationalCoefficientComponent degree character) Edges) :=
  ((endpointPullCochain degree character side 2).comp
    (MaximalCycles degree character side).subtype).codRestrict _ (by
    intro representative
    funext vertices edge
    exact congrFun (congrFun representative.property vertices) (endpoint side edge))

theorem endpointPull_boundaryMap (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (representative : MaximalCochains degree character side 1) :
    endpointPullCocycle degree character side (boundaryMap _ _ representative) =
      boundaryMap _ _ (endpointPullCochain degree character side 1 representative) := by
  apply Subtype.ext
  exact endpointPull_differentialOne degree character side representative

def endpointPullH2 (degree : ℕ) (character : RankOneCharacter) (side : Side) :
    StratumH2 degree character side →ₗ[ℂ] EdgeH2 degree character :=
  (LinearMap.range (boundaryMap rationalLevel
    (flagRepresentation (rationalCoefficientComponent degree character) side))).liftQ
      ((classOf rationalLevel
        (functionRepresentation (rationalCoefficientComponent degree character) Edges)).comp
        (endpointPullCocycle degree character side)) (by
      rintro representative ⟨incoming, rfl⟩
      change classOf rationalLevel
        (functionRepresentation (rationalCoefficientComponent degree character) Edges)
        (endpointPullCocycle degree character side (boundaryMap _ _ incoming)) = 0
      rw [endpointPull_boundaryMap]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩)

theorem endpointPullH2_realizes (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (representative : MaximalCycles degree character side) :
    endpointPullH2 degree character side (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) side) representative) =
      classOf rationalLevel
        (functionRepresentation (rationalCoefficientComponent degree character) Edges)
      (endpointPullCocycle degree character side representative) :=
  Submodule.liftQ_apply _ _ _

theorem endpointStabilizer_le (level : Subgroup RationalGL3) (side : Side)
    (edge : Edges) :
    MulAction.stabilizer level edge ≤
      MulAction.stabilizer level (endpoint side edge) := by
  intro element membership
  rw [MulAction.mem_stabilizer_iff] at membership ⊢
  change element.val • edge = edge at membership
  have equivariance := endpoint_smul side element.val edge
  rw [membership] at equivariance
  exact equivariance.symm

def edgeComparison (degree : ℕ) (character : RankOneCharacter) :
    BoundaryCoordinates degree character →ₗ[ℂ] EdgeH2 degree character :=
  ((endpointPullH2 degree character .plane).comp (LinearMap.fst ℂ _ _)) -
    ((endpointPullH2 degree character .line).comp (LinearMap.snd ℂ _ _))

theorem fullBoundary_edgeBoundary (degree : ℕ) (character : RankOneCharacter)
    (representative : fullBoundaryCycles degree character) :
    endpointPullCocycle degree character .plane representative.val.1.1 -
        endpointPullCocycle degree character .line representative.val.1.2 =
      boundaryMap rationalLevel
        (functionRepresentation (rationalCoefficientComponent degree character) Edges)
        representative.val.2 := by
  apply Subtype.ext
  apply Subtype.ext
  funext vertices edge
  have compatible := congrFun (congrFun representative.property vertices) edge
  exact sub_eq_zero.mp compatible

theorem fullBoundaryCoordinates_edgeComparison (degree : ℕ) (character : RankOneCharacter)
    (representative : fullBoundaryCycles degree character) :
    edgeComparison degree character
      (Helpers.canonicalCoordinates degree character (fullBoundaryClass degree character representative)) =
      0 := by
  rw [Helpers.canonicalCoordinates_realizes]
  change endpointPullH2 degree character .plane (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .plane)
      representative.val.1.1) -
    endpointPullH2 degree character .line (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .line)
      representative.val.1.2) = 0
  rw [endpointPullH2_realizes, endpointPullH2_realizes, ← map_sub, fullBoundary_edgeBoundary]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩

theorem coordinates_range_le_ker (degree : ℕ) (character : RankOneCharacter) :
    LinearMap.range (Helpers.canonicalCoordinates degree character) ≤
      LinearMap.ker (edgeComparison degree character) := by
  rintro coordinates ⟨boundaryClass, rfl⟩
  obtain ⟨representative, rfl⟩ :=
    (fullBoundaryRelations degree character).mkQ_surjective boundaryClass
  exact fullBoundaryCoordinates_edgeComparison degree character representative

theorem edgeComparison_zero_lifts (degree : ℕ) (character : RankOneCharacter)
    (coordinates : BoundaryCoordinates degree character)
    (compatible : edgeComparison degree character coordinates = 0) :
    ∃ boundaryClass, Helpers.canonicalCoordinates degree character boundaryClass = coordinates := by
  have planeSurjective := (LinearMap.range (boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .plane))).mkQ_surjective
      coordinates.1
  obtain ⟨planeRepresentative, planeEquality⟩ := planeSurjective
  have lineSurjective := (LinearMap.range (boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .line))).mkQ_surjective
      coordinates.2
  obtain ⟨lineRepresentative, lineEquality⟩ := lineSurjective
  have coordinatesEquality : coordinates =
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) .plane) planeRepresentative,
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) .line) lineRepresentative) :=
    Prod.ext planeEquality.symm lineEquality.symm
  rw [coordinatesEquality] at compatible
  change endpointPullH2 degree character .plane (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .plane)
      planeRepresentative) -
    endpointPullH2 degree character .line (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .line)
      lineRepresentative) = 0 at compatible
  rw [endpointPullH2_realizes, endpointPullH2_realizes, ← map_sub] at compatible
  have edgeExists := (Submodule.Quotient.mk_eq_zero _).mp compatible
  obtain ⟨edgeRepresentative, edgeEquality⟩ := edgeExists
  let totalRepresentative : fullBoundaryCycles degree character :=
    ⟨((planeRepresentative, lineRepresentative), edgeRepresentative), by
      funext vertices edge
      have equality := congrArg
        (fun representative => representative.val.val vertices edge) edgeEquality
      change edgeRepresentative.val ![vertices 1, vertices 2] edge -
          edgeRepresentative.val ![vertices 0, vertices 2] edge +
          edgeRepresentative.val ![vertices 0, vertices 1] edge =
        planeRepresentative.val.val vertices (endpoint .plane edge) -
          lineRepresentative.val.val vertices (endpoint .line edge) at equality
      exact sub_eq_zero.mpr equality.symm⟩
  refine ⟨fullBoundaryClass degree character totalRepresentative, ?_⟩
  rw [Helpers.canonicalCoordinates_realizes, coordinatesEquality]

theorem coordinates_range_eq_ker (degree : ℕ) (character : RankOneCharacter) :
    LinearMap.range (Helpers.canonicalCoordinates degree character) =
      LinearMap.ker (edgeComparison degree character) := by
  apply le_antisymm
  · exact coordinates_range_le_ker degree character
  · intro coordinates compatible
    exact edgeComparison_zero_lifts degree character coordinates compatible

theorem associatePair_lifts_iff {degree : ℕ} (data : InducingData degree) :
    associatePair data ≤ LinearMap.range (Helpers.canonicalCoordinates degree data.chi) ↔
      boundarySummand data .plane ≤ LinearMap.ker (endpointPullH2 degree data.chi .plane) ∧
        boundarySummand data .line ≤ LinearMap.ker (endpointPullH2 degree data.chi .line) := by
  rw [coordinates_range_eq_ker]
  constructor
  · intro lifts
    constructor
    · intro planeClass membership
      change endpointPullH2 degree data.chi .plane planeClass = 0
      have vanishes := lifts (show (planeClass, 0) ∈ associatePair data from
        ⟨membership, (boundarySummand data .line).zero_mem⟩)
      change endpointPullH2 degree data.chi .plane planeClass -
        endpointPullH2 degree data.chi .line 0 = 0 at vanishes
      simpa only [map_zero, sub_zero] using vanishes
    · intro lineClass membership
      change endpointPullH2 degree data.chi .line lineClass = 0
      have vanishes := lifts (show (0, lineClass) ∈ associatePair data from
        ⟨(boundarySummand data .plane).zero_mem, membership⟩)
      change endpointPullH2 degree data.chi .plane 0 -
        endpointPullH2 degree data.chi .line lineClass = 0 at vanishes
      simpa only [map_zero, zero_sub, neg_eq_zero] using vanishes
  · rintro ⟨planeVanishes, lineVanishes⟩ coordinates membership
    change endpointPullH2 degree data.chi .plane coordinates.1 -
      endpointPullH2 degree data.chi .line coordinates.2 = 0
    rw [planeVanishes membership.1, lineVanishes membership.2, sub_self]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BoundaryExactness
