module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

theorem classOf_eq_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (level : Subgroup G) (representation : Representation ℂ G V)
    (first second : cocycles level representation) :
    classOf level representation first = classOf level representation second ↔
      ∃ primitive : cochains level representation 1,
        boundaryMap level representation primitive = first - second := by
  exact Submodule.Quotient.eq (LinearMap.range (boundaryMap level representation))

theorem vanishesOnGood_iff_representative {degree : ℕ} {character : RankOneCharacter}
    {side : Side} (representative : MaximalCycles degree character side) :
    VanishesOnGood degree character side
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent degree character) side)
          representative) ↔
      ∃ primitive : MaximalCochains degree character side 1,
        ∀ vertices flag, GoodFlag side flag →
          representative.val.val vertices flag =
            (differentialOne rationalLevel
              (flagRepresentation (rationalCoefficientComponent degree character) side)
              primitive).val vertices flag := by
  constructor
  · rintro ⟨other, sameClass, primitive, vanishing⟩
    obtain ⟨correction, correction_eq⟩ :=
      (classOf_eq_iff rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        representative other).mp sameClass.symm
    refine ⟨primitive + correction, ?_⟩
    intro vertices flag goodFlag
    have pointwise := congrArg (fun cycle : MaximalCycles degree character side =>
      cycle.val.val vertices flag) correction_eq
    change (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) side)
      correction).val vertices flag =
        representative.val.val vertices flag - other.val.val vertices flag at pointwise
    rw [map_add]
    change representative.val.val vertices flag = _ + _
    rw [pointwise, vanishing vertices flag goodFlag]
    abel
  · rintro ⟨primitive, vanishing⟩
    exact ⟨representative, rfl, primitive, vanishing⟩

def endpointCochain (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (cochainDegree : ℕ) :
    MaximalCochains degree character side cochainDegree →ₗ[ℂ]
      EdgeCochains degree character cochainDegree where
  toFun primitive := ⟨fun vertices edge => primitive.val vertices (endpoint side edge), by
    intro element vertices
    funext edge
    have equivariance := congrFun (primitive.property element vertices) (endpoint side edge)
    change primitive.val (fun index => element.val * vertices index) (endpoint side edge) = _
    rw [equivariance]
    change rationalCoefficientComponent degree character element.val
        (primitive.val vertices (element.val⁻¹ • endpoint side edge)) =
      rationalCoefficientComponent degree character element.val
        (primitive.val vertices (endpoint side (element.val⁻¹ • edge)))
    rw [endpoint_smul]⟩
  map_add' first second := rfl
  map_smul' scalar primitive := rfl

theorem endpointCochain_differentialOne (degree : ℕ) (character : RankOneCharacter)
    (side : Side) (primitive : MaximalCochains degree character side 1) :
    endpointCochain degree character side 2
        (differentialOne rationalLevel
          (flagRepresentation (rationalCoefficientComponent degree character) side) primitive) =
      differentialOne rationalLevel
        (functionRepresentation (rationalCoefficientComponent degree character) Edges)
        (endpointCochain degree character side 1 primitive) := rfl

theorem innerBoundary_iff_representative {degree : ℕ} {character : RankOneCharacter}
    {side : Side} (representative : MaximalCycles degree character side) :
    InnerBoundary degree character side
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent degree character) side)
          representative) ↔
      ∃ primitive : EdgeCochains degree character 1,
        ∀ vertices edge,
          representative.val.val vertices (endpoint side edge) =
            (differentialOne rationalLevel
              (functionRepresentation (rationalCoefficientComponent degree character) Edges)
              primitive).val vertices edge := by
  constructor
  · rintro ⟨other, sameClass, primitive, inner⟩
    obtain ⟨correction, correction_eq⟩ :=
      (classOf_eq_iff rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        representative other).mp sameClass.symm
    refine ⟨primitive + endpointCochain degree character side 1 correction, ?_⟩
    intro vertices edge
    have pointwise := congrArg (fun cycle : MaximalCycles degree character side =>
      cycle.val.val vertices (endpoint side edge)) correction_eq
    change (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) side)
      correction).val vertices (endpoint side edge) =
        representative.val.val vertices (endpoint side edge) -
          other.val.val vertices (endpoint side edge) at pointwise
    rw [map_add]
    change representative.val.val vertices (endpoint side edge) =
      (differentialOne rationalLevel
        (functionRepresentation (rationalCoefficientComponent degree character) Edges)
        primitive).val vertices edge +
      (differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        correction).val vertices (endpoint side edge)
    rw [pointwise, inner vertices edge]
    abel
  · rintro ⟨primitive, inner⟩
    exact ⟨representative, rfl, primitive, inner⟩

theorem supported_inner_representative {degree : ℕ} {character : RankOneCharacter}
    {side : Side} {coordinate : StratumH2 degree character side}
    (good : VanishesOnGood degree character side coordinate)
    (inner : InnerBoundary degree character side coordinate) :
    ∃ representative : MaximalCycles degree character side,
      classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent degree character) side)
          representative = coordinate ∧
      (∀ vertices flag, GoodFlag side flag → representative.val.val vertices flag = 0) ∧
      ∃ primitive : EdgeCochains degree character 1,
        ∀ vertices edge,
          representative.val.val vertices (endpoint side edge) =
            (differentialOne rationalLevel
              (functionRepresentation (rationalCoefficientComponent degree character) Edges)
              primitive).val vertices edge := by
  obtain ⟨original, originalClass, primitive, vanishing⟩ := good
  let representative := original - boundaryMap rationalLevel
    (flagRepresentation (rationalCoefficientComponent degree character) side) primitive
  have representativeClass : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) side)
      representative = coordinate := by
    rw [← originalClass]
    apply (classOf_eq_iff rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) side)
      representative original).mpr
    refine ⟨-primitive, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext vertices flag
    change (-primitive.val ![vertices 1, vertices 2] flag -
        -primitive.val ![vertices 0, vertices 2] flag +
        -primitive.val ![vertices 0, vertices 1] flag) =
      (original.val.val vertices flag -
        (primitive.val ![vertices 1, vertices 2] flag -
          primitive.val ![vertices 0, vertices 2] flag +
          primitive.val ![vertices 0, vertices 1] flag)) -
      original.val.val vertices flag
    abel
  refine ⟨representative, representativeClass, ?_, ?_⟩
  · intro vertices flag goodFlag
    change original.val.val vertices flag -
      (differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        primitive).val vertices flag = 0
    rw [vanishing vertices flag goodFlag, sub_self]
  · apply (innerBoundary_iff_representative representative).mp
    rw [representativeClass]
    exact inner

theorem boundarySummand_le_automorphicLineSpan {degree : ℕ}
    (datum : CohomologicalCuspData degree) :
    boundarySummand datum.inducingData .line ≤ automorphicLineSpan degree := by
  intro coordinate membership
  exact Submodule.subset_span ⟨datum, membership⟩

theorem zero_mem_automorphicLineSpan (degree : ℕ) :
    (0 : StratumH2 degree trivialCharacter .line) ∈ automorphicLineSpan degree :=
  (automorphicLineSpan degree).zero_mem

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
