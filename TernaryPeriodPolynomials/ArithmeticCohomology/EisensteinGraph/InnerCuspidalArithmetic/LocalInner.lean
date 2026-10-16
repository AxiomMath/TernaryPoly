module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.AutomorphicSpan
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.OrbitCohomology

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def subgroupRestrictionCochain {smaller larger : Subgroup RationalGL3}
    (inclusion : smaller ≤ larger) (representation : Representation ℂ RationalGL3 V)
    (degree : ℕ) :
    cochains larger representation degree →ₗ[ℂ] cochains smaller representation degree where
  toFun cochain := ⟨cochain.val, by
    intro element vertices
    exact cochain.property ⟨element.val, inclusion element.property⟩ vertices⟩
  map_add' first second := rfl
  map_smul' scalar cochain := rfl

def subgroupRestrictionCycle {smaller larger : Subgroup RationalGL3}
    (inclusion : smaller ≤ larger) (representation : Representation ℂ RationalGL3 V) :
    cocycles larger representation →ₗ[ℂ] cocycles smaller representation where
  toFun cycle := ⟨subgroupRestrictionCochain inclusion representation 2 cycle.val,
    cycle.property⟩
  map_add' _first _second := rfl
  map_smul' _scalar _cycle := rfl

def subgroupRestrictionH2 {smaller larger : Subgroup RationalGL3}
    (inclusion : smaller ≤ larger) (representation : Representation ℂ RationalGL3 V) :
    H2 larger representation →ₗ[ℂ] H2 smaller representation :=
  (LinearMap.range (boundaryMap larger representation)).mapQ
    (LinearMap.range (boundaryMap smaller representation))
    (subgroupRestrictionCycle inclusion representation) (by
      rintro cycle ⟨primitive, rfl⟩
      exact ⟨subgroupRestrictionCochain inclusion representation 1 primitive, rfl⟩)

theorem fixedPointLevel_edge_le_endpoint (side : Side) (edge : Edges) :
    fixedPointLevel rationalLevel edge ≤
      fixedPointLevel rationalLevel (endpoint side edge) := by
  intro element membership
  refine ⟨membership.1, ?_⟩
  apply MulAction.mem_stabilizer_iff.mpr
  rw [← endpoint_smul, MulAction.mem_stabilizer_iff.mp membership.2]

def endpointStabilizerRestriction (degree : ℕ) (character : RankOneCharacter)
    (side : Side) (edge : Edges) :
    H2 (fixedPointLevel rationalLevel (endpoint side edge))
        (rationalCoefficientComponent degree character) →ₗ[ℂ]
      H2 (fixedPointLevel rationalLevel edge)
        (rationalCoefficientComponent degree character) :=
  subgroupRestrictionH2 (fixedPointLevel_edge_le_endpoint side edge)
    (rationalCoefficientComponent degree character)

theorem endpointStabilizerRestriction_fixedPointH2 (degree : ℕ)
    (character : RankOneCharacter) (side : Side) (edge : Edges)
    (coordinate : StratumH2 degree character side) :
    endpointStabilizerRestriction degree character side edge
        (fixedPointH2 rationalLevel (rationalCoefficientComponent degree character)
          (endpoint side edge) coordinate) =
      fixedPointH2 rationalLevel (rationalCoefficientComponent degree character) edge
        (endpointH2 degree character side coordinate) := by
  refine Quotient.inductionOn' coordinate ?_
  intro cycle
  rfl

theorem innerBoundary_iff_endpointStabilizerRestrictions {degree : ℕ}
    {character : RankOneCharacter} {side : Side}
    (coordinate : StratumH2 degree character side) :
    InnerBoundary degree character side coordinate ↔
      ∀ edge : Edges,
        endpointStabilizerRestriction degree character side edge
          (fixedPointH2 rationalLevel (rationalCoefficientComponent degree character)
            (endpoint side edge) coordinate) = 0 := by
  rw [innerBoundary_iff_endpointH2]
  constructor
  · intro vanishing edge
    rw [endpointStabilizerRestriction_fixedPointH2, vanishing, map_zero]
  · intro vanishing
    apply (eq_zero_iff_fixedPointH2 rationalLevel
      (rationalCoefficientComponent degree character) _).mpr
    intro edge
    rw [← endpointStabilizerRestriction_fixedPointH2]
    exact vanishing edge

theorem fixedPointLevel_edge_le_flag (side : Side) (edge : Edges)
    (flag : Flags side) (endpoint_eq : endpoint side edge = flag) :
    fixedPointLevel rationalLevel edge ≤ fixedPointLevel rationalLevel flag := by
  rw [← endpoint_eq]
  exact fixedPointLevel_edge_le_endpoint side edge

def locallyInnerClasses (degree : ℕ) (character : RankOneCharacter)
    (side : Side) (flag : Flags side) :
    Submodule ℂ (H2 (fixedPointLevel rationalLevel flag)
      (rationalCoefficientComponent degree character)) :=
  ⨅ edge : {edge : Edges // endpoint side edge = flag},
    LinearMap.ker
      (subgroupRestrictionH2
        (fixedPointLevel_edge_le_flag side edge.val flag edge.property)
        (rationalCoefficientComponent degree character))

theorem innerBoundary_fixedPointH2_locallyInner {degree : ℕ}
    {character : RankOneCharacter} {side : Side}
    {coordinate : StratumH2 degree character side}
    (inner : InnerBoundary degree character side coordinate) (flag : Flags side) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent degree character)
      flag coordinate ∈ locallyInnerClasses degree character side flag := by
  apply (Submodule.mem_iInf
    (M := H2 (fixedPointLevel rationalLevel flag)
      (rationalCoefficientComponent degree character)) _).mpr
  intro edge
  have restriction :=
    (innerBoundary_iff_endpointStabilizerRestrictions coordinate).mp inner edge.val
  cases edge with
  | mk edge endpoint_eq =>
    cases endpoint_eq
    exact restriction

theorem innerBoundary_iff_locallyInner {degree : ℕ}
    {character : RankOneCharacter} {side : Side}
    (coordinate : StratumH2 degree character side) :
    InnerBoundary degree character side coordinate ↔
      ∀ flag : Flags side,
        fixedPointH2 rationalLevel (rationalCoefficientComponent degree character)
          flag coordinate ∈ locallyInnerClasses degree character side flag := by
  constructor
  · exact fun inner => innerBoundary_fixedPointH2_locallyInner inner
  · intro localInner
    apply (innerBoundary_iff_endpointStabilizerRestrictions coordinate).mpr
    intro edge
    have membership := localInner (endpoint side edge)
    have restriction := (Submodule.mem_iInf
      (M := H2 (fixedPointLevel rationalLevel (endpoint side edge))
        (rationalCoefficientComponent degree character)) _).mp membership
      ⟨edge, rfl⟩
    exact restriction

theorem mem_innerBadLineClasses_iff_local (degree : ℕ)
    (coordinate : StratumH2 degree trivialCharacter .line) :
    coordinate ∈ innerBadLineClasses degree ↔
      (∀ flag : Flags .line, GoodFlag .line flag →
        fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
          flag coordinate = 0) ∧
      (∀ flag : Flags .line,
        fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
          flag coordinate ∈ locallyInnerClasses degree trivialCharacter .line flag) := by
  rw [mem_innerBadLineClasses_iff, vanishesOnGood_iff_fixedPointH2,
    innerBoundary_iff_locallyInner]

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
