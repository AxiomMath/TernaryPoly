module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.LineInner
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.PlaneInner
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.EvenCase
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.BadPlane
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.Span
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.RestrictionFinal
public import TernaryPeriodPolynomials.EisensteinSeries.Holomorphy
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.SourceStandard
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.EisensteinCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.Helpers
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.StabilizerRestriction

@[expose] public section


/-!
# Realizing `automorphicPlaneSpan` as explicit global cocycles, and `constant_terms`

Bundles `globalCoordinates` as a genuine `LinearMap` by identifying it with the composite `canonicalCoordinates ∘ canonicalRestriction ∘ classOf`
(`GraphPieces.Helpers.canonicalCoordinates_restriction`, whose statement `RealizesRestriction`
unfolds to literally `globalCoordinates`'s own defining equation). This gives additivity/
homogeneity of `globalCoordinates` in its cocycle argument "for free".

Using this, every generator `SourceSpace.sourceClass D .plane plane` of a plane boundary summand
(for `D : InducingData n` with `PlaneEisensteinHolomorphic D` and `4 ≤ n`) is realized by an
explicit global cocycle (`EndpointEisensteinCocycle.globalCocycle D hol large plane`, via
`ConstantTerm.restrictionFormula`) whose line coordinate is `InnerBoundary`
(`LineInner.sourceClass_line_subset_innerBoundary`). Packaging "realizable" as a `Submodule` (using
`innerBoundary_iff_endpointH2` for closure on the line side, mirroring `PlaneInner.lean`'s own
plane-side closure argument) extends this from generators to the whole of `automorphicPlaneSpan n`.

`constant_terms` then follows by decomposing `ξ = ξ' + (ξ - ξ')` via `good_plane_cuspidal_span`, realizing each summand,
and summing the two witnessing cocycles.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
open TernaryPeriodPolynomials.GraphPieces.Helpers

/-- `globalCoordinates`, bundled as a `LinearMap` via the canonical
restriction/coordinates composite. -/
def globalCoordinatesLinear (n : ℕ) (χ : RankOneCharacter) :
    cocycles rationalLevel (rationalCoefficientComponent n χ) →ₗ[ℂ] BoundaryCoordinates n χ :=
  ((canonicalCoordinates n χ).comp (canonicalRestriction n χ)).comp
    (classOf rationalLevel (rationalCoefficientComponent n χ))

theorem globalCoordinatesLinear_eq (n : ℕ) (χ : RankOneCharacter)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    globalCoordinatesLinear n χ c = globalCoordinates n χ c :=
  canonicalCoordinates_restriction n χ c

theorem globalCoordinates_add (n : ℕ) (χ : RankOneCharacter)
    (c1 c2 : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    globalCoordinates n χ (c1 + c2) = globalCoordinates n χ c1 + globalCoordinates n χ c2 := by
  rw [← globalCoordinatesLinear_eq, ← globalCoordinatesLinear_eq, ← globalCoordinatesLinear_eq,
    map_add]

theorem globalCoordinates_zero (n : ℕ) (χ : RankOneCharacter) :
    globalCoordinates n χ 0 = 0 := by
  rw [← globalCoordinatesLinear_eq, map_zero]

theorem globalCoordinates_smul (n : ℕ) (χ : RankOneCharacter) (a : ℂ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    globalCoordinates n χ (a • c) = a • globalCoordinates n χ c := by
  rw [← globalCoordinatesLinear_eq, ← globalCoordinatesLinear_eq, map_smul]

/-- Realizability as an explicit global cocycle whose plane coordinate is a given class and
whose line coordinate is `InnerBoundary`, bundled as a submodule of the plane stratum. -/
def realizableSubmodule (n : ℕ) (_large : 4 ≤ n) :
    Submodule ℂ (StratumH2 n trivialCharacter .plane) where
  carrier := {ξ | ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
    (globalCoordinates n trivialCharacter c).1 = ξ ∧
    InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2}
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩
    · rw [globalCoordinates_zero]
      rfl
    · rw [globalCoordinates_zero]
      exact (innerBoundary_iff_endpointH2 0).mpr (map_zero _)
  add_mem' := by
    rintro ξ1 ξ2 ⟨c1, hc1, hinner1⟩ ⟨c2, hc2, hinner2⟩
    refine ⟨c1 + c2, ?_, ?_⟩
    · rw [globalCoordinates_add]
      show (globalCoordinates n trivialCharacter c1).1 + (globalCoordinates n trivialCharacter c2).1
          = ξ1 + ξ2
      rw [hc1, hc2]
    · rw [globalCoordinates_add]
      show InnerBoundary n trivialCharacter .line
        ((globalCoordinates n trivialCharacter c1).2 + (globalCoordinates n trivialCharacter c2).2)
      rw [innerBoundary_iff_endpointH2] at hinner1 hinner2 ⊢
      rw [map_add, hinner1, hinner2, add_zero]
  smul_mem' := by
    rintro a ξ ⟨c, hc, hinner⟩
    refine ⟨a • c, ?_, ?_⟩
    · rw [globalCoordinates_smul]
      show a • (globalCoordinates n trivialCharacter c).1 = a • ξ
      rw [hc]
    · rw [globalCoordinates_smul]
      show InnerBoundary n trivialCharacter .line (a • (globalCoordinates n trivialCharacter c).2)
      rw [innerBoundary_iff_endpointH2] at hinner ⊢
      rw [map_smul, hinner, smul_zero]

/-- Every element of `automorphicPlaneSpan n` is realizable: it is the plane coordinate of an
explicit global cocycle whose line coordinate is `InnerBoundary`. -/
theorem automorphicPlaneSpan_le_realizable {n : ℕ} (large : 4 ≤ n) :
    automorphicPlaneSpan n ≤ realizableSubmodule n large := by
  apply Submodule.span_le.mpr
  rintro ξ ⟨Dm, hξ⟩
  rw [← SourceSpace.sourceClass_range Dm.inducingData .plane] at hξ
  obtain ⟨plane, hplane⟩ := hξ
  have hol : PlaneEisensteinHolomorphic Dm.inducingData :=
    TernaryPeriodPolynomials.EisensteinHolomorphy.eisenstein_holomorphy
      n (by omega) Dm.inducingData rfl
  refine ⟨EndpointEisensteinCocycle.globalCocycle Dm.inducingData hol large plane, ?_, ?_⟩
  · rw [← hplane]
    exact congrArg Prod.fst (restrictionFormula large Dm.inducingData hol plane)
  · rw [congrArg Prod.snd (restrictionFormula large Dm.inducingData hol plane)]
    exact sourceClass_line_subset_innerBoundary Dm.inducingData
      (EndpointSourceStandard.sourceStandard Dm.inducingData large hol plane)

/-- **Constant terms** (new-route target). Every mixed-cuspidal plane class is the plane
restriction of a global class whose line restriction is again mixed cuspidal.

For **even** `n` the `bad_plane_cuspidal_span` dependency is avoided entirely by
using the unconditional `EvenCase.bad_plane_cuspidal_span_even` directly. -/
theorem constant_terms (n : ℕ) (hn : 4 ≤ n) (ξ : StratumH2 n trivialCharacter .plane)
    (hξ : InnerBoundary n trivialCharacter .plane ξ) :
    ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      (globalCoordinates n trivialCharacter c).1 = ξ ∧
      InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 := by
  have h0n : 0 < n := by omega
  obtain ⟨ξ', hξ'mem, hξ'good⟩ :=
    TernaryPeriodPolynomials.good_plane_cuspidal_span n h0n ξ hξ
  have hξ'inner : InnerBoundary n trivialCharacter .plane ξ' :=
    automorphicPlaneSpan_subset_innerBoundary hξ'mem
  have hdiff_inner : InnerBoundary n trivialCharacter .plane (ξ - ξ') := by
    rw [innerBoundary_iff_endpointH2] at hξ hξ'inner ⊢
    rw [map_sub, hξ, hξ'inner, sub_zero]
  have hdiff_mem : ξ - ξ' ∈ automorphicPlaneSpan n := by
    rcases Nat.even_or_odd n with heven | hodd
    · exact bad_plane_cuspidal_span_even n h0n heven (ξ - ξ') hξ'good
    · exact TernaryPeriodPolynomials.bad_plane_cuspidal_span n h0n (ξ - ξ')
        hξ'good hdiff_inner
  obtain ⟨c1, hc1, hinner1⟩ := automorphicPlaneSpan_le_realizable hn hξ'mem
  obtain ⟨c2, hc2, hinner2⟩ := automorphicPlaneSpan_le_realizable hn hdiff_mem
  refine ⟨c1 + c2, ?_, ?_⟩
  · rw [globalCoordinates_add]
    show (globalCoordinates n trivialCharacter c1).1 + (globalCoordinates n trivialCharacter c2).1
        = ξ
    rw [hc1, hc2]
    abel
  · rw [globalCoordinates_add]
    show InnerBoundary n trivialCharacter .line
      ((globalCoordinates n trivialCharacter c1).2 + (globalCoordinates n trivialCharacter c2).2)
    rw [innerBoundary_iff_endpointH2] at hinner1 hinner2 ⊢
    rw [map_add, hinner1, hinner2, add_zero]

end TernaryPeriodPolynomials.Argument.CuspidalSpan
