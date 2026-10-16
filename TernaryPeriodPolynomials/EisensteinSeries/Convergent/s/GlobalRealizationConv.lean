module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.GlobalRealization
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Basic
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.ConstantTerm.RestrictionFinal
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.EndpointSourceStandard
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.EndpointEisensteinCocycle

@[expose] public section


/-!
# `constant_terms` without the continuation of the plane Eisenstein operators

Same proof as `CuspidalSpan.constant_terms` (`Revision/Proofs/CuspidalSpan/GlobalRealization.lean`),
but the explicit global cocycles come from the convergent versions in
`Revision/Proofs/ConvergentEisenstein`: for `4 ≤ n` the plane Eisenstein series converges absolutely
at the cohomological point, the global cocycle is built from that series, the standard line
cocycle from the absolutely convergent standard integral, and the restriction formula from
`ConvergentEisenstein.ConstantTerm.restrictionFormula`.  The hypothesis is
`PlaneEisensteinConvergent` (flat extensions, `PlaneFlatExtensions.plane_flat_extensions`), not
`PlaneEisensteinHolomorphic`; neither `plane_eisenstein_continuation` nor
`eisenstein_holomorphy` is used.

The hypothesis-free pieces (`realizableSubmodule`, additivity of `globalCoordinates`, ...) are those
of `GlobalRealization.lean`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Consumers

open TernaryPeriodPolynomials.Argument.CuspidalSpan
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

/-- Every element of `automorphicPlaneSpan n` is realizable by an explicit global cocycle whose
line coordinate is `InnerBoundary`, with the convergent Eisenstein cocycle. -/
theorem automorphicPlaneSpan_le_realizable_conv {n : ℕ} (large : 4 ≤ n) :
    automorphicPlaneSpan n ≤ realizableSubmodule n large := by
  apply Submodule.span_le.mpr
  rintro ξ ⟨Dm, hξ⟩
  rw [← SourceSpace.sourceClass_range Dm.inducingData .plane] at hξ
  obtain ⟨plane, hplane⟩ := hξ
  have hol : PlaneEisensteinConvergent Dm.inducingData :=
    planeEisensteinConvergent large Dm.inducingData
  refine ⟨EndpointEisensteinCocycle.globalCocycle Dm.inducingData hol large plane, ?_, ?_⟩
  · rw [← hplane]
    exact congrArg Prod.fst (ConstantTerm.restrictionFormula large Dm.inducingData hol plane)
  · rw [congrArg Prod.snd (ConstantTerm.restrictionFormula large Dm.inducingData hol plane)]
    exact sourceClass_line_subset_innerBoundary Dm.inducingData
      (EndpointSourceStandard.sourceStandard Dm.inducingData large hol plane)

/-- **Constant terms** (`ar:eq:constantterms`) from the absolutely convergent Eisenstein series:
the proof of `CuspidalSpan.constant_terms` with `automorphicPlaneSpan_le_realizable_conv`. -/
theorem constant_terms_conv (n : ℕ) (hn : 4 ≤ n) (ξ : StratumH2 n trivialCharacter .plane)
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
  obtain ⟨c1, hc1, hinner1⟩ := automorphicPlaneSpan_le_realizable_conv hn hξ'mem
  obtain ⟨c2, hc2, hinner2⟩ := automorphicPlaneSpan_le_realizable_conv hn hdiff_mem
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

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Consumers
