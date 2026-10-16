module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TracePairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.StabilizerRestriction

@[expose] public section


/-!
# Every plane boundary summand class is `InnerBoundary`

For any cuspidal datum `D : InducingData n`, every class in `boundarySummand D .plane` is
`InnerBoundary` (vanishes as a coboundary at every complete flag, not just the good ones).
This is the key bridge needed to realize `automorphicPlaneSpan n` elements as `InnerBoundary`,
for use in `constant_terms`'s proof via the decomposition `ξ = ξ' + (ξ - ξ')` using
`good_plane_cuspidal_span`/`bad_plane_cuspidal_span`.

The underlying fact: `GraphPieces.EndpointReduction.boundarySummand_le_ker` combined with
`FlagExactness.plane_flagExact` (unconditional, mirroring `line_flagExact`) is already used in
the code at
`BoundaryDuality.TraceRepresentatives.planeEdgeExact_of_mem`, and packaged —
representative-existence included — as `TracePairing.flat_of_mem` + `TracePairing.exists_rep`.
The only remaining step is matching `PlaneEdgeExact`'s witness (phrased via `differentialOneRaw`)
to `InnerBoundary`'s own existential (phrased via `differentialOne ... |>.val`); these are
definitionally equal (`differentialOne`'s `.val` field unfolds to exactly the `differentialOneRaw`
formula), so no conversion lemma is needed.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open TernaryPeriodPolynomials.BoundaryDuality

/-- Every class in a plane boundary summand is `InnerBoundary`: it vanishes as a coboundary at
every complete flag, not merely the good ones. -/
theorem boundarySummand_plane_subset_innerBoundary {n : ℕ} (D : InducingData n)
    {ξ : StratumH2 n D.chi .plane} (hξ : ξ ∈ boundarySummand D .plane) :
    InnerBoundary n D.chi .plane ξ := by
  obtain ⟨z, hz⟩ := TracePairing.exists_rep ξ
  obtain ⟨s, hs⟩ := TracePairing.flat_of_mem hξ z hz
  exact ⟨z, hz, s, hs⟩

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers in
/-- Every element of `automorphicPlaneSpan n` is `InnerBoundary`. Extends
`boundarySummand_plane_subset_innerBoundary` from a single boundary summand to the whole span,
using that `InnerBoundary` is kernel-membership of the linear map `endpointH2`
(`innerBoundary_iff_endpointH2`), hence cut out by a submodule. -/
theorem automorphicPlaneSpan_subset_innerBoundary {n : ℕ}
    {ξ : StratumH2 n trivialCharacter .plane} (hξ : ξ ∈ automorphicPlaneSpan n) :
    InnerBoundary n trivialCharacter .plane ξ := by
  have hsub : {a : StratumH2 n trivialCharacter .plane | ∃ D : CohomologicalCuspData n,
      a ∈ boundarySummand D.inducingData .plane} ≤
      LinearMap.ker (endpointH2 n trivialCharacter .plane) := by
    rintro a ⟨D, ha⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [← innerBoundary_iff_endpointH2]
    exact boundarySummand_plane_subset_innerBoundary D.inducingData ha
  have hmem := Submodule.span_le.mpr hsub hξ
  rw [LinearMap.mem_ker] at hmem
  exact (innerBoundary_iff_endpointH2 ξ).mpr hmem

end TernaryPeriodPolynomials.Argument.CuspidalSpan
