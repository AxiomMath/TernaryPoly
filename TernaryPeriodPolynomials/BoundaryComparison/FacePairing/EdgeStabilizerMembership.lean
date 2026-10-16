module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.RadicalFactorization

@[expose] public section


/-!
# `baseEdge`-stabilizer membership for the good-line radical and the Levi element at `T` (M1a)

Thin membership wrappers around `BaseEdgeStabilizer.lean`'s "fixes `baseEdge`" facts, in the
exact shape (`.val ∈ fixedPointLevel rationalLevel (mk baseEdge)`) needed to invoke
`relOn`/`relCocycleOn_vanish` from `ParabolicDualityIdentCore.lean` with
`Σ := fixedPointLevel rationalLevel (mk baseEdge)` as the smaller subgroup, mirroring the
plane-side `CuspidalSpan.EdgeStabilizerMembership`'s role for
`identityPlaneRadicalInclusion_mem_edgeStabilizer` / `identityPlaneLeviSection_T_mem_edgeStabilizer`.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GoodBuildingPaths.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.LineCoordinates

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- Every good-line radical element lies in the stabilizer of `baseEdge`, viewed inside the
ambient group `RationalGL3` (the shape `relOn`/`relCocycleOn_vanish` need). -/
theorem goodLineRadicalInclusion_mem_edgeStabilizer (a : RadicalLattice) :
    (goodLineRadicalInclusion a).val ∈
      fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges) :=
  Subgroup.mem_inf.mpr ⟨(goodLineRadicalInclusion a).property.1,
    MulAction.mem_stabilizer_iff.mpr (goodLineRadicalInclusion_fixes_baseEdge a)⟩

/-- The Levi element at `ModularGroup.T` lies in the stabilizer of `baseEdge`, viewed inside the
ambient group `RationalGL3`. -/
theorem goodLineLeviSection_T_mem_edgeStabilizer :
    (goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T)).val ∈
      fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges) :=
  Subgroup.mem_inf.mpr ⟨(goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T)).property.1,
    MulAction.mem_stabilizer_iff.mpr goodLineLeviSection_T_fixes_baseEdge⟩

end TernaryPeriodPolynomials.Argument.FacePairing
