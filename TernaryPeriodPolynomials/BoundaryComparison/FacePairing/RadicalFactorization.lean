module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.BaseEdgeStabilizer
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LineCoordinates

@[expose] public section


/-!
# The good-line radical factors through the `baseEdge` stabilizer (M1a, bridging step)

`goodLineRadicalInclusion : RadicalLattice →* ↥Λ₁` lands, by `goodLineRadicalInclusion_fixes_baseEdge`
(`BaseEdgeStabilizer.lean`), inside the stabilizer of the *complete flag* `baseEdge`, which is a
subgroup of `Λ₁` (the stabilizer of its line-side endpoint alone). `radicalToSmaller` is the
resulting codomain restriction to that smaller stabilizer, and
`goodLineRadicalInclusion_eq_inclusion_comp_radicalToSmaller` factors `goodLineRadicalInclusion`
through it and the inclusion of the smaller stabilizer into `Λ₁`. The inclusion
`innerInclusion : fixedPointLevel rationalLevel (mk baseEdge) ≤ Λ₁` is `fixedPointLevel_edge_le_endpoint`
specialised at `baseEdge`'s line endpoint, which is `rationalGoodLine` by `baseEdge_line_eq_goodLine`.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GoodBuildingPaths.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.LineCoordinates

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- The stabilizer of the complete flag `baseEdge` sits inside `Λ₁`, the stabilizer of its
line-side endpoint alone. -/
theorem innerInclusion :
    fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges) ≤ Λ₁ := by
  have step := fixedPointLevel_edge_le_endpoint .line (QuotientGroup.mk baseEdge : Edges)
  rwa [baseEdge_line_eq_goodLine] at step

/-- The good-line radical, viewed as landing in the stabilizer of the complete flag `baseEdge`
rather than merely in `Λ₁`, the stabilizer of its line-side endpoint. -/
def radicalToSmaller :
    RadicalLattice →* ↥(fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges)) :=
  (Λ₁.subtype.comp goodLineRadicalInclusion).codRestrict _ (fun a =>
    Subgroup.mem_inf.mpr ⟨(goodLineRadicalInclusion a).property.1,
      MulAction.mem_stabilizer_iff.mpr (goodLineRadicalInclusion_fixes_baseEdge a)⟩)

/-- **Factorization.** The good-line radical inclusion factors through `radicalToSmaller` and the
inclusion of the smaller stabilizer into `Λ₁`. -/
theorem goodLineRadicalInclusion_eq_inclusion_comp_radicalToSmaller :
    goodLineRadicalInclusion = (Subgroup.inclusion innerInclusion).comp radicalToSmaller :=
  MonoidHom.ext fun _ => Subtype.ext rfl

end TernaryPeriodPolynomials.Argument.FacePairing
