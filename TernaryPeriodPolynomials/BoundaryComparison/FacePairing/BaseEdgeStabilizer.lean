module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.EdgeRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerSplitting

@[expose] public section


/-!
# `baseEdge` is fixed by the good-line radical and by the Levi element at `T` (M1a, gap (c))

The remaining obstruction to evaluating `goodLineBinaryEdgeCycle_value`'s
explicit Hecke-free formula at the generator `T` is whether the two group elements appearing there
(`goodLineRadicalInclusion _` and `goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T)`)
fix the *complete flag* `baseEdge`, not merely its line-side endpoint (already known via
`arithmeticLevi_goodLine` / `lowerRadicalLattice_stabilizer` composed with
`baseEdge_line_eq_goodLine`).

Since `Edges = RationalGL3 ⧸ (parabolic .plane ⊓ parabolic .line)`, fixing the complete flag is
exactly fixing *both* endpoints (`fixes_edge_of_fixes_endpoints`). The line side is already
available from each element's own membership proof. The new content here is the plane side:
`baseEdge`'s plane endpoint is `QuotientGroup.mk swapLastTwo` (`baseEdge_plane`,
`GoodBuildingPaths/Helpers.lean`), and:

- every radical element fixes it unconditionally (`goodLineRadicalInclusion_fixes_swapLastTwo`):
  conjugating `lowerPlaneUnipotent` by `swapLastTwo` always lands in `InPlaneParabolic`;
- the Levi element at `T` fixes it too (`goodLineLeviSection_T_fixes_swapLastTwo`), because `T`'s
  matrix `!![1,1;0,1]` has vanishing `(1,0)` entry, which is exactly the condition under which
  conjugating `arithmeticLevi` by `swapLastTwo` lands in `InPlaneParabolic`.

Combining both resolves gap (c): `goodLineRadicalInclusion_fixes_baseEdge` and
`goodLineLeviSection_T_fixes_baseEdge`.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GoodBuildingPaths.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- An edge's endpoint, evaluated at the class of its own representative, is just the class of
that representative: `endpoint` is `Quotient.map' id`. -/
theorem endpoint_mk (s : Side) (x : RationalGL3) :
    endpoint s (QuotientGroup.mk x : Edges) = QuotientGroup.mk x := rfl

/-- If `g` fixes both endpoints of a complete flag `mk x`, it fixes the complete flag itself:
`Edges` is the quotient by exactly the intersection of the two endpoint parabolics. -/
theorem fixes_edge_of_fixes_endpoints {g x : RationalGL3}
    (hplane : g • endpoint .plane (QuotientGroup.mk x : Edges) =
      endpoint .plane (QuotientGroup.mk x : Edges))
    (hline : g • endpoint .line (QuotientGroup.mk x : Edges) =
      endpoint .line (QuotientGroup.mk x : Edges)) :
    g • (QuotientGroup.mk x : Edges) = QuotientGroup.mk x := by
  rw [endpoint_mk] at hplane hline
  have hplane' : (QuotientGroup.mk (g * x) : Flags .plane) = QuotientGroup.mk x := hplane
  have hline' : (QuotientGroup.mk (g * x) : Flags .line) = QuotientGroup.mk x := hline
  show (QuotientGroup.mk (g * x) : Edges) = QuotientGroup.mk x
  exact QuotientGroup.eq.mpr
    (Subgroup.mem_inf.mpr ⟨QuotientGroup.eq.mp hplane', QuotientGroup.eq.mp hline'⟩)

/-- Every good-line radical element fixes `baseEdge`'s plane endpoint `mk swapLastTwo`:
conjugating `lowerPlaneUnipotent` by `swapLastTwo` always lands in `InPlaneParabolic`, with no
constraint on the radical parameter. -/
theorem goodLineRadicalInclusion_fixes_swapLastTwo (a : RadicalLattice) :
    (goodLineRadicalInclusion a).val • (QuotientGroup.mk swapLastTwo : Flags .plane) =
      QuotientGroup.mk swapLastTwo := by
  show (QuotientGroup.mk ((goodLineRadicalInclusion a).val * swapLastTwo) : Flags .plane) =
    QuotientGroup.mk swapLastTwo
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  change (swapLastTwo⁻¹ * ((goodLineRadicalInclusion a).val * swapLastTwo)).val 2 0 = 0 ∧
    (swapLastTwo⁻¹ * ((goodLineRadicalInclusion a).val * swapLastTwo)).val 2 1 = 0
  constructor <;>
    simp [goodLineRadicalInclusion, lowerRadicalLattice, swapLastTwo,
      lowerPlaneUnipotent, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

/-- The Levi element at `ModularGroup.T` fixes `baseEdge`'s plane endpoint `mk swapLastTwo`:
`T`'s matrix `!![1,1;0,1]` has vanishing `(1,0)` entry, which is exactly the condition under which
conjugating `arithmeticLevi` by `swapLastTwo` lands in `InPlaneParabolic`. -/
theorem goodLineLeviSection_T_fixes_swapLastTwo :
    (goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T)).val •
      (QuotientGroup.mk swapLastTwo : Flags .plane) = QuotientGroup.mk swapLastTwo := by
  show (QuotientGroup.mk
      ((goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T)).val * swapLastTwo) :
      Flags .plane) = QuotientGroup.mk swapLastTwo
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  change (swapLastTwo⁻¹ *
      ((goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T)).val * swapLastTwo)).val 2 0
        = 0 ∧
    (swapLastTwo⁻¹ *
      ((goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T)).val * swapLastTwo)).val 2 1
        = 0
  have hT : (SpecialLinearGroup.toGL ModularGroup.T : GeneralLinearGroup (Fin 2) ℤ).val =
      !![1,1;0,1] := rfl
  constructor <;>
    simp [goodLineLeviSection, arithmeticLeviHom, arithmeticLevi, planeLevi, planeBlock,
      swapLastTwo, hT, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

/-- Every good-line radical element fixes `baseEdge` as a complete flag,
unconditionally. -/
theorem goodLineRadicalInclusion_fixes_baseEdge (a : RadicalLattice) :
    (goodLineRadicalInclusion a).val • (QuotientGroup.mk baseEdge : Edges) =
      QuotientGroup.mk baseEdge := by
  apply fixes_edge_of_fixes_endpoints
  · rw [baseEdge_plane]
    exact goodLineRadicalInclusion_fixes_swapLastTwo a
  · rw [baseEdge_line_eq_goodLine]
    exact MulAction.mem_stabilizer_iff.mp (goodLineRadicalInclusion a).property.2

/-- The Levi element at `ModularGroup.T` fixes `baseEdge` as a complete
flag. -/
theorem goodLineLeviSection_T_fixes_baseEdge :
    (goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T)).val •
      (QuotientGroup.mk baseEdge : Edges) = QuotientGroup.mk baseEdge := by
  apply fixes_edge_of_fixes_endpoints
  · rw [baseEdge_plane]
    exact goodLineLeviSection_T_fixes_swapLastTwo
  · rw [baseEdge_line_eq_goodLine]
    exact MulAction.mem_stabilizer_iff.mp
      (goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T)).property.2

end TernaryPeriodPolynomials.Argument.FacePairing
