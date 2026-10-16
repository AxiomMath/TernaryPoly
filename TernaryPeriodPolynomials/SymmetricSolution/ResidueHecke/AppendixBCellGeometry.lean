module

public import TernaryPeriodPolynomials.SymmetricSpace.CellGeometry.Radius
public import TernaryPeriodPolynomials.SymmetricSpace.CellGeometry.Schur
public import TernaryPeriodPolynomials.SymmetricSpace.CellGeometry.Voronoi
public import TernaryPeriodPolynomials.SymmetricSpace.CellGeometry.Equiv
public import TernaryPeriodPolynomials.SymmetricSpace.CellGeometry.Convex
public import TernaryPeriodPolynomials.SymmetricSpace.CellGeometry.Chart

@[expose] public section


/-!
# Appendix B (`lem:literal-residue-comparison`): the geometric cell calculation

Paper: proof of Lemma B.1, the paragraphs on `G(w,C)`, the covering radius, the Voronoi inequalities, the
Schur complement, well-roundedness, the `P_H`-equivariant embedding `ℝ² × W₂ → W₃`, contractibility and fibre integration.  Formalized by Claude Sonnet 5.5.
Everything in `Exports/AppendixBResidue.lean` (the map `Gmat`, `Gmat_wellRounded`, `image_eq_translates`, `Gmat_equivariant`, `torus_volume`, stabilizer orders) is unchanged; the files here add
the claims below as literal statements.

## Claim ↦ Lean

* **Covering radius `1/(2(1+|t|))`**: `deltaSq_Ct_le` (bound, existing) and, new, `deltaSq_vertex`, `coveringRadiusSq_isGreatest`, `coveringRadiusSq_Ct`: it is attained at the Voronoi vertex
  (`vertexPt`), so it is exactly the covering radius; `deltaSq_BinWR_le`: `δ_C(w)² ≤ 1/2` for every minimum-one well-rounded binary `C`.
* **Voronoi inequalities**: `voronoi_iff_nonneg`, `voronoi_iff_nonpos`: for `0 ≤ t ≤ 1/2` the Voronoi cell of `0` is exactly `|w₁+tw₂|, |tw₁+w₂| ≤ 1/2, |w₁-w₂| ≤ 1` (and with `|w₁+w₂| ≤ 1` for `t ≤ 0`).
* **Positivity of the Schur complement and positive definiteness**: `Gblock`, `schurComplement_Gblock` (`A - B C⁻¹ Bᴴ = 1 - δ²` literally), `schur_pos` (`≥ 1/2`),
  `posDef_fromBlocks_of_schur` (strict Schur criterion for Mathlib's `Matrix.PosDef`), `Gmat_matrixPosDef` (`Matrix.PosDef (G(w,C))` for every `BinWR C`).
* **Well-roundedness**: `Statements.AppendixBResidue.Gmat_wellRounded` (existing).
* **`P_H`-equivariant embedding**: `phAct` (the action `(w,C) ↦ (D⁻¹(u+ηw), DᵗCD)` of `g ∈ P_H`), `Gmat_phAct` (`gᵗG(w,C)g = G(g·(w,C))` for all `g ∈ P_H`), `phAct_one`, `phAct_mul` (action law),
  `phAct_radPH` (the integral radical acts by translation of `w`, trivially on `C`), `torusLinear_det`/`fiber_compat_torus`: the determinant of the linear part on the torus coordinate is `deltaG eU g`,
  the scalar of `fiber_compat`/`kappaLit`.
* **Image and parametrization**: `BinWR_eq_union_edges` (`W₂` is the union of the `GL₂(ℤ)`-translates of the standard edge), `Tparam`, `TparamHomeo` (the standard cell `≃ₜ` the Voronoi fibration over the edge),
  `chartMap_hasFDerivAt`, `chartJac_det_pos` (the Jacobian `(w₁,w₂,t) ↦ (Cw,t)` has determinant `1 - t² > 0`), `Gmat_eq_cellMat` (the residue coordinates are the same polynomial throughout the fibre).
* **Contractibility**: `Tcell_convex`, `Tcell_contractible`, `voronoi_convex`, `voronoi_contractible`.

## NOT built (recorded precisely)

* The cell structure of `W₂` as a tree and its contractibility (hence contractibility of `ℝ² × W₂` and of the image of `i`); the ternary retract `W₃` as a cell complex and its contractibility
  (Ash); only the standard cell is treated.
* The equivariant subdivision, the augmented cellular chain complexes as projective resolutions of `P_H`, the comparison theorem for resolutions identifying the cellular inclusion with
  the group-homology map, the cellular cross product and the fibre integration `[ℤ²\ℝ²] ⊗ (e ⊗ q) ↦ e ⊗ q` as a chain map (what is proved: the torus has covolume one, `torus_volume`, the orientation factor
  is `deltaG`, `torusLinear_det`, and the radical acts by translation).
* The identification of that fibre map with the Hochschild-Serre `κ` is the group-homological `kappaLit` (`Statements.AppendixBResidue`/`TernaryPeriodPolynomials.Argument.AppendixBResidue.LiteralKappa`); the comparison with `res_H` is `PHCompat`,
  proved for every `n` by `FaceMain.phCompat_of_tree` with `TreeMapsMain.treeData`.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.AppendixBCellGeometry

open TernaryPeriodPolynomials.Argument.AppendixBCellGeometry

export TernaryPeriodPolynomials.Argument.AppendixBCellGeometry
  (coveringRadiusSq vertexPt deltaSq_vertex coveringRadiusSq_isGreatest coveringRadiusSq_Ct coveringRadiusSq_le_half
    voronoi_iff_nonneg voronoi_iff_nonpos
    posDef_fromBlocks_of_schur Gblock Gmat_eq_submatrix posDefQ_iff_posDef BinWR_posDef deltaSq_BinWR_le schurComplement_Gblock
    schur_pos Gmat_matrixPosDef
    phAct phMat Gmat_phAct phAct_one phAct_mul phAct_radPH torusLinear torusLinear_det fiber_compat_torus
    Tcell_convex Tcell_contractible voronoi_convex voronoi_contractible BinWR_eq_union_edges Tfib Tparam
    chartMap chartJac chartJac_det chartJac_det_pos chartMap_hasFDerivAt cellMat Gmat_eq_cellMat TparamHomeo)

end TernaryPeriodPolynomials.Argument.Statements.AppendixBCellGeometry
