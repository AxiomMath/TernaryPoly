module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.TraceEvaluation

@[expose] public section


/-!
# P09 D3: the whole-boundary trace comparison (level `Γ → Γ(6)` transfer, assembly `τ = c · ev_{[∂M]}`)

Formalized by Claude Sonnet 5.5.

**Setting.**  `rationalLevel` is the model level, `N6` the image of `Γ(6)` in `GL₃(ℚ)`.  A *closed edge
three-cochain* is a level-invariant homogeneous scalar three-cochain `f : (GL₃(ℚ)⁴) → (Edges → ℂ)` with
`δf = 0` (`closedEdgeCochains`).  It is *boundary exact at `Γ`* (`BoundaryExactAt Γ`) if it is the
`Γ`-invariant coboundary of an edge two-cochain plus the pullback of a closed plane three-cochain minus
the pullback of a closed line three-cochain.  `levelTrace` is the boundary trace `traceDataL2.trace`
restricted to `closedEdgeCochains rationalLevel`; it kills boundary-exact cochains
(`levelTrace_eq_zero_of_boundaryExactAt`).

**Results.**

* `exists_closed_levelTrace_ne_zero` (S2): `levelTrace ≠ 0`, i.e. the trace is nonzero on the boundary cup
  product of an anchor (degree `n = 6`).
* `boundaryExactAt_of_N6` (S3, transfer level → `Γ(6)`): boundary exactness at `N6` implies boundary
  exactness at the level (averaging over `rationalLevel / N6`).
* `coneR_H4` (S4): the model cone of the three resolutions `ℚ[GL₃(ℚ)^{•+1} × Z]` of the flag, line and plane
  label modules of `Γ(6)` has `H⁴(Hom(·, ℚ)) ≅ ℚ`; it is chain homotopy equivalent (`coneEquiv`) to
  the library's stabilizer cone, whose top cohomology is computed by Poincaré duality of `∂M`
  (`stabilizerTotal_H4_iso`).
* `traceComparison` (S5–S7): there are a finite rational chain `Ω` of pairs (four vertices, label of a
  complete flag), and constants `c ∈ ℂˣ`, `κ ∈ ℚˣ` such that
  - `levelTrace f = c · Σ_y Ω(y) f(y)` for every level-invariant closed three-cochain (`evalOmega`);
  - `Σ_y Ω(y) f(y) = 0` implies `f` is boundary exact at the level;
  - (tie to the fundamental class) for every `ℚ`-linear `r : ℂ → ℚ` and every `Γ(6)`-invariant closed `f`,
    the geometric evaluation `geoIso` of the class of the `r`-component of `f` (transported from the model
    cone to the library's stabilizer cone by the homotopy equivalence) equals `κ · r(Σ_y Ω(y) f(y))`.
    `geoIso` is `H⁴(∂M; ℚ) → H₀(∂M; ℚ) → ℚ`, the cap product with the fundamental class of the orientation
    `boundaryOrientation` (that of `boundaryFundamentalClass`, `boundaryOrientation_class`) followed by the
    augmentation.
* `boundaryTrace_unique`: every linear functional on the level-invariant closed three-cochains killing
  boundary-exact cochains is a multiple of the trace.

**Scope.**  The scalar `c` of `levelTrace = c · ev` is the unavoidable normalization constant of the
manifest convention C4; no value is asserted.  The tie to the fundamental
class is componentwise over `ℚ` (`ℂ` is a `ℚ`-vector space and the Poincaré duality of `∂M` is rational):
for rational data it is the equality `κ · ev = ⟨[f], [∂M]⟩`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.TraceComparison

open CategoryTheory
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

/-- **S2.** The boundary trace is nonzero on the level-invariant closed edge three-cochains. -/
theorem levelTrace_ne_zero : ∃ f : closedEdgeCochains rationalLevel, levelTrace f ≠ 0 :=
  exists_closed_levelTrace_ne_zero

/-- **S3.** Boundary exactness at `Γ(6)` implies boundary exactness at the level. -/
theorem boundaryExact_descends_to_level {f : (Fin 4 → RationalGL3) → Edges → ℂ}
    (hf : f ∈ closedEdgeCochains rationalLevel) (h : BoundaryExactAt N6 f) :
    BoundaryExactAt rationalLevel f :=
  boundaryExactAt_of_N6 hf h

/-- **S4.** The top cohomology of the model cone (three resolutions of the label modules of `Γ(6)`) with trivial
rational coefficients is one-dimensional. -/
theorem modelCone_top_cohomology :
    Nonempty ((TernaryPoly.EquivariantSingularSmall.homCochains coneR trivialW).homology 4 ≅
      ModuleCat.of ℚ ℚ) :=
  coneR_H4

/-- **The trace comparison** (`τ = c · ev_{[∂M]}`, up to the nonzero constants of the convention C4). -/
theorem trace_comparison :
    ∃ (Ω : MonoidAlgebra ℚ ((Fin 4 → RationalGL3) × TernaryPoly.SymmetricSpaceBoundaryMV.Flag))
      (c : ℂ) (κ : ℚ), c ≠ 0 ∧ κ ≠ 0 ∧
      (∀ f : closedEdgeCochains rationalLevel, levelTrace f = c * evalOmega Ω f.1) ∧
      (∀ f : closedEdgeCochains rationalLevel, evalOmega Ω f.1 = 0 →
        BoundaryExactAt rationalLevel f.1) ∧
      (∀ (r : ℂ →ₗ[ℚ] ℚ) (f : closedEdgeCochains N6), modelClass r f = κ * r (evalOmega Ω f.1)) :=
  traceComparison

/-- Every functional on the level-invariant closed three-cochains killing boundary-exact ones is a multiple
of the boundary trace. -/
theorem boundary_trace_unique (σ : closedEdgeCochains rationalLevel →ₗ[ℂ] ℂ)
    (hσ : ∀ f : closedEdgeCochains rationalLevel, BoundaryExactAt rationalLevel f.1 → σ f = 0) :
    ∃ a : ℂ, ∀ f : closedEdgeCochains rationalLevel, σ f = a * levelTrace f :=
  boundaryTrace_unique σ hσ

/-- The orientation of the geometric evaluation is that of the boundary fundamental class. -/
theorem geoEval_orientation_is_fundamental_class :
    TernaryPoly.SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass =
      TernaryPoly.HalfSpaceBoundaryOrientation.ordinaryFundamentalClass 2
        TernaryPoly.SymmetricSpaceBoundaryManifold.boundaryEuclidean
        TernaryPoly.SymmetricSpaceBoundaryOrientation.boundaryOrientation :=
  boundaryOrientation_class

end TernaryPeriodPolynomials.Argument.Statements.TraceComparison
