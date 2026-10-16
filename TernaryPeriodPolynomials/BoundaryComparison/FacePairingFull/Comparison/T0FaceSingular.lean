module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.T0Face
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.SingularRestriction

@[expose] public section


/-!
# The face dictionary of the intertwiner `T₀`, in terms of the library's singular restriction

`T0_graph_geometric` (K2) describes the graph of the intertwiner `T` of Proposition `line_constant_term_comparison` as the set of pairs
(plane component, line component) of the geometric restrictions `geoRestriction` of global classes with inner coordinates.
`geoRestriction_eq_singular_restriction` (L5) identifies `geoRestriction` with the singular restriction
`H²(M; E) → H²(∂M; E)` of Submission.  `T0_graph_singular` combines the two: the graph of `T` is the set of pairs of face components of
the singular restriction to the boundary of the (singular) class of a global cocycle with inner coordinates.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.EquivariantSingularSmall
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

variable (n : ℕ) (χ : RankOneCharacter)

/-- The singular restriction to the boundary `∂M` of the class of a global cocycle (of the arithmetic level), as a class of the
cone model of `H²(∂M; E)`: the class of the cocycle in the singular cohomology of the bordification
(`groupLocalCohomologyIso`), restricted to the actual boundary (`geometricBoundaryRestriction`) and transported to the
model cone (`modelBoundaryQuasiIso`). -/
def singularFaceRestriction (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    (homCochains coneR (coeffRep (rationalCoefficientComponent n χ))).homology 2 :=
  (homologyMap (modelBoundaryQuasiIso (coeffRep (rationalCoefficientComponent n χ))) 2).hom
    ((homologyMap (SingularBoundaryRestriction.geometricBoundaryRestriction (coeffRep (rationalCoefficientComponent n χ))) 2).hom
      ((SingularLocalCoefficient.groupLocalCohomologyIso SingularBoundaryRestriction.wholeProjection SingularBoundaryRestriction.wholeQuotientCovering
        (coeffRep (rationalCoefficientComponent n χ)) 2).hom.hom
        ((fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl)
          (coeffRep (rationalCoefficientComponent n χ)) 2).hom
          (ptCls (rationalCoefficientComponent n χ)
            (cocyclesRes (rationalCoefficientComponent n χ) N6_le_rationalLevel c)))))

theorem singularFaceRestriction_eq (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    singularFaceRestriction n χ c =
      geoRestriction (rationalCoefficientComponent n χ)
        (cocyclesRes (rationalCoefficientComponent n χ) N6_le_rationalLevel c) :=
  (geoRestriction_eq_singular_restriction (rationalCoefficientComponent n χ) _).symm

/-- **The face dictionary of the intertwiner `T₀` for the library's singular restriction.**  The pairs (plane face
component, line face component) of the singular restrictions to `∂M` of global classes with inner coordinates are exactly the pairs
`(planeCls ξ, lineCls (T ξ))`, `ξ` inner, for any `T` with the graph property of `line_constant_term_comparison`. -/
theorem T0_graph_singular
    (T : StratumH2 n χ .plane → StratumH2 n χ .line)
    (h1 : ∀ ξ, InnerBoundary n χ .plane ξ → InnerBoundary n χ .line (T ξ) ∧
      ∃ c, globalCoordinates n χ c = (ξ, T ξ))
    (h2 : ∀ c, InnerBoundary n χ .plane (globalCoordinates n χ c).1 →
      InnerBoundary n χ .line (globalCoordinates n χ c).2 →
      (globalCoordinates n χ c).2 = T (globalCoordinates n χ c).1) :
    (∀ ξ, InnerBoundary n χ .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n χ),
        (homologyMap (homPullback conePlane (coeffRep (rationalCoefficientComponent n χ))) 2).hom
            (singularFaceRestriction n χ c) = planeCls n χ ξ ∧
        (homologyMap (homPullback coneLine (coeffRep (rationalCoefficientComponent n χ))) 2).hom
            (singularFaceRestriction n χ c) = lineCls n χ (T ξ)) ∧
    (∀ c : cocycles rationalLevel (rationalCoefficientComponent n χ),
      InnerBoundary n χ .plane (globalCoordinates n χ c).1 →
      InnerBoundary n χ .line (globalCoordinates n χ c).2 →
      ∃ ξ, InnerBoundary n χ .plane ξ ∧
        (homologyMap (homPullback conePlane (coeffRep (rationalCoefficientComponent n χ))) 2).hom
            (singularFaceRestriction n χ c) = planeCls n χ ξ ∧
        (homologyMap (homPullback coneLine (coeffRep (rationalCoefficientComponent n χ))) 2).hom
            (singularFaceRestriction n χ c) = lineCls n χ (T ξ)) := by
  simp only [singularFaceRestriction_eq]
  exact T0_graph_geometric n χ T h1 h2

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
