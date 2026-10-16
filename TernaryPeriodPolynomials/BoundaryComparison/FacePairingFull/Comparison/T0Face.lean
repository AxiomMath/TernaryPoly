module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Restriction
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.InnerLift
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.LevelSix
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# The boundary coordinates of a global class are its restrictions to the open faces of `∂M`

For the coefficient system `E = rationalCoefficientComponent n χ` and a cocycle `c` of the arithmetic level
(`rationalLevel`), the geometric restriction of the class of `c|_{Γ(6)}` to the boundary cone
(`geoRestriction`, the map `H²(Γ(6); E) → H²(∂M; E)` induced by the chain map `coneToPt`) has

* plane component the class `planeCls` of the model coordinate `r_P` of `c`
  (`geoRestriction_plane_globalCoordinates`),
* line component the class `lineCls` of the model coordinate `r_Q` of `c`
  (`geoRestriction_line_globalCoordinates`),

where `planeCls`, `lineCls` send a class of the stratum `StratumH2 n χ s` (the level cohomology of
`Fun(Flags s, E)`) to the cohomology of the Hom complex of the plane (resp. line) model resolution, i.e. to
the cohomology of the open faces of `∂M`, and are injective (`planeCls_injective`, `lineCls_injective`).
Consequently the graph of any map `T` with the graph property of the intertwiner
(`T0_graph_geometric`) is the set of pairs (plane component, line component) of the geometric restrictions
of those global classes whose two coordinates are inner.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.EquivariantSingularSmall
open TernaryPoly.OrdinaryIncidence (Line Plane)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

variable (n : ℕ) (χ : RankOneCharacter)

/-- The class in the cohomology of the open plane faces of a plane-stratum class. -/
def planeCls : StratumH2 n χ .plane →
    (homK (rationalCoefficientComponent n χ) (Z := Plane)).homology 2 :=
  fun a => modelClsH2 (rationalCoefficientComponent n χ) psiPlane psiPlane_smul
    (resH2 (flagRepresentation (rationalCoefficientComponent n χ) .plane) N6_le_rationalLevel a)

/-- The class in the cohomology of the open line faces of a line-stratum class. -/
def lineCls : StratumH2 n χ .line →
    (homK (rationalCoefficientComponent n χ) (Z := Line)).homology 2 :=
  fun a => modelClsH2 (rationalCoefficientComponent n χ) psiLine psiLine_smul
    (resH2 (flagRepresentation (rationalCoefficientComponent n χ) .line) N6_le_rationalLevel a)

theorem planeCls_injective : Function.Injective (planeCls n χ) :=
  (modelClsH2_injective _ psiPlane psiPlane_smul).comp
    (resH2_injective _ N6_le_rationalLevel N6_normalized)

theorem lineCls_injective : Function.Injective (lineCls n χ) :=
  (modelClsH2_injective _ psiLine psiLine_smul).comp
    (resH2_injective _ N6_le_rationalLevel N6_normalized)

/-- The plane component of the geometric restriction of a global class is the plane coordinate. -/
theorem geoRestriction_plane_globalCoordinates
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    (homologyMap (homPullback conePlane (coeffRep (rationalCoefficientComponent n χ))) 2).hom
        (geoRestriction (rationalCoefficientComponent n χ)
          (cocyclesRes (rationalCoefficientComponent n χ) N6_le_rationalLevel c)) =
      planeCls n χ (globalCoordinates n χ c).1 :=
  geoRestriction_plane (rationalCoefficientComponent n χ) _

/-- The line component of the geometric restriction of a global class is the line coordinate. -/
theorem geoRestriction_line_globalCoordinates
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    (homologyMap (homPullback coneLine (coeffRep (rationalCoefficientComponent n χ))) 2).hom
        (geoRestriction (rationalCoefficientComponent n χ)
          (cocyclesRes (rationalCoefficientComponent n χ) N6_le_rationalLevel c)) =
      lineCls n χ (globalCoordinates n χ c).2 :=
  geoRestriction_line (rationalCoefficientComponent n χ) _

/-- **Inner line classes lift to the cohomology of the boundary cone** with plane component zero and
line component the class itself. -/
theorem innerLine_lift (ξ : StratumH2 n χ .line) (hξ : InnerBoundary n χ .line ξ) :
    ∃ κ : (TernaryPoly.EquivariantSingularSmall.homCochains coneR
        (coeffRep (rationalCoefficientComponent n χ))).homology 2,
      (homologyMap (homPullback coneLine (coeffRep (rationalCoefficientComponent n χ))) 2).hom κ =
        lineCls n χ ξ ∧
      (homologyMap (homPullback conePlane (coeffRep (rationalCoefficientComponent n χ))) 2).hom κ = 0 := by
  obtain ⟨z, hz, u, hu⟩ := hξ
  let zN : cocycles N6 (flagRepresentation (rationalCoefficientComponent n χ) .line) :=
    cocyclesRes (flagRepresentation (rationalCoefficientComponent n χ) .line) N6_le_rationalLevel z
  let uN : cochains N6 (functionRepresentation (rationalCoefficientComponent n χ) Edges) 1 :=
    cochainsRes (functionRepresentation (rationalCoefficientComponent n χ) Edges)
      N6_le_rationalLevel 1 u
  have huN : ∀ x e, zN.val.1 x (endpoint .line e) =
      (differentialOne N6 (functionRepresentation (rationalCoefficientComponent n χ) Edges) uN).1 x e :=
    hu
  refine ⟨innerLineCone _ zN uN huN, innerLineCone_line _ zN uN huN ▸ ?_, innerLineCone_plane _ zN uN huN⟩
  rw [← hz]
  rfl

/-- **Inner plane classes lift to the cohomology of the boundary cone** with line component zero and
plane component the class itself. -/
theorem innerPlane_lift (ξ : StratumH2 n χ .plane) (hξ : InnerBoundary n χ .plane ξ) :
    ∃ κ : (TernaryPoly.EquivariantSingularSmall.homCochains coneR
        (coeffRep (rationalCoefficientComponent n χ))).homology 2,
      (homologyMap (homPullback conePlane (coeffRep (rationalCoefficientComponent n χ))) 2).hom κ =
        planeCls n χ ξ ∧
      (homologyMap (homPullback coneLine (coeffRep (rationalCoefficientComponent n χ))) 2).hom κ = 0 := by
  obtain ⟨z, hz, u, hu⟩ := hξ
  let zN : cocycles N6 (flagRepresentation (rationalCoefficientComponent n χ) .plane) :=
    cocyclesRes (flagRepresentation (rationalCoefficientComponent n χ) .plane) N6_le_rationalLevel z
  let uN : cochains N6 (functionRepresentation (rationalCoefficientComponent n χ) Edges) 1 :=
    cochainsRes (functionRepresentation (rationalCoefficientComponent n χ) Edges)
      N6_le_rationalLevel 1 u
  have huN : ∀ x e, zN.val.1 x (endpoint .plane e) =
      (differentialOne N6 (functionRepresentation (rationalCoefficientComponent n χ) Edges) uN).1 x e :=
    hu
  refine ⟨innerPlaneCone _ zN uN huN, innerPlaneCone_plane _ zN uN huN ▸ ?_, innerPlaneCone_line _ zN uN huN⟩
  rw [← hz]
  rfl

/-- **The face dictionary of the intertwiner.**  Let `T` have the graph property of the intertwiner of
Proposition `line_constant_term_comparison` (every inner plane class `ξ` is the plane coordinate of a global class whose line
coordinate is `T ξ`, and a global class with inner coordinates has line coordinate `T` of its plane
coordinate).  Then the pairs (plane face component, line face component) of the geometric restrictions
`H²(Γ(6); E) → H²(∂M; E)` of global classes with inner coordinates are exactly the pairs
`(planeCls ξ, lineCls (T ξ))`, `ξ` inner. -/
theorem T0_graph_geometric
    (T : StratumH2 n χ .plane → StratumH2 n χ .line)
    (h1 : ∀ ξ, InnerBoundary n χ .plane ξ → InnerBoundary n χ .line (T ξ) ∧
      ∃ c, globalCoordinates n χ c = (ξ, T ξ))
    (h2 : ∀ c, InnerBoundary n χ .plane (globalCoordinates n χ c).1 →
      InnerBoundary n χ .line (globalCoordinates n χ c).2 →
      (globalCoordinates n χ c).2 = T (globalCoordinates n χ c).1) :
    (∀ ξ, InnerBoundary n χ .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n χ),
        (homologyMap (homPullback conePlane (coeffRep (rationalCoefficientComponent n χ))) 2).hom
            (geoRestriction (rationalCoefficientComponent n χ)
              (cocyclesRes (rationalCoefficientComponent n χ) N6_le_rationalLevel c)) =
          planeCls n χ ξ ∧
        (homologyMap (homPullback coneLine (coeffRep (rationalCoefficientComponent n χ))) 2).hom
            (geoRestriction (rationalCoefficientComponent n χ)
              (cocyclesRes (rationalCoefficientComponent n χ) N6_le_rationalLevel c)) =
          lineCls n χ (T ξ)) ∧
    (∀ c : cocycles rationalLevel (rationalCoefficientComponent n χ),
      InnerBoundary n χ .plane (globalCoordinates n χ c).1 →
      InnerBoundary n χ .line (globalCoordinates n χ c).2 →
      ∃ ξ, InnerBoundary n χ .plane ξ ∧
        (homologyMap (homPullback conePlane (coeffRep (rationalCoefficientComponent n χ))) 2).hom
            (geoRestriction (rationalCoefficientComponent n χ)
              (cocyclesRes (rationalCoefficientComponent n χ) N6_le_rationalLevel c)) =
          planeCls n χ ξ ∧
        (homologyMap (homPullback coneLine (coeffRep (rationalCoefficientComponent n χ))) 2).hom
            (geoRestriction (rationalCoefficientComponent n χ)
              (cocyclesRes (rationalCoefficientComponent n χ) N6_le_rationalLevel c)) =
          lineCls n χ (T ξ)) := by
  refine ⟨fun ξ hξ => ?_, fun c hp hl => ?_⟩
  · obtain ⟨-, c, hc⟩ := h1 ξ hξ
    refine ⟨c, ?_, ?_⟩
    · rw [geoRestriction_plane_globalCoordinates, hc]
    · rw [geoRestriction_line_globalCoordinates, hc]
  · refine ⟨(globalCoordinates n χ c).1, hp, ?_, ?_⟩
    · exact geoRestriction_plane_globalCoordinates n χ c
    · rw [geoRestriction_line_globalCoordinates, h2 c hp hl]

/-- The line component of the geometric restriction of a global class with inner coordinates is
determined by its plane component. -/
theorem lineFace_eq_of_planeFace_eq
    (T : StratumH2 n χ .plane → StratumH2 n χ .line)
    (h2 : ∀ c, InnerBoundary n χ .plane (globalCoordinates n χ c).1 →
      InnerBoundary n χ .line (globalCoordinates n χ c).2 →
      (globalCoordinates n χ c).2 = T (globalCoordinates n χ c).1)
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n χ))
    (hp : InnerBoundary n χ .plane (globalCoordinates n χ c).1)
    (hl : InnerBoundary n χ .line (globalCoordinates n χ c).2)
    (hp' : InnerBoundary n χ .plane (globalCoordinates n χ c').1)
    (hl' : InnerBoundary n χ .line (globalCoordinates n χ c').2)
    (h : (homologyMap (homPullback conePlane (coeffRep (rationalCoefficientComponent n χ))) 2).hom
            (geoRestriction (rationalCoefficientComponent n χ)
              (cocyclesRes (rationalCoefficientComponent n χ) N6_le_rationalLevel c)) =
        (homologyMap (homPullback conePlane (coeffRep (rationalCoefficientComponent n χ))) 2).hom
            (geoRestriction (rationalCoefficientComponent n χ)
              (cocyclesRes (rationalCoefficientComponent n χ) N6_le_rationalLevel c'))) :
    (homologyMap (homPullback coneLine (coeffRep (rationalCoefficientComponent n χ))) 2).hom
            (geoRestriction (rationalCoefficientComponent n χ)
              (cocyclesRes (rationalCoefficientComponent n χ) N6_le_rationalLevel c)) =
        (homologyMap (homPullback coneLine (coeffRep (rationalCoefficientComponent n χ))) 2).hom
            (geoRestriction (rationalCoefficientComponent n χ)
              (cocyclesRes (rationalCoefficientComponent n χ) N6_le_rationalLevel c')) := by
  rw [geoRestriction_plane_globalCoordinates, geoRestriction_plane_globalCoordinates] at h
  have h3 := planeCls_injective n χ h
  rw [geoRestriction_line_globalCoordinates, geoRestriction_line_globalCoordinates,
    h2 c hp hl, h2 c' hp' hl', h3]

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
