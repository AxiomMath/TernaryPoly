module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullOrdinaryComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.OrdinaryBoundaryConeActual
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.ConeMVZero
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.ConeMVFaces
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeTotal
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullCanonicalCone
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.BoundaryCohomology
public import TernaryPeriodPolynomials.BoundaryComparison.FaceRestriction.Statements

@[expose] public section


/-!
# The mapping-cone model of the boundary against the topological Mayer-Vietoris sequence

Formalized by Claude Sonnet 5.5.

For `M = Ind_K^G E_{n,t}` and `∂ = ∂X̄_G`, two collar neighbourhoods of the unions of closed maximal faces of the
neat cover, with Borel strata as intersection and no triple intersection (a flag has only a line and a plane),
give by induction and Shapiro the Mayer-Vietoris sequence
`H⁰(P,M) ⊕ H⁰(Q,M) → H⁰(B₀,M) → H¹(∂,M) → H¹(P,M) ⊕ H¹(Q,M) → H¹(B₀,M)` (`eq:MV-boundary`), and the
mapping cone `𝒞^r = C^r(P,M) ⊕ C^r(Q,M) ⊕ C^{r-1}(B₀,M)` keeps the corner signs explicit.

**What the library has and what is exported.**  The library proves the comparison in three layers, all of which
are stated below with the library theorem proving them.

1. *The topological sequence* (`topological_mv_short_exact`): the short exact sequence of equivariant singular
   chain complexes of the boundary of the principal level-six cover given by the two open neighbourhoods
   (line faces `U`, plane faces `V`, `U ∩ V` the flag corners).
2. *The cone is the topological sequence* (`cone_to_boundary_quasiIso`, `full_cone_to_boundary_quasiIso`,
   `cone_face_coordinates_are_inclusions`): the homotopy cofibre of the signed incidence
   `flag → line ⊕ plane` of the singular face resolutions maps to the singular chains of the boundary by the
   actual geometric inclusions, a quasi-isomorphism; its face coordinates are the inclusions of the line and plane
   face neighbourhoods into the boundary, so on cochains with values in any local system `W` the face components
   of a cone cocycle are the restrictions of a cocycle of the boundary to the faces.  Over the full integral group
   `GL₃(ℤ)` the same is true for the model cone built from the induced bar complexes of `P`, `Q` and
   `B₀ = P ∩ Q` (`canonicalBoundaryEquiv`), whose `Hom(-, W)` is literally `C^r(P,W) ⊕ C^r(Q,W) ⊕ C^{r-1}(B₀,W)`
   with the differential of the paper (`cone_differential_zero`, `cone_differential_one`).
3. *Cohomology* (`boundary_H1_is_cone_H1`, `model_cone_computes_boundary_cohomology`): for every rational
   representation `W` the first cohomology of the boundary is the first cohomology of the mapping cone of
   `C^•(P,W) ⊕ C^•(Q,W) → C^•(B₀,W)` (degree one, full group), and for the principal level-six group the
   cohomology of the model cone is that of the boundary in every degree.

Consequently the five-term sequence `eq:MV-boundary` holds for `H¹(∂,W)` itself, with the maps below
(`topological_mv_exact`): the cone-model maps conjugated by the comparison isomorphism.

**Restriction (link L5).**  The identification of the face components `toFaces` with the cochain restriction
`H¹(∂,W) → H¹(U,W) ⊕ H¹(V,W)` is the chain-level statement `cone_face_coordinates_are_inclusions` (the face coordinates of the
comparison map are the inclusions).  The comparison of the singular restriction `H^*(M) → H^*(∂M)` of the bordification with the cone
restriction of a global class is proved:
`Statements.FaceRestriction.geoRestriction_is_singular_restriction` (`Comparison/SingularRestriction.singular_restriction_eq_geoRestriction`),
re-exported here as `model_restriction_is_singular_restriction`.
-/

open TernaryPoly

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.BoundaryMayerVietoris

open CategoryTheory

/-- **The topological Mayer-Vietoris sequence of the boundary.** For the boundary of the principal
level-six cover, covered by the open neighbourhoods `U` of the line faces and `V` of the plane faces, the sequence of
equivariant singular chain complexes `0 → C(U ∩ V) → C(U) ⊕ C(V) → C(∂) → 0` is short exact (the intersection is the
flag neighbourhood, a Borel stratum; there is no triple intersection). -/
alias topological_mv_short_exact := SymmetricSpaceBoundaryIncidenceHomology.mvShortExact

/-- **The mapping cone is the topological Mayer-Vietoris sequence, principal level six.** The
homotopy cofibre of the signed incidence `flag ⟶ line ⊞ plane` of the singular face resolutions maps to the singular
chains of the boundary by the geometric inclusions, and this is a quasi-isomorphism. -/
alias cone_to_boundary_quasiIso := SymmetricSpaceBoundaryGeometricCone.faceConeToBoundary_quasiIso

/-- The same over the full integral group `GL₃(ℤ)`: the full face cone maps to the full boundary chains by the
actual geometric inclusions, and this is a quasi-isomorphism. -/
alias full_cone_to_boundary_quasiIso := SymmetricSpaceBoundaryFull.fullFaceConeToBoundary_quasiIso

/-- **The face coordinates of the comparison are the geometric inclusions.** The restriction of the
comparison `cone ⟶ ∂` to the face part `line ⊞ plane` is the map `facesToOpen` (the neighbourhood inclusions) followed
by the Mayer-Vietoris projection to the chains of the boundary: the face components of a cone cochain with values in
a local system are the restrictions to the line and plane neighbourhoods. -/
alias cone_face_coordinates_are_inclusions := SymmetricSpaceBoundaryGeometricCone.faceConeToBoundary_inr

/-- The same over the full integral group: the face part of the full cone maps to the boundary by the two
inclusions of the line-face and plane-face sums. -/
alias full_cone_face_coordinates_are_inclusions := SymmetricSpaceBoundaryFull.fullFaceConeToBoundary_inr

open SymmetricSpaceBoundaryFull OrdinaryParabolicGroups OrdinaryBoundaryCone

/-- **The model cone of the induced bar complexes of `P`, `Q`, `B₀` is the boundary.** The boundary
chains of the full level are homotopy equivalent, equivariantly for `GL₃(ℤ)`, to the cone of the signed incidence
`Ind B₀ ⟶ Ind Q ⊞ Ind P` of the induced bar complexes (Shapiro at the chain level). -/
def boundary_cone_equivalence :
    _root_.HomotopyEquiv fullBoundaryChains canonicalFaceCone :=
  canonicalBoundaryEquiv

/-- **Degree-zero differential of the mapping cone.** On the model cone, the coordinates
`(C^0(P,W) ⊕ C^0(Q,W))` of a degree-zero cochain are sent by the differential of the cone to
`(d a, d b, a - b)`: this is `d(a,b,c)` of the paper in degree zero. -/
alias cone_differential_zero := ordinaryCoordinates_d0

/-- **Degree-one differential of the mapping cone.** The cone differential is
`d(a,b,c) = (da, db, Res a - Res b - dc)`, in the coordinates `C^1(P,W) ⊕ C^1(Q,W) ⊕ C^0(B₀,W)`. -/
alias cone_differential_one := ordinaryCoordinates_d1

/-- **The three-term complex.** The part `𝒞^0 → 𝒞^1 → 𝒞^2` of the cochains of the model cone is isomorphic, as a
complex of rational vector spaces, to the explicit mapping-cone complex of the paper (`C^r(P,W) ⊕ C^r(Q,W) ⊕
C^{r-1}(B₀,W)`), for every rational representation `W` of `GL₃(ℤ)`. -/
alias cone_three_term_complex := ordinaryShortComplexIso

/-- **`H¹(∂, W)` is the first cohomology of the mapping cone.** For every rational representation `W`
of the full integral group, the first cohomology of the singular cochains of the boundary of the principal level-six
cover with values in `W` (equivariant cochains, i.e. the cohomology of the boundary of the arithmetic quotient with
coefficients in `W`) is the first cohomology of the cone `𝒞^•(P,Q,W)`: cocycles `(A_P, A_Q, u)` with
`du = Res A_P - Res A_Q`, modulo the cone coboundaries. -/
alias boundary_H1_is_cone_H1 := fullBoundaryOrdinaryH1Iso

/-- **The model cone computes the cohomology of the boundary in every degree (principal level six).** For every
rational representation `W` of `Γ(6)` and every degree `k`, the cohomology of `Hom(coneR, W)`, `coneR` the cone of the
model resolutions of the flag, line and plane labels, is `H^k(∂M; W)`. -/
alias model_cone_computes_boundary_cohomology :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.modelBoundary_cohomology_iso

/-- The same for the coefficient systems `Sym^n ⊗ det^e` of the geometric side. -/
alias model_cone_computes_boundary_cohomology_E :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.modelBoundary_cohomology_iso_E

/-- **The face components of the model are the constant-term restrictions (Statements.FaceRestriction).** The boundary
coordinates of a global class are the face components of its geometric restriction. -/
alias model_face_components_are_restrictions :=
  TernaryPeriodPolynomials.Argument.Statements.FaceRestriction.boundary_coordinates_are_face_restrictions

/-- **The cone restriction is the singular restriction to the boundary (link L5, K2).** For every rational representation `W` of
`Γ(6)` and every degree, the geometric restriction of the model, transported by the boundary comparison, is the singular restriction
`H^n(M; W) → H^n(∂M; W)`. -/
alias model_restriction_is_singular_restriction :=
  TernaryPeriodPolynomials.Argument.Statements.FaceRestriction.geoRestriction_is_singular_restriction

variable (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL)

/-- The connecting map `H⁰(B₀, W) → H¹(∂, W)` of the topological Mayer-Vietoris sequence: a corner invariant `u` is the
cone cocycle `(0, 0, u)`, transported to the boundary by the comparison isomorphism. -/
def topologicalConnecting :
    InvariantsB W P Q →ₗ[ℚ] ↑((EquivariantSingularSmall.homCochains fullBoundaryChains W).homology 1) :=
  (fullBoundaryOrdinaryH1Iso W).inv.hom.comp (connecting W P Q)

/-- The map `H¹(∂, W) → H¹(P, W) ⊕ H¹(Q, W)` of the topological Mayer-Vietoris sequence: the face classes of the cone
representative. -/
def topologicalToFaces :
    ↑((EquivariantSingularSmall.homCochains fullBoundaryChains W).homology 1) →ₗ[ℚ] FaceH1 W P Q :=
  (toFaces W P Q).comp (fullBoundaryOrdinaryH1Iso W).hom.hom

/-- **`eq:MV-boundary` for the topological `H¹(∂, W)`.**  For every rational representation `W` of
the full integral group, the sequence
`H⁰(P,W) ⊕ H⁰(Q,W) → H⁰(B₀,W) → H¹(∂,W) → H¹(P,W) ⊕ H¹(Q,W) → H¹(B₀,W)`
is exact at the four interior places (`H⁰(P) ⊕ H⁰(Q)`'s kernel is the image of the common invariants;
`H⁰(B₀)` modulo the face invariants is the image of the connecting map; `H¹(∂)` has face classes zero exactly on the
image of the connecting map; a pair of face classes lifts to `H¹(∂)` exactly when the two restrictions to `B₀`
agree). -/
theorem topological_mv_exact :
    LinearMap.range (invariantDiagonal W P Q) = LinearMap.ker (invariantDifference W P Q) ∧
    LinearMap.range (invariantDifference W P Q) = LinearMap.ker (topologicalConnecting W) ∧
    LinearMap.range (topologicalConnecting W) = LinearMap.ker (topologicalToFaces W) ∧
    LinearMap.range (topologicalToFaces W) = LinearMap.ker (restrictionDifference W P Q) := by
  set E := (fullBoundaryOrdinaryH1Iso W).toLinearEquiv with hE
  have hinv : ∀ y, (fullBoundaryOrdinaryH1Iso W).inv.hom y = E.symm y := fun y => rfl
  have hhom : ∀ y, (fullBoundaryOrdinaryH1Iso W).hom.hom y = E y := fun y => rfl
  refine ⟨range_invariantDiagonal_eq_ker_invariantDifference W P Q, ?_, ?_, ?_⟩
  · rw [range_invariantDifference_eq_ker_connecting]
    ext u
    simp only [LinearMap.mem_ker, topologicalConnecting, LinearMap.comp_apply, hinv]
    exact (map_eq_zero_iff E.symm E.symm.injective).symm
  · have h1 := range_connecting_eq_ker_toFaces W P Q
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      have hu : connecting W P Q u ∈ LinearMap.ker (toFaces W P Q) := by
        rw [← h1]; exact ⟨u, rfl⟩
      simp only [LinearMap.mem_ker, topologicalToFaces, topologicalConnecting,
        LinearMap.comp_apply, hinv, hhom, LinearEquiv.apply_symm_apply]
      exact hu
    · intro h
      have h2 : E y ∈ LinearMap.ker (toFaces W P Q) := by
        simpa only [LinearMap.mem_ker, topologicalToFaces, LinearMap.comp_apply, hhom] using h
      rw [← h1] at h2
      obtain ⟨u, hu⟩ := h2
      refine ⟨u, ?_⟩
      simp only [topologicalConnecting, LinearMap.comp_apply, hinv, hu, LinearEquiv.symm_apply_apply]
  · rw [← range_toFaces_eq_ker_restrictionDifference]
    ext f
    simp only [LinearMap.mem_range, topologicalToFaces, LinearMap.comp_apply, hhom]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨E y, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨E.symm z, by simp⟩

end TernaryPeriodPolynomials.Argument.Statements.BoundaryMayerVietoris
