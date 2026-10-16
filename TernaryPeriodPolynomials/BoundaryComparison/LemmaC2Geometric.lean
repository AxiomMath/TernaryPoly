module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.GeoFace
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FaceCoords
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.FacePairing

@[expose] public section


/-!
# Lemma C.2 and `ar:eq:facepair` in geometric form (Appendix C)

Formalized by Claude Sonnet 5.5.

The model face pairings of `Exports/FacePairing.lean` (`facePairing`, `Plane.facePairingP`: cone cup products of the cochain
model) are compared with the library's Poincare-duality pairing `geoPairingBoundary` of the singular cohomology of the actual
boundary `∂M` of the Borel-Serre compactification.

* `geoLinePairing`, `geoPlanePairing` (**geometric face pairings**): for inner classes `b` (line), `ξ` (plane) the value of
  `geoPairingBoundary` on the classes in `H²(∂M; E)`, `H²(∂M; E^∨)` (the latter through a `ℚ`-linear functional `r : ℂ → ℚ`) of
  the cone lifts (`innerLineCone`, `innerPlaneCone` of `Comparison/InnerLift.lean`, and their `φ`-twists) of `b`, `ξ`, identified
  with the singular cohomology of `∂M` through `modelBoundary_cohomology_iso` (the library's quasi-isomorphism of the boundary
  cochains with the model cone, `coneEquiv`, `faceConeStabilizerEquiv`).  They are defined by the library's pairing alone; no
  comparison map `Ψ` is involved (`Glue.CanonFull`: the glue comparison induces `modelBoundary_cohomology_iso` on all of
  cohomology).
* `facePairing_geometric` (**`ar:eq:facepair`, comparison with Poincare duality**): there is one nonzero constant `c` with
  `r (c⁻¹ ⟨b, ξ⟩_Q) = geoLinePairing`, `r ((-c)⁻¹ ⟨ξ, b⟩_P) = geoPlanePairing` for every `r`: the line and plane face carry
  opposite orientations (the sign is derived from the cone differential, `Glue.PlaneDict`).  The normalization `c` (orientation
  of the comparison with the boundary fundamental class, and the unnormalized constant of the cone/trace comparison) is not
  computed; every statement is homogeneous in it.
* `geoLinePairing_perfect`, `geoPlanePairing_perfect` (**perfectness of the geometric face pairings**), from the perfectness of
  the model pairings (`Statements.FacePairing.facePairing_perfect_all`, `facePairingP_perfect_all`) through the comparison.
* `lemma_C2_geometric` (**Lemma C.2, `ar:lem:stokes`, in geometric form**): for global cocycles `c1`, `c2` of the arithmetic level
  with zero flag restrictions (edge-exact: `hw1`, `hw2`), representing `a ∈ H²(M; E)` and (through the `φ`-twist and `r`)
  `b ∈ H²(M; E^∨)`:
  `⟨r_Q a, r_P b⟩^{geo}_Q + ⟨r_P a, r_Q b⟩^{geo}_P = ⟨j^* b, j^* a⟩_{∂M} = 0`,
  where `j^*` is the library's singular restriction `H²(M; ·) → H²(∂M; ·)` (`Glue.restrictedClass`) and the vanishing is the
  geometric Stokes theorem on the compactification (`geoPairingBoundary_restriction`).  The Lean proof is the comparison of the
  cone cup product of the cone lifts of the global classes (whose corner component has the vanishing flag terms) with the face
  pairings (`Glue.Stokes.global_stokes_of_pairGeo`, `Glue.Main.glue_of_pairGeo`), not a de Rham / collar argument.
* `lemma_C2_model_vs_geometric`: the same identity expressed for the model pairings (`GlobalStokes`).

What is NOT proved here: (1) the absolute sign/value of `c`; (2) that `geoLinePairing` is the pairing of the compactly supported
cohomology of the open face `Q` with the cohomology of `Q` (per-face Poincare duality for non-compact faces): only the comparison
of the model pairing with the pairing of the closed manifold `∂M` on lifts is proved; (3) that library's restriction maps
to the open faces agree with the model's `coneLine`, `conePlane` on arbitrary classes of `H²(∂M; ·)` (they agree on restrictions
of global classes: `boundary_coordinates_are_face_restrictions`, `singular_restriction_eq_geoRestriction`).
-/


open CategoryTheory Limits MonoidalCategory
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.LemmaC2Geometric

variable {n : ℕ}

theorem exists_line_reps (b : innerClasses n .line) :
    ∃ (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1),
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val ∧
        EdgePrimitive z w := by
  obtain ⟨z, hz, u, hu⟩ := b.property
  exact ⟨z, u, hz, fun x e => hu x e⟩

theorem exists_plane_dual_reps (ξ : innerClasses n .plane) :
    ∃ (y : MaximalCycles n trivialCharacter .plane) (s : EdgeCochains n trivialCharacter 1),
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val ∧
        ∀ x e, y.val.val x (endpoint .plane e) = differentialOneRaw s.val x e := by
  obtain ⟨y, hy, u, hu⟩ := ξ.property
  exact ⟨y, u, hy, fun x e => hu x e⟩

theorem exists_plane_reps (ξ : innerClasses n .plane) :
    ∃ (z : MaximalCycles n trivialCharacter .plane) (w : EdgeCochains n trivialCharacter 1),
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z = ξ.val ∧
        EdgePrimitiveP z w := by
  obtain ⟨z, hz, u, hu⟩ := ξ.property
  exact ⟨z, u, hz, fun x e => hu x e⟩

theorem exists_line_dual_reps (b : innerClasses n .line) :
    ∃ (y : MaximalCycles n trivialCharacter .line) (s : EdgeCochains n trivialCharacter 1),
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) y = b.val ∧
        ∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e := by
  obtain ⟨y, hy, u, hu⟩ := b.property
  exact ⟨y, u, hy, fun x e => hu x e⟩

/-- **The geometric line face pairing** of an inner line class `b` (coefficients `E`) and an inner plane class `ξ` (the
`φ`-twist, coefficients `E^∨` through `r`): the Poincare-duality pairing `geoPairingBoundary` of the boundary `∂M` of the
classes of the cone lifts of `b` and `ξ`, identified with `H²(∂M; ·)` through `modelBoundary_cohomology_iso`.  It depends on
the chosen representatives only through the classes (`geoLinePairing_eq`). -/
def geoLinePairing (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line) (ξ : innerClasses n .plane) : ℚ :=
  geoPairingBoundary (coeffRep (rationalCoefficientComponent n trivialCharacter))
    (coneLiftGeo _ (lineLiftA (dualityData n trivialCharacter) r (exists_plane_dual_reps ξ).choose
        (exists_plane_dual_reps ξ).choose_spec.choose)
      (lineLiftA_cocycle (dualityData n trivialCharacter) r (exists_plane_dual_reps ξ).choose_spec.choose_spec.2))
    (coneLiftGeo _ (lineLiftB (exists_line_reps b).choose (exists_line_reps b).choose_spec.choose)
      (lineLiftB_cocycle (exists_line_reps b).choose_spec.choose_spec.2))

/-- **The geometric plane face pairing** of an inner plane class `ξ` and an inner line class `b` (the plane-supported twin). -/
def geoPlanePairing (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane) (b : innerClasses n .line) : ℚ :=
  geoPairingBoundary (coeffRep (rationalCoefficientComponent n trivialCharacter))
    (coneLiftGeo _ (planeLiftA (dualityDataP n trivialCharacter) r (exists_line_dual_reps b).choose
        (exists_line_dual_reps b).choose_spec.choose)
      (planeLiftA_cocycle (dualityDataP n trivialCharacter) r (exists_line_dual_reps b).choose_spec.choose_spec.2))
    (coneLiftGeo _ (planeLiftB (exists_plane_reps ξ).choose (exists_plane_reps ξ).choose_spec.choose)
      (planeLiftB_cocycle (exists_plane_reps ξ).choose_spec.choose_spec.2))

theorem geoLinePairing_eq {c : ℂ} (hQ : LineGeo c) (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line)
    (ξ : innerClasses n .plane) : r (c⁻¹ * facePairing n b ξ) = geoLinePairing n r b ξ :=
  hQ n r b ξ (exists_line_reps b).choose (exists_line_reps b).choose_spec.choose
    (exists_plane_dual_reps ξ).choose (exists_plane_dual_reps ξ).choose_spec.choose
    (exists_line_reps b).choose_spec.choose_spec.1
    (exists_line_reps b).choose_spec.choose_spec.2 (exists_plane_dual_reps ξ).choose_spec.choose_spec.1
    (exists_plane_dual_reps ξ).choose_spec.choose_spec.2

theorem geoPlanePairing_eq {c : ℂ} (hP : PlaneGeo c) (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane)
    (b : innerClasses n .line) : r (c⁻¹ * Plane.facePairingP n ξ b) = geoPlanePairing n r ξ b :=
  hP n r ξ b (exists_plane_reps ξ).choose (exists_plane_reps ξ).choose_spec.choose
    (exists_line_dual_reps b).choose (exists_line_dual_reps b).choose_spec.choose
    (exists_plane_reps ξ).choose_spec.choose_spec.1
    (exists_plane_reps ξ).choose_spec.choose_spec.2 (exists_line_dual_reps b).choose_spec.choose_spec.1
    (exists_line_dual_reps b).choose_spec.choose_spec.2

/-- **`ar:eq:facepair`, geometric form.**  There is a nonzero constant `c` (the orientation / normalization constant of the
comparison with the boundary fundamental class) such that the model face pairings are the geometric ones:
`r (c⁻¹ ⟨b, ξ⟩_Q) = ⟨b, ξ⟩^{geo}_Q` for the line face and `r ((-c)⁻¹ ⟨ξ, b⟩_P) = ⟨ξ, b⟩^{geo}_P` for the plane face (the opposite
orientation of the two faces is the sign), for every `ℚ`-linear `r : ℂ → ℚ`.  The right-hand sides are defined by
`geoPairingBoundary` alone. -/
theorem facePairing_geometric : ∃ c : ℂ, c ≠ 0 ∧
    (∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line) (ξ : innerClasses n .plane),
      r (c⁻¹ * facePairing n b ξ) = geoLinePairing n r b ξ) ∧
    ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane) (b : innerClasses n .line),
      r ((-c)⁻¹ * Plane.facePairingP n ξ b) = geoPlanePairing n r ξ b := by
  exact geometric_glue.elim (fun c hc => ⟨c, hc.1, geoLinePairing_eq hc.2.1, geoPlanePairing_eq hc.2.2.1⟩)

/-- **`ar:eq:facepair` for the geometric line pairing is perfect, every `n`.** -/
theorem geoLinePairing_perfect (n : ℕ) :
    (∀ b : innerClasses n .line, (∀ (ξ : innerClasses n .plane) (r : ℂ →ₗ[ℚ] ℚ), geoLinePairing n r b ξ = 0) → b = 0) ∧
      ∀ ξ : innerClasses n .plane, (∀ (b : innerClasses n .line) (r : ℂ →ₗ[ℚ] ℚ), geoLinePairing n r b ξ = 0) → ξ = 0 := by
  obtain ⟨c, hc, hQ, -⟩ := facePairing_geometric
  have key : ∀ (b : innerClasses n .line) (ξ : innerClasses n .plane),
      (∀ r : ℂ →ₗ[ℚ] ℚ, geoLinePairing n r b ξ = 0) → facePairing n b ξ = 0 := by
    intro b ξ h
    have h0 : c⁻¹ * facePairing n b ξ = 0 :=
      (Module.forall_dual_apply_eq_zero_iff ℚ (c⁻¹ * facePairing n b ξ)).1 (fun r => (hQ n r b ξ).trans (h r))
    exact (mul_eq_zero.1 h0).resolve_left (inv_ne_zero hc)
  have hperf := Statements.FacePairing.facePairing_perfect_all n
  exact ⟨fun b h => hperf.1 b (fun ξ => key b ξ (fun r => h ξ r)),
    fun ξ h => hperf.2 ξ (fun b => key b ξ (fun r => h b r))⟩

/-- **The geometric plane pairing is perfect, every `n`.** -/
theorem geoPlanePairing_perfect (n : ℕ) :
    (∀ ξ : innerClasses n .plane, (∀ (b : innerClasses n .line) (r : ℂ →ₗ[ℚ] ℚ), geoPlanePairing n r ξ b = 0) → ξ = 0) ∧
      ∀ b : innerClasses n .line, (∀ (ξ : innerClasses n .plane) (r : ℂ →ₗ[ℚ] ℚ), geoPlanePairing n r ξ b = 0) → b = 0 := by
  obtain ⟨c, hc, -, hP⟩ := facePairing_geometric
  have key : ∀ (ξ : innerClasses n .plane) (b : innerClasses n .line),
      (∀ r : ℂ →ₗ[ℚ] ℚ, geoPlanePairing n r ξ b = 0) → Plane.facePairingP n ξ b = 0 := by
    intro ξ b h
    have h0 : (-c)⁻¹ * Plane.facePairingP n ξ b = 0 :=
      (Module.forall_dual_apply_eq_zero_iff ℚ ((-c)⁻¹ * Plane.facePairingP n ξ b)).1
        (fun r => (hP n r ξ b).trans (h r))
    exact (mul_eq_zero.1 h0).resolve_left (inv_ne_zero (neg_ne_zero.2 hc))
  have hperf := Statements.FacePairing.facePairingP_perfect_all n
  exact ⟨fun ξ h => hperf.1 ξ (fun b => key ξ b (fun r => h b r)),
    fun b h => hperf.2 b (fun ξ => key ξ b (fun r => h ξ r))⟩

/-- The inner line class of the line restriction of an edge-exact global cocycle (`r_Q a`). -/
def lineInnerClass (c1 : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w1 : EdgeCochains n trivialCharacter 1) (hw1 : ∀ x e, c1.val.val x = differentialOneRaw w1.val x e) :
    innerClasses n .line :=
  ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
    (restrictionCocycle n trivialCharacter .line c1), innerBoundary_restriction_of_exact c1 w1 hw1 .line⟩

/-- The inner plane class of the plane restriction of an edge-exact global cocycle (`r_P a`). -/
def planeInnerClass (c1 : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w1 : EdgeCochains n trivialCharacter 1) (hw1 : ∀ x e, c1.val.val x = differentialOneRaw w1.val x e) :
    innerClasses n .plane :=
  ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
    (restrictionCocycle n trivialCharacter .plane c1), innerBoundary_restriction_of_exact c1 w1 hw1 .plane⟩

/-- **Lemma C.2 (`ar:lem:stokes`) in geometric form.**  For global cocycles `c1` (the class `a ∈ H²(M; E)`) and `c2` (whose
`φ`-twist, paired into `ℚ` by `r`, is the class `b ∈ H²(M; E^∨)`) of the arithmetic level with zero flag restrictions and inner
face restrictions (edge-exact, `hw1`, `hw2`):

`⟨r_Q a, r_P b⟩^{geo}_Q + ⟨r_P a, r_Q b⟩^{geo}_P = ⟨j^* b, j^* a⟩_{∂M} = 0`

where the face pairings are the geometric face pairings (`geoLinePairing`, `geoPlanePairing`: Poincare duality
`geoPairingBoundary` of the singular cohomology of the boundary, on the classes of the inner lifts), `j^*` is the singular
restriction `H²(M; ·) → H²(∂M; ·)` of the library and the right-hand side vanishes by the geometric Stokes theorem on the
compactification (`geoPairingBoundary_restriction`).  The orientation of the faces is the relative sign in the two glue
statements of `facePairing_geometric`. -/
theorem lemma_C2_geometric (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ)
    (c1 c2 : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w1 w2 : EdgeCochains n trivialCharacter 1)
    (hw1 : ∀ x e, c1.val.val x = differentialOneRaw w1.val x e)
    (hw2 : ∀ x e, c2.val.val x = differentialOneRaw w2.val x e) :
    geoLinePairing n r (lineInnerClass c1 w1 hw1) (planeInnerClass c2 w2 hw2) +
        geoPlanePairing n r (planeInnerClass c1 w1 hw1) (lineInnerClass c2 w2 hw2) =
      geoPairingBoundary (coeffRep (rationalCoefficientComponent n trivialCharacter))
        (restrictedClass _ (dualGlobalClass r c2)) (restrictedClass _ (globalClass c1)) ∧
    geoLinePairing n r (lineInnerClass c1 w1 hw1) (planeInnerClass c2 w2 hw2) +
        geoPlanePairing n r (planeInnerClass c1 w1 hw1) (lineInnerClass c2 w2 hw2) = 0 := by
  refine lemma_C2_geometric_glue.elim (fun c hc => ?_)
  have hQ : LineGeo c := hc.2.1
  have hP : PlaneGeo (-c) := hc.2.2.1
  have hH := hc.2.2.2 n r c1 c2 w1 w2 hw1 hw2
  have e1 : geoFaceLine r c1 c2 w1 w2 hw1 hw2 =
      geoLinePairing n r (lineInnerClass c1 w1 hw1) (planeInnerClass c2 w2 hw2) :=
    (hQ n r (lineInnerClass c1 w1 hw1) (planeInnerClass c2 w2 hw2) (restrictionCocycle n trivialCharacter .line c1) w1
      (restrictionCocycle n trivialCharacter .plane c2) w2 rfl (fun x e => hw1 x e) rfl (fun x e => hw2 x e)).symm.trans
      (geoLinePairing_eq hQ n r _ _)
  have e2 : geoFacePlane r c1 c2 w1 w2 hw1 hw2 =
      geoPlanePairing n r (planeInnerClass c1 w1 hw1) (lineInnerClass c2 w2 hw2) :=
    (hP n r (planeInnerClass c1 w1 hw1) (lineInnerClass c2 w2 hw2) (restrictionCocycle n trivialCharacter .plane c1) w1
      (restrictionCocycle n trivialCharacter .line c2) w2 rfl (fun x e => hw1 x e) rfl (fun x e => hw2 x e)).symm.trans
      (geoPlanePairing_eq hP n r _ _)
  rw [e1, e2] at hH
  exact hH

/-- **Lemma C.2 for the model pairings, compared with the geometric pairing of the singular restrictions**
(`Glue.global_stokes_glue`): `r (c⁻¹ (⟨r_Q a, r_P b⟩_Q - ⟨r_P a, r_Q b⟩_P)) = ⟨j^* b, j^* a⟩_{∂M}` for edge-exact global cocycles, in
the model conventions (the paper's `⟨ , ⟩_P` has the opposite orientation). -/
theorem lemma_C2_model_vs_geometric : ∃ c : ℂ, c ≠ 0 ∧ Glue.GlobalStokes c :=
  Glue.global_stokes_glue

/-- **Intrinsic coordinates of the lifts** (`Glue.lineLift_faceCoords`): the boundary cocycles of the face-wise glue have the
face coordinates `(b, 0)` (line lift) and `(0, ξ)` (plane lift), for the face coordinates defined by the cone's line and plane
components through `modelBoundary_cohomology_iso`. -/
alias lineLift_faceCoords := Glue.lineLift_faceCoords

alias planeLift_faceCoords := Glue.planeLift_faceCoords

alias lineLiftA_faceCoords := Glue.lineLiftA_faceCoords

alias planeLiftA_faceCoords := Glue.planeLiftA_faceCoords

/-- **The comparison of the face-wise glue is the library's identification on all of cohomology** (`Glue.facePairing_glue_canonical`;
route: strata of the two cone maps are homotopic by the uniqueness of maps from a complex of projectives to a resolution
over the augmentation (`uniqHomotopy`), and the cone-level uniqueness `Glue.cone_maps_homotopic` (the connecting obstruction lies
in `Hom(A, L')`, `Hom(A, P')` with `L'`, `P'` resolutions: acyclic in positive degrees)). -/
alias facePairing_glue_canonical := Glue.facePairing_glue_canonical

end TernaryPeriodPolynomials.Argument.Statements.LemmaC2Geometric
