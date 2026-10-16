module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Stokes
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.CanonFull

@[expose] public section


/-!
# Geometric face pairings: the glue and Lemma C.2 through the canonical identification

With the canonicity of the comparison `Ψ` on all of cohomology (`CanonFull`), the boundary cocycles of the face-wise glue
have the classes `(modelBoundary_cohomology_iso W 2).hom [B]` of the cone lifts `B` of the inner classes
(`cochainClass_eq_isoHom`).  The glue statements therefore become statements about the library's Poincare-duality pairing
`geoPairingBoundary` of the singular cohomology of the boundary `∂M`, with no choice of `Ψ` left:

* `coneLiftGeo`: the class in `H²(∂M; W)` of a cone cocycle;
* `LineGeo c`, `PlaneGeo c` (`lineGeo_of_lineGlue`, `planeGeo_of_planeGlue`): `r (c⁻¹ ⟨b, ξ⟩_Q)` is the geometric pairing of the
  classes of the lifts of `(b, ξ)` and `r ((-c)⁻¹ ⟨ξ, b⟩_P)` likewise (orientations included);
* `geometric_glue`: one constant `c` for both glue statements and for `GlobalStokes c`;
* `geoFaceLine`, `geoFacePlane`, `lemma_C2_geometric_glue`: for global cocycles with edge-exact (zero flag, inner face)
  restrictions, the sum of the two geometric face pairings equals the Poincare-duality pairing `⟨j^* b, j^* a⟩` of the singular
  restrictions to `∂M` of the global classes, and vanishes (geometric Stokes on the compactification).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane
open TernaryPeriodPolynomials.Argument.FacePairingFull.Swap
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology (boundaryChains ambient)
open TernaryPoly.EquivariantSingularResolution

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

attribute [local instance] Comparison.vertexAction

section Classes

open HomologicalComplex TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.SingularBoundaryRestriction TernaryPoly.SymmetricSpaceBoundaryGeometricCone
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SingularLocalCompactCap.Algebra

/-- **A boundary cocycle whose `Ψ`-pullback is cohomologous to a cone cocycle `B` has the class `H(modelBoundary)⁻¹ [B]`.**
With the canonicity of `Ψ` on all of cohomology (`isCarriedPsi_transport_eq`), the class in `H²(∂M; W)` of any boundary
cocycle `β` with `Ψ.f 2 ≫ β = B + d η` is the image of the class of `B` under `(modelBoundary_cohomology_iso W 2).hom`. -/
theorem cochainClass_eq_isoHom {Ψ : coneR ⟶ boundaryChains} (hΨ : IsCarriedPsi Ψ) {W : Rep.{0} ℚ Γ6}
    (B : coneR.X 2 ⟶ W) (hB : coneR.d 3 2 ≫ B = 0)
    (β : boundaryChains.X 2 ⟶ W) (hβ : boundaryChains.d (2 + 1) 2 ≫ β = 0) (η : coneR.X 1 ⟶ W)
    (hη : Ψ.f 2 ≫ β = B + coneR.d 2 1 ≫ η) :
    cochainClass _ 2 (cocycleOf boundaryProjection W 2 β hβ) =
      (modelBoundary_cohomology_iso W 2).hom (cls2 (homCochains coneR W) B hB) := by
  have hcyc : ((homCochains coneR W).d 2 3).hom (Ψ.f 2 ≫ β) = 0 := chainMap_cocycle Ψ β hβ
  let y : Cycles ((homCochains coneR W).sc' (2 - 1) 2 (2 + 1)) := ⟨Ψ.f 2 ≫ β, hcyc⟩
  have hy : y.val =
      (transport Ψ W).f 2 ((cocycleOf boundaryProjection W 2 β hβ).val) := by
    have h := congrArg (fun t => (t.f 2).hom β)
      (SingularLocalCoefficient.cochainIso boundaryProjection boundaryQuotientCovering W).hom_inv_id
    exact (congrArg (fun t => Ψ.f 2 ≫ t) h).symm
  have hdη : ((homCochains coneR W).d 2 3).hom (coneR.d 2 1 ≫ η) = 0 := by
    change coneR.d 3 2 ≫ coneR.d 2 1 ≫ η = 0
    rw [← Category.assoc, coneR.d_comp_d, zero_comp]
  have hB' : ((homCochains coneR W).d 2 3).hom B = 0 := hB
  have hsum : ((homCochains coneR W).d 2 3).hom (B + coneR.d 2 1 ≫ η) = 0 :=
    (map_add ((homCochains coneR W).d 2 3).hom B (coneR.d 2 1 ≫ η)).trans
      ((congrArg₂ (· + ·) hB' hdη).trans (add_zero 0))
  have himg : (homologyMap (modelBoundaryQuasiIso W) 2).hom
      (cochainClass _ 2 (cocycleOf boundaryProjection W 2 β hβ)) = cls2 (homCochains coneR W) B hB := by
    have e1 := congrArg (fun m => m.hom (cochainClass _ 2 (cocycleOf boundaryProjection W 2 β hβ)))
      (isCarriedPsi_transport_eq hΨ W 2)
    refine e1.symm.trans ?_
    rw [cochainClass_natural (transport Ψ W) 2 (cocycleOf boundaryProjection W 2 β hβ) y hy]
    rw [cochainClass_eq_cls2 _ y hcyc]
    calc cls2 (homCochains coneR W) y.val hcyc
        = cls2 (homCochains coneR W) (B + coneR.d 2 1 ≫ η) hsum := cls2_congr _ _ _ hη
      _ = cls2 (homCochains coneR W) B hB + cls2 (homCochains coneR W) (coneR.d 2 1 ≫ η) hdη :=
          cls2_add _ _ _ hB hdη hsum
      _ = cls2 (homCochains coneR W) B hB := by
          rw [(cls2_eq_zero_iff _ _ hdη).2 ⟨η, rfl⟩, add_zero]
  have := congrArg (fun x => (modelBoundary_cohomology_iso W 2).hom x) himg
  refine Eq.trans ?_ this
  have h2 := congrArg (fun m => m.hom (cochainClass _ 2 (cocycleOf boundaryProjection W 2 β hβ)))
    (modelBoundary_cohomology_iso W 2).inv_hom_id
  exact h2.symm

/-- The class in `H²(∂M; W)` of a cone cocycle `B`, through the canonical identification `modelBoundary_cohomology_iso`. -/
def coneLiftGeo (W : Rep.{0} ℚ principalSix) (B : coneR.X 2 ⟶ W) (hB : coneR.d 3 2 ≫ B = 0) :
    (localBoundaryCochains W).homology 2 :=
  (modelBoundary_cohomology_iso W 2).hom (cls2 (homCochains coneR W) B hB)

/-- **Line glue, geometric form**: the model line face pairing is `c` times the Poincare-duality pairing of the boundary
of the classes of the cone lifts, identified through `modelBoundary_cohomology_iso`. -/
def LineGeo (c : ℂ) : Prop :=
  ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line) (ξ : innerClasses n .plane)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane) (s : EdgeCochains n trivialCharacter 1)
    (_hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val)
    (hw : EdgePrimitive z w)
    (_hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val)
    (hs : ∀ x e, y.val.val x (endpoint .plane e) = differentialOneRaw s.val x e),
    r (c⁻¹ * facePairing n b ξ) =
      geoPairingBoundary (coeffRep (rationalCoefficientComponent n trivialCharacter))
        (coneLiftGeo _ (lineLiftA (dualityData n trivialCharacter) r y s)
          (lineLiftA_cocycle (dualityData n trivialCharacter) r hs))
        (coneLiftGeo _ (lineLiftB z w) (lineLiftB_cocycle hw))

/-- **Plane glue, geometric form.** -/
def PlaneGeo (c : ℂ) : Prop :=
  ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane) (b : innerClasses n .line)
    (z : MaximalCycles n trivialCharacter .plane) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .line) (s : EdgeCochains n trivialCharacter 1)
    (_hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z = ξ.val)
    (hw : EdgePrimitiveP z w)
    (_hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) y = b.val)
    (hs : ∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e),
    r (c⁻¹ * facePairingP n ξ b) =
      geoPairingBoundary (coeffRep (rationalCoefficientComponent n trivialCharacter))
        (coneLiftGeo _ (planeLiftA (dualityDataP n trivialCharacter) r y s)
          (planeLiftA_cocycle (dualityDataP n trivialCharacter) r hs))
        (coneLiftGeo _ (planeLiftB z w) (planeLiftB_cocycle hw))

/-- A glue statement for a carried comparison is a geometric statement: the boundary cocycles of the glue have the classes
`modelBoundary_cohomology_iso.hom [cone lift]`. -/
theorem lineGeo_of_lineGlue {Ψ : coneR ⟶ boundaryChains} {c : ℂ} (hΨ : IsCarriedPsi Ψ) (hG : LineGlue Ψ c) :
    LineGeo c := by
  intro n r b ξ z w y s hz hw hy hs
  obtain ⟨⟨β, hβ, α, hα, hPB, hPA⟩, H⟩ := hG n r b ξ z w y s hz hw hy hs
  rw [H β hβ α hα hPB hPA]
  obtain ⟨η, hη⟩ := hPB
  obtain ⟨η', hη'⟩ := hPA
  unfold geoOf coneLiftGeo
  rw [cochainClass_eq_isoHom hΨ _ _ β hβ η hη, cochainClass_eq_isoHom hΨ _ _ α hα η' hη']

theorem planeGeo_of_planeGlue {Ψ : coneR ⟶ boundaryChains} {c : ℂ} (hΨ : IsCarriedPsi Ψ) (hG : PlaneGlue Ψ c) :
    PlaneGeo c := by
  intro n r ξ b z w y s hz hw hy hs
  obtain ⟨⟨β, hβ, α, hα, hPB, hPA⟩, H⟩ := hG n r ξ b z w y s hz hw hy hs
  rw [H β hβ α hα hPB hPA]
  obtain ⟨η, hη⟩ := hPB
  obtain ⟨η', hη'⟩ := hPA
  unfold geoOf coneLiftGeo
  rw [cochainClass_eq_isoHom hΨ _ _ β hβ η hη, cochainClass_eq_isoHom hΨ _ _ α hα η' hη']

end Classes

section Final

open TernaryPoly.EquivariantSingularSmall
open TernaryPoly.SingularLocalDuality (dualRepresentation)

/-- **The face-wise glue in geometric form, with one constant also valid for Lemma C.2.**  There is a single nonzero
constant `c` such that the model line pairing is `c` times, and the model plane pairing `-c` times, the Poincare-duality
pairing of the boundary `∂M` of the classes of the cone lifts of the inner classes (identified with `H²(∂M; ·)` through
`modelBoundary_cohomology_iso`), and such that the Stokes identity `GlobalStokes c` for global classes holds. -/
theorem geometric_glue : ∃ c : ℂ, c ≠ 0 ∧ LineGeo c ∧ PlaneGeo (-c) ∧ GlobalStokes c := by
  obtain ⟨Ω, Ψ, κ, c₀, hcyc, hcar, hq, haug, hκ, hc₀, pairGeo, htr⟩ := exists_pairGeo
  have hg := glue_of_pairGeo hcyc hq hκ hc₀ pairGeo htr
  exact ⟨(κ : ℂ) * c₀, mul_ne_zero (Rat.cast_ne_zero.2 hκ) hc₀, lineGeo_of_lineGlue hcar hg.1,
    planeGeo_of_planeGlue hcar hg.2, global_stokes_of_pairGeo hcyc hq haug hκ hc₀ pairGeo htr⟩

theorem sub_aux (c : ℂ) (r : ℂ →ₗ[ℚ] ℚ) (FQ FP : ℂ) {Gq Gp R : ℚ} (h1 : r (c⁻¹ * FQ) = Gq)
    (h2 : r ((-c)⁻¹ * FP) = Gp) (h3 : r (c⁻¹ * (FQ - FP)) = R) : Gq + Gp = R := by
  rw [← h1, ← h2, ← h3, mul_sub, map_sub, inv_neg, neg_mul, map_neg]
  ring

variable {n : ℕ}

/-- The geometric line face pairing `⟨r_Q a, r_Q b⟩_Q` of the global classes of two edge-exact global cocycles: the
Poincare-duality pairing of the boundary of the classes of the lifts of their line and plane restrictions. -/
def geoFaceLine (r : ℂ →ₗ[ℚ] ℚ) (c1 c2 : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w1 w2 : EdgeCochains n trivialCharacter 1)
    (hw1 : ∀ x e, c1.val.val x = differentialOneRaw w1.val x e)
    (hw2 : ∀ x e, c2.val.val x = differentialOneRaw w2.val x e) : ℚ :=
  geoPairingBoundary (coeffRep (rationalCoefficientComponent n trivialCharacter))
    (coneLiftGeo _ (lineLiftA (dualityData n trivialCharacter) r (restrictionCocycle n trivialCharacter .plane c2) w2)
      (lineLiftA_cocycle (dualityData n trivialCharacter) r (fun x e => hw2 x e)))
    (coneLiftGeo _ (lineLiftB (restrictionCocycle n trivialCharacter .line c1) w1)
      (lineLiftB_cocycle (fun x e => hw1 x e)))

/-- The geometric plane face pairing `⟨r_P a, r_P b⟩_P`. -/
def geoFacePlane (r : ℂ →ₗ[ℚ] ℚ) (c1 c2 : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w1 w2 : EdgeCochains n trivialCharacter 1)
    (hw1 : ∀ x e, c1.val.val x = differentialOneRaw w1.val x e)
    (hw2 : ∀ x e, c2.val.val x = differentialOneRaw w2.val x e) : ℚ :=
  geoPairingBoundary (coeffRep (rationalCoefficientComponent n trivialCharacter))
    (coneLiftGeo _ (planeLiftA (dualityDataP n trivialCharacter) r (restrictionCocycle n trivialCharacter .line c2) w2)
      (planeLiftA_cocycle (dualityDataP n trivialCharacter) r (fun x e => hw2 x e)))
    (coneLiftGeo _ (planeLiftB (restrictionCocycle n trivialCharacter .plane c1) w1)
      (planeLiftB_cocycle (fun x e => hw1 x e)))

/-- **Lemma C.2 in geometric form.**  There is a nonzero constant `c` (independent of everything else) such that for global
cocycles `c1, c2` with edge-exact restrictions (zero flag restrictions and inner face restrictions) and every `ℚ`-linear
`r : ℂ → ℚ`:
`geoFaceLine + geoFacePlane = ⟨j^* b, j^* a⟩_{∂M}`, the Poincare-duality pairing of the singular restrictions to `∂M` of the
global classes `a = [c1] ∈ H²(M; E)`, `b = [c2 ∘ φ] ∈ H²(M; E^∨)`, and the right-hand side is `0` (Stokes on `M̄`). -/
theorem lemma_C2_geometric_glue :
    ∃ c : ℂ, c ≠ 0 ∧ LineGeo c ∧ PlaneGeo (-c) ∧ ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ)
      (c1 c2 : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
      (w1 w2 : EdgeCochains n trivialCharacter 1)
      (hw1 : ∀ x e, c1.val.val x = differentialOneRaw w1.val x e)
      (hw2 : ∀ x e, c2.val.val x = differentialOneRaw w2.val x e),
      geoFaceLine r c1 c2 w1 w2 hw1 hw2 + geoFacePlane r c1 c2 w1 w2 hw1 hw2 =
        geoPairingBoundary (coeffRep (rationalCoefficientComponent n trivialCharacter))
          (restrictedClass _ (dualGlobalClass r c2)) (restrictedClass _ (globalClass c1)) ∧
      geoFaceLine r c1 c2 w1 w2 hw1 hw2 + geoFacePlane r c1 c2 w1 w2 hw1 hw2 = 0 := by
  obtain ⟨c, hc, hQ, hP, hS⟩ := geometric_glue
  refine ⟨c, hc, hQ, hP, fun n r c1 c2 w1 w2 hw1 hw2 => ?_⟩
  have h1 := hQ n r
    ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
        (restrictionCocycle n trivialCharacter .line c1), innerBoundary_restriction_of_exact c1 w1 hw1 .line⟩
    ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
        (restrictionCocycle n trivialCharacter .plane c2), innerBoundary_restriction_of_exact c2 w2 hw2 .plane⟩
    (restrictionCocycle n trivialCharacter .line c1) w1 (restrictionCocycle n trivialCharacter .plane c2) w2
    rfl (fun x e => hw1 x e) rfl (fun x e => hw2 x e)
  have h2 := hP n r
    ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
        (restrictionCocycle n trivialCharacter .plane c1), innerBoundary_restriction_of_exact c1 w1 hw1 .plane⟩
    ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
        (restrictionCocycle n trivialCharacter .line c2), innerBoundary_restriction_of_exact c2 w2 hw2 .line⟩
    (restrictionCocycle n trivialCharacter .plane c1) w1 (restrictionCocycle n trivialCharacter .line c2) w2
    rfl (fun x e => hw1 x e) rfl (fun x e => hw2 x e)
  have h3 := hS n r c1 c2 w1 w2 hw1 hw2
  have hsum := sub_aux c r _ _ h1 h2 (by unfold stokesDefect at h3; exact h3)
  exact ⟨hsum, hsum.trans (geoPairing_restrictedClass_zero _ _ _)⟩

end Final

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
