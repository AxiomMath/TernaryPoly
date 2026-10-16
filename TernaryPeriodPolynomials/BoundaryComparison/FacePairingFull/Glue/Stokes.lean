module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Global
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Canon
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Main
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.TraceEvalV
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.StokesPairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.SingularRestriction
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.GeoStokes

@[expose] public section


/-!
# Lemma C.2 in the model, compared with the geometric Stokes theorem of the boundary

For two global cocycles `c1, c2` of the arithmetic level with edge-exact restrictions (the model of global classes `a ∈
H²(M; E)`, `b ∈ H²(M; E*)` with inner face restrictions), `global_stokes_glue` identifies, for every `ℚ`-linear functional
`r : ℂ → ℚ`, the defect `⟨r_Q c1, r_P c2⟩_Q - ⟨r_P c1, r_Q c2⟩_P` of the model Stokes identity (the model pairings of
`FacePairingForm` and `Plane.Pairing`, which `facePairingP_global_eq_facePairing_global` proves equal) with the geometric
Poincaré-duality pairing `geoPairingBoundary` of the library of the singular restrictions `j^*` of the two global classes
(`restrictedClass`: the group cohomology class on the point resolution, `groupLocalCohomologyIso`, restriction to `∂M`):

`r (c⁻¹ * stokesDefect) = geoPairingBoundary V (j^* [c2 ∘ φ]) (j^* [c1])`,

for a nonzero constant `c` independent of everything else.  The right-hand side vanishes by the geometric Stokes theorem
(`geoPairingBoundary_restriction`), so `global_stokes_geometric` and `stokesDefect_eq_zero` re-prove the model identity
from the geometry.  The proof expands the pairing of the Rep-level cone cochains `coneToPt^* c1` and `coneToPt^* (c2 ∘ φ)`
(whose corner components vanish: `pair_global`) as the evaluation of the difference of the vertex primitives, compares it
with the model's face pairings (`traceValue_eq_evalCorner`: both equal `c₀` times the evaluation on the corner chain, with
the flag-independent terms `w ⌣ (c2 ∘ φ)` cancelling) and identifies the boundary classes through the comparison `Ψ` over the
augmentation (`cochainClass_eq_restrictedClass`, `transport_restriction`).  Here the right-hand classes are the actual
singular restrictions, not classes defined through a choice of homotopy inverse of `Ψ`.

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

section ModelDiff

variable {n : ℕ}

theorem boundaryValue_sub_boundaryValueP (w : EdgeCochains n trivialCharacter 1)
    (c2 : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (γL : (Fin 4 → RationalGL3) → Flags .line → ℂ) (γP : (Fin 4 → RationalGL3) → Flags .plane → ℂ) :
    (fun x e => boundaryValue (dualityData n trivialCharacter) w
        (restrictionCocycle n trivialCharacter .plane c2) γL x e -
      boundaryValueP (dualityDataP n trivialCharacter) w
        (restrictionCocycle n trivialCharacter .line c2) γP x e) =
      fun x e => γP x (endpoint .plane e) - γL x (endpoint .line e) := by
  funext x e
  change (dualPairing n (w.val ![x 0, x 1] e) (c2.val.val ![dualInvolution (x 1), dualInvolution (x 2),
        dualInvolution (x 3)]) - γL x (endpoint .line e)) -
      (dualPairing n (w.val ![x 0, x 1] e) (c2.val.val ![dualInvolution (x 1), dualInvolution (x 2),
        dualInvolution (x 3)]) - γP x (endpoint .plane e)) = _
  abel

end ModelDiff

section Classes

open HomologicalComplex TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.SingularBoundaryRestriction TernaryPoly.SymmetricSpaceBoundaryGeometricCone
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SingularLocalCompactCap.Algebra

/-- The class of a degree-two cocycle `f` of the point resolution (model cohomology of `Γ(6)`). -/
def ptClassOf {W : Rep.{0} ℚ Γ6} (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ W)
    (hf : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0) :
    (homCochains (prodComplex Γ6 RationalGL3 PUnit) W).homology 2 :=
  cls2 (homCochains (prodComplex Γ6 RationalGL3 PUnit) W) f hf

/-- **The singular restriction `j^*` of a class of `H²(Γ(6); W)` to the boundary `∂M`.** -/
def restrictedClass (W : Rep.{0} ℚ principalSix)
    (x : (homCochains (prodComplex Γ6 RationalGL3 PUnit) W).homology 2) :
    (localBoundaryCochains W).homology 2 :=
  (fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) W 2 ≫
    (SingularLocalCoefficient.groupLocalCohomologyIso wholeProjection wholeQuotientCovering W 2).hom ≫
      homologyMap (geometricBoundaryRestriction W) 2).hom x

/-- **`Ψ` and the library's `modelBoundaryQuasiIso` induce the same map on the singular restrictions**: both send `j^* x`
to the geometric restriction `H(coneToPt) x` of the model cone (`transport_restriction` and
`singular_restriction_eq_geoRestriction`). -/
theorem transport_eq_modelBoundary_on_restriction {Ψ : coneR ⟶ boundaryChains} (haug : Ψ ≫ augB = augR)
    (W : Rep.{0} ℚ principalSix) (x : (homCochains (prodComplex Γ6 RationalGL3 PUnit) W).homology 2) :
    (homologyMap (transport Ψ W) 2).hom (restrictedClass W x) =
      (homologyMap (modelBoundaryQuasiIso W) 2).hom (restrictedClass W x) :=
  (congrArg (fun m => m.hom x) (transport_restriction W Ψ haug 2)).trans
    (congrArg (fun m => m.hom x) (singular_restriction_eq_geoRestriction W 2)).symm

theorem cochainClass_eq_cls2 (K : CochainComplex (ModuleCat.{0} ℚ) ℕ) (x : Cycles (K.sc' (2 - 1) 2 (2 + 1)))
    (hx : (K.d 2 3).hom x.val = 0) :
    cochainClass K 2 x = cls2 K x.val hx := by
  have hcls : ∀ (T : ShortComplex (ModuleCat.{0} ℚ)) (z : Cycles T),
      TernaryPoly.SingularLocalCap.Homology.cycleClass T z = T.homologyπ.hom (T.moduleCatCyclesIso.inv.hom z) := by
    intro T z
    have := congrArg (fun t => t.hom z) T.moduleCatCyclesIso_inv_π
    exact this.symm
  unfold cochainClass cls2
  rw [hcls]
  have h1 := congrArg (fun t => t.hom ((K.sc' (2 - 1) 2 (2 + 1)).moduleCatCyclesIso.inv.hom x))
    (K.π_homologyIsoSc'_inv (2 - 1) 2 (2 + 1) (up_prev _) (up_next _))
  refine h1.trans (congrArg (K.homologyπ 2).hom ?_)
  apply iCycles_injective K 2
  have h2 := congrArg (fun t => t.hom ((K.sc' (2 - 1) 2 (2 + 1)).moduleCatCyclesIso.inv.hom x))
    (K.cyclesIsoSc'_inv_iCycles (2 - 1) 2 (2 + 1) (up_prev _) (up_next _))
  have h3 := congrArg (fun t => t.hom x) (K.sc' (2 - 1) 2 (2 + 1)).moduleCatCyclesIso_inv_iCycles
  exact (h2.trans h3).trans (iCycles_cycle2 K x.val hx).symm

theorem transport_quasiIso {Ψ : coneR ⟶ boundaryChains} (hq : QuasiIso Ψ) (W : Rep.{0} ℚ principalSix) :
    QuasiIso (transport Ψ W) := by
  have hp1 : ∀ n, Projective (coneR.X n) := coneR_projective
  have hp2 : ∀ n, Projective (boundaryChains.X n) :=
    fun n => chainRep_projective principalSix ambient n
  obtain ⟨e, he⟩ : ∃ e : _root_.HomotopyEquiv coneR boundaryChains, e.hom = Ψ :=
    (ChainComplex.quasiIso_iff_of_projective Ψ).mp hq
  have h1 : QuasiIso (homPullback e.hom W) := homPullback_quasiIso_of_homotopyEquiv e W
  rw [he] at h1
  exact _root_.quasiIso_comp _ _

/-- The cohomology class (in `H²(∂M; W)`) of a boundary cocycle `β` whose pullback along `Ψ` is cohomologous to the
cone restriction `coneToPt^* f` of a cocycle `f` of the point resolution is the singular restriction `j^*` of the class
of `f`: the comparison `Ψ` is canonical on restriction classes. -/
theorem cochainClass_eq_restrictedClass {Ψ : coneR ⟶ boundaryChains} (hq : QuasiIso Ψ) (haug : Ψ ≫ augB = augR)
    {W : Rep.{0} ℚ Γ6} (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ W)
    (hf : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0)
    (β : boundaryChains.X 2 ⟶ W) (hβ : boundaryChains.d (2 + 1) 2 ≫ β = 0) (η : coneR.X 1 ⟶ W)
    (hη : Ψ.f 2 ≫ β = coneToPt.f 2 ≫ f + coneR.d 2 1 ≫ η) :
    cochainClass _ 2 (cocycleOf boundaryProjection W 2 β hβ) = restrictedClass W (ptClassOf f hf) := by
  have hiso := transport_quasiIso hq W
  have hinj : Function.Injective (homologyMap (transport Ψ W) 2).hom :=
    (ModuleCat.mono_iff_injective (homologyMap (transport Ψ W) 2)).1 inferInstance
  apply hinj
  -- the image of the restriction class
  have hres : (homologyMap (transport Ψ W) 2).hom (restrictedClass W (ptClassOf f hf)) =
      (homologyMap (homPullback coneToPt W) 2).hom (ptClassOf f hf) :=
    congrArg (fun m => m.hom (ptClassOf f hf)) (transport_restriction W Ψ haug 2)
  rw [hres]
  have hB : ((homCochains coneR W).d 2 3).hom (coneToPt.f 2 ≫ f) = 0 := by
    change coneR.d 3 2 ≫ coneToPt.f 2 ≫ f = 0
    rw [← Category.assoc, ← coneToPt.comm 3 2, Category.assoc, hf, comp_zero]
  have hmap : (homologyMap (homPullback coneToPt W) 2).hom (ptClassOf f hf) =
      cls2 (homCochains coneR W) (coneToPt.f 2 ≫ f) hB :=
    cls2_map (homCochains (prodComplex Γ6 RationalGL3 PUnit) W) (homPullback coneToPt W) f hf _
  rw [hmap]
  -- the image of the class of `β`
  have hcyc : ((homCochains coneR W).d 2 3).hom (Ψ.f 2 ≫ β) = 0 := chainMap_cocycle Ψ β hβ
  let y : Cycles ((homCochains coneR W).sc' (2 - 1) 2 (2 + 1)) := ⟨Ψ.f 2 ≫ β, hcyc⟩
  have hy : y.val =
      (transport Ψ W).f 2 ((cocycleOf boundaryProjection W 2 β hβ).val) := by
    have h := congrArg (fun t => (t.f 2).hom β)
      (SingularLocalCoefficient.cochainIso boundaryProjection boundaryQuotientCovering W).hom_inv_id
    exact (congrArg (fun t => Ψ.f 2 ≫ t) h).symm
  rw [cochainClass_natural (transport Ψ W) 2 (cocycleOf boundaryProjection W 2 β hβ) y hy]
  rw [cochainClass_eq_cls2 _ y hcyc]
  have hdη : ((homCochains coneR W).d 2 3).hom (coneR.d 2 1 ≫ η) = 0 := by
    change coneR.d 3 2 ≫ coneR.d 2 1 ≫ η = 0
    rw [← Category.assoc, coneR.d_comp_d, zero_comp]
  have hsum : ((homCochains coneR W).d 2 3).hom (coneToPt.f 2 ≫ f + coneR.d 2 1 ≫ η) = 0 := by
    exact (map_add ((homCochains coneR W).d 2 3).hom (coneToPt.f 2 ≫ f) (coneR.d 2 1 ≫ η)).trans
      ((congrArg₂ (· + ·) hB hdη).trans (add_zero 0))
  calc cls2 (homCochains coneR W) y.val hcyc
      = cls2 (homCochains coneR W) (coneToPt.f 2 ≫ f + coneR.d 2 1 ≫ η) hsum :=
        cls2_congr _ _ _ hη
    _ = cls2 (homCochains coneR W) (coneToPt.f 2 ≫ f) hB + cls2 (homCochains coneR W) (coneR.d 2 1 ≫ η) hdη :=
        cls2_add _ _ _ hB hdη hsum
    _ = cls2 (homCochains coneR W) (coneToPt.f 2 ≫ f) hB := by
        rw [(cls2_eq_zero_iff _ _ hdη).2 ⟨η, rfl⟩, add_zero]

end Classes

section Final

open TernaryPoly.EquivariantSingularSmall
open TernaryPoly.SingularLocalDuality (dualRepresentation)

variable {n : ℕ}

theorem ptHom_cocycle (ρ : Representation ℂ RationalGL3 (HomogeneousPoly n))
    (f : cochains N6 ρ 2) (hf : differentialTwo N6 ρ f = 0) :
    (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ ptHom ρ f = 0 :=
  modelHomOf_cocycle ρ (Equiv.refl PUnit) (fun _ _ => rfl) (restrictCocycle ρ PUnit ⟨f, hf⟩)

/-- The class in `H²(Γ(6); V)` of a global cocycle of the arithmetic level (coefficients `ρ`, restricted to `Γ(6)`). -/
def globalClass (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    (homCochains (prodComplex Γ6 RationalGL3 PUnit) (coeffRep (rationalCoefficientComponent n trivialCharacter))).homology 2 :=
  ptClassOf (ptHom (rationalCoefficientComponent n trivialCharacter)
      (restrictN6 (rationalCoefficientComponent n trivialCharacter) c.val))
    (ptHom_cocycle _ _ c.property)

/-- The class in `H²(Γ(6); V^*)` of the `φ`-twist of a global cocycle, with the coefficient `ℂ` paired into `ℚ` by `r`. -/
def dualGlobalClass (r : ℂ →ₗ[ℚ] ℚ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    (homCochains (prodComplex Γ6 RationalGL3 PUnit)
      (dualRepresentation (coeffRep (rationalCoefficientComponent n trivialCharacter)))).homology 2 :=
  ptClassOf (ptHom (twistRep (dualityData n trivialCharacter)) (twistGlobal (dualityData n trivialCharacter) c.val) ≫
      pairHom (dualityData n trivialCharacter) r)
    (by
      rw [← Category.assoc, ptHom_cocycle _ _ (twistGlobal_cocycle _ _ c.property), zero_comp])

/-- The defect of the model Stokes identity for two global classes with edge-exact restrictions: the line pairing of
`(r_Q c1, r_P c2)` minus the plane pairing of `(r_P c1, r_Q c2)`. -/
def stokesDefect (n : ℕ) (c1 c2 : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w1 w2 : EdgeCochains n trivialCharacter 1)
    (hw1 : ∀ x e, c1.val.val x = differentialOneRaw w1.val x e)
    (hw2 : ∀ x e, c2.val.val x = differentialOneRaw w2.val x e) : ℂ :=
  facePairing n
      ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (restrictionCocycle n trivialCharacter .line c1),
        innerBoundary_restriction_of_exact c1 w1 hw1 .line⟩
      ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (restrictionCocycle n trivialCharacter .plane c2),
        innerBoundary_restriction_of_exact c2 w2 hw2 .plane⟩ -
    Plane.facePairingP n
      ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (restrictionCocycle n trivialCharacter .plane c1),
        innerBoundary_restriction_of_exact c1 w1 hw1 .plane⟩
      ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (restrictionCocycle n trivialCharacter .line c2),
        innerBoundary_restriction_of_exact c2 w2 hw2 .line⟩

/-- The statement of `global_stokes_glue` for a constant `c`. -/
def GlobalStokes (c : ℂ) : Prop := ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ)
    (c1 c2 : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w1 w2 : EdgeCochains n trivialCharacter 1)
    (hw1 : ∀ x e, c1.val.val x = differentialOneRaw w1.val x e)
    (hw2 : ∀ x e, c2.val.val x = differentialOneRaw w2.val x e),
    r (c⁻¹ * stokesDefect n c1 c2 w1 w2 hw1 hw2) =
      geoPairingBoundary (coeffRep (rationalCoefficientComponent n trivialCharacter))
        (restrictedClass _ (dualGlobalClass r c2)) (restrictedClass _ (globalClass c1))

/-- The Lemma C.2 identity `GlobalStokes` for the constant `κ c₀` of any comparison data of `exists_pairGeo`. -/
theorem global_stokes_of_pairGeo {Ω : coneR.X 4} {Ψ : coneR ⟶ boundaryChains} {κ : ℚ} {c₀ : ℂ}
    (hcyc : IsCoinvCycle Ω) (hq : QuasiIso Ψ) (haug : Ψ ≫ augB = augR) (hκ : κ ≠ 0) (hc₀ : c₀ ≠ 0)
    (pairGeo : PairGeo Ψ Ω κ)
    (htr : ∀ f : closedEdgeCochains rationalLevel, levelTrace f = c₀ * evalOmega (cornerChain Ω) f.1) :
    GlobalStokes ((κ : ℂ) * c₀) := by
  have hκ' : (κ : ℂ) ≠ 0 := Rat.cast_ne_zero.2 hκ
  unfold GlobalStokes
  intro n r c1 c2 w1 w2 hw1 hw2
  have hex1 : ∃ γ, VertexPrimitive (dualityData n trivialCharacter)
      (restrictionCocycle n trivialCharacter .line c1) (restrictionCocycle n trivialCharacter .plane c2) γ :=
    exists_vertexPrimitive_line n _ _
  obtain ⟨γL, hγL⟩ := hex1
  have hex2 : ∃ γ, VertexPrimitiveP (dualityDataP n trivialCharacter)
      (restrictionCocycle n trivialCharacter .plane c1) (restrictionCocycle n trivialCharacter .line c2) γ :=
    exists_vertexPrimitive_plane n _ _
  obtain ⟨γP, hγP⟩ := hex2
  have hwQ : EdgePrimitive (restrictionCocycle n trivialCharacter .line c1) w1 := fun x e => hw1 x e
  have hwP : EdgePrimitiveP (restrictionCocycle n trivialCharacter .plane c1) w1 := fun x e => hw1 x e
  have hFQ : facePairing n
      ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (restrictionCocycle n trivialCharacter .line c1),
        innerBoundary_restriction_of_exact c1 w1 hw1 .line⟩
      ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (restrictionCocycle n trivialCharacter .plane c2),
        innerBoundary_restriction_of_exact c2 w2 hw2 .plane⟩ =
      c₀ * evalOmega (cornerChain Ω) (boundaryValue (dualityData n trivialCharacter) w1
        (restrictionCocycle n trivialCharacter .plane c2) γL) := by
    rw [facePairing_apply_eq (z := restrictionCocycle n trivialCharacter .line c1) (w := w1)
      (y := restrictionCocycle n trivialCharacter .plane c2) rfl hwQ rfl,
      ← trace_boundaryValue_eq_traceValue hγL]
    exact htr ⟨boundaryValue (dualityData n trivialCharacter) w1
      (restrictionCocycle n trivialCharacter .plane c2) γL, boundaryValue_mem_closed _ hwQ hγL⟩
  have hFP : Plane.facePairingP n
      ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (restrictionCocycle n trivialCharacter .plane c1),
        innerBoundary_restriction_of_exact c1 w1 hw1 .plane⟩
      ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (restrictionCocycle n trivialCharacter .line c2),
        innerBoundary_restriction_of_exact c2 w2 hw2 .line⟩ =
      c₀ * evalOmega (cornerChain Ω) (boundaryValueP (dualityDataP n trivialCharacter) w1
        (restrictionCocycle n trivialCharacter .line c2) γP) := by
    rw [Plane.facePairing_apply_eqP (z := restrictionCocycle n trivialCharacter .plane c1) (w := w1)
      (y := restrictionCocycle n trivialCharacter .line c2) rfl hwP rfl,
      ← Plane.trace_boundaryValue_eq_traceValueP hγP]
    exact htr ⟨boundaryValueP (dualityDataP n trivialCharacter) w1
      (restrictionCocycle n trivialCharacter .line c2) γP, boundaryValueP_mem_closed _ hwP hγP⟩
  -- the cone side
  have hB : coneR.d 3 2 ≫ globalB c1 = 0 := by
    unfold globalB
    rw [← Category.assoc, ← coneToPt.comm 3 2, Category.assoc,
      ptHom_cocycle _ _ (restrictN6_cocycle _ c1.val c1.property), comp_zero]
  have hA : coneR.d 3 2 ≫ globalA (dualityData n trivialCharacter) r c2 = 0 := by
    unfold globalA
    rw [← Category.assoc, ← coneToPt.comm 3 2, Category.assoc, ← Category.assoc
      ((prodComplex Γ6 RationalGL3 PUnit).d 3 2),
      ptHom_cocycle _ _ (twistGlobal_cocycle _ _ c2.property), zero_comp, comp_zero]
  have hex3 : ∃ (β : boundaryChains.X 2 ⟶ coeffRep (rationalCoefficientComponent n trivialCharacter))
      (_ : boundaryChains.d (2 + 1) 2 ≫ β = 0), PullsBackTo Ψ β (globalB c1) :=
    exists_pullsBackTo hq (globalB c1) hB
  obtain ⟨β, hβ, hPB⟩ := hex3
  have hex4 : ∃ (α : boundaryChains.X 2 ⟶ dualRepresentation (coeffRep (rationalCoefficientComponent n trivialCharacter)))
      (_ : boundaryChains.d (2 + 1) 2 ≫ α = 0),
      PullsBackTo Ψ α (globalA (dualityData n trivialCharacter) r c2) :=
    exists_pullsBackTo hq _ hA
  obtain ⟨α, hα, hPA⟩ := hex4
  have hpair := pairGeo (globalB c1) (globalA (dualityData n trivialCharacter) r c2) β hβ α hα hA hPB hPA
  have hglob := pair_global (dualityData n trivialCharacter) r Ω hcyc c1 c2 γL hγL.1 (fun x F => hγL.2 x F)
    γP hγP.1 (fun x F => hγP.2 x F)
  obtain ⟨η, hη⟩ := hPB
  obtain ⟨η', hη'⟩ := hPA
  have hβcls := cochainClass_eq_restrictedClass hq haug
    (ptHom (rationalCoefficientComponent n trivialCharacter)
      (restrictN6 (rationalCoefficientComponent n trivialCharacter) c1.val))
    (ptHom_cocycle _ _ (restrictN6_cocycle _ c1.val c1.property)) β hβ η hη
  have hαcls := cochainClass_eq_restrictedClass hq haug
    (ptHom (twistRep (dualityData n trivialCharacter)) (twistGlobal (dualityData n trivialCharacter) c2.val) ≫
      pairHom (dualityData n trivialCharacter) r)
    (by rw [← Category.assoc, ptHom_cocycle _ _ (twistGlobal_cocycle _ _ c2.property), zero_comp])
    α hα η' hη'
  have hgeo : geoOf (coeffRep (rationalCoefficientComponent n trivialCharacter)) α hα β hβ =
      geoPairingBoundary (coeffRep (rationalCoefficientComponent n trivialCharacter))
        (restrictedClass _ (dualGlobalClass r c2)) (restrictedClass _ (globalClass c1)) := by
    unfold geoOf
    rw [hβcls, hαcls]
    rfl
  refine Eq.trans ?_ hgeo
  have hdef : stokesDefect n c1 c2 w1 w2 hw1 hw2 = c₀ * evalOmega (cornerChain Ω) (boundaryValue (dualityData n trivialCharacter) w1
        (restrictionCocycle n trivialCharacter .plane c2) γL) -
       c₀ * evalOmega (cornerChain Ω) (boundaryValueP (dualityDataP n trivialCharacter) w1
        (restrictionCocycle n trivialCharacter .line c2) γP) := by
    exact congrArg₂ (· - ·) hFQ hFP
  rw [hdef]
  have hdiff : evalOmega (cornerChain Ω) (boundaryValue (dualityData n trivialCharacter) w1
        (restrictionCocycle n trivialCharacter .plane c2) γL) -
      evalOmega (cornerChain Ω) (boundaryValueP (dualityDataP n trivialCharacter) w1
        (restrictionCocycle n trivialCharacter .line c2) γP) =
      evalOmega (cornerChain Ω) (fun x e => γP x (endpoint .plane e) - γL x (endpoint .line e)) := by
    rw [← map_sub]
    exact congrArg _ (boundaryValue_sub_boundaryValueP w1 c2 γL γP)
  have hE : r (evalOmega (cornerChain Ω) (fun x e => γP x (endpoint .plane e) - γL x (endpoint .line e))) =
      κ * geoOf (coeffRep (rationalCoefficientComponent n trivialCharacter)) α hα β hβ :=
    hglob.symm.trans hpair
  have e1 : ((κ : ℂ) * c₀)⁻¹ *
      (c₀ * evalOmega (cornerChain Ω) (boundaryValue (dualityData n trivialCharacter) w1
        (restrictionCocycle n trivialCharacter .plane c2) γL) -
       c₀ * evalOmega (cornerChain Ω) (boundaryValueP (dualityDataP n trivialCharacter) w1
        (restrictionCocycle n trivialCharacter .line c2) γP)) =
      ((κ⁻¹ : ℚ) : ℂ) * evalOmega (cornerChain Ω) (fun x e => γP x (endpoint .plane e) - γL x (endpoint .line e)) := by
    rw [← mul_sub, hdiff]
    push_cast
    field_simp
  rw [e1, ← Rat.smul_def, map_smul, hE, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul]

/-- **Lemma C.2 in the model, with the geometric pairing.** -/
theorem global_stokes_glue : ∃ c : ℂ, c ≠ 0 ∧ GlobalStokes c := by
  obtain ⟨Ω, Ψ, κ, c₀, hcyc, -, hq, haug, hκ, hc₀, pairGeo, htr⟩ := exists_pairGeo
  exact ⟨(κ : ℂ) * c₀, mul_ne_zero (Rat.cast_ne_zero.2 hκ) hc₀,
    global_stokes_of_pairGeo hcyc hq haug hκ hc₀ pairGeo htr⟩

/-- **Geometric Stokes for restriction classes**: the Poincaré-duality pairing of the boundary pairs the singular
restrictions `j^*` of two classes of `H²(Γ(6); ·)` to zero (the library's `geoPairingBoundary_restriction`). -/
theorem geoPairing_restrictedClass_zero (V : Rep.{0} ℚ principalSix)
    (x' : (homCochains (prodComplex Γ6 RationalGL3 PUnit) (dualRepresentation V)).homology 2)
    (x : (homCochains (prodComplex Γ6 RationalGL3 PUnit) V).homology 2) :
    geoPairingBoundary V (restrictedClass _ x') (restrictedClass _ x) = 0 :=
  geoPairingBoundary_restriction V _ _

/-- **Lemma C.2 in the model, geometric form**: the model Stokes defect vanishes for the restrictions of two global
classes; the geometric Stokes theorem of the boundary gives the vanishing of the right-hand side of `global_stokes_glue`. -/
theorem global_stokes_geometric : ∃ c : ℂ, c ≠ 0 ∧ ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ)
    (c1 c2 : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w1 w2 : EdgeCochains n trivialCharacter 1)
    (hw1 : ∀ x e, c1.val.val x = differentialOneRaw w1.val x e)
    (hw2 : ∀ x e, c2.val.val x = differentialOneRaw w2.val x e),
    r (c⁻¹ * stokesDefect n c1 c2 w1 w2 hw1 hw2) = 0 := by
  obtain ⟨c, hc, H⟩ := global_stokes_glue
  refine ⟨c, hc, fun n r c1 c2 w1 w2 hw1 hw2 => ?_⟩
  exact (H n r c1 c2 w1 w2 hw1 hw2).trans (geoPairing_restrictedClass_zero _ _ _)

/-- **The model Stokes identity, from the geometric one**: `⟨r_P c1, r_Q c2⟩_P = ⟨r_Q c1, r_P c2⟩_Q` for global classes with
edge-exact restrictions (the paper's Lemma C.2 in the conventions of the model), re-proved here from the geometric
Stokes theorem of the boundary and the comparison of the model pairings with the geometric one. -/
theorem stokesDefect_eq_zero (n : ℕ)
    (c1 c2 : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w1 w2 : EdgeCochains n trivialCharacter 1)
    (hw1 : ∀ x e, c1.val.val x = differentialOneRaw w1.val x e)
    (hw2 : ∀ x e, c2.val.val x = differentialOneRaw w2.val x e) :
    stokesDefect n c1 c2 w1 w2 hw1 hw2 = 0 := by
  obtain ⟨c, hc, H⟩ := global_stokes_geometric
  have h : c⁻¹ * stokesDefect n c1 c2 w1 w2 hw1 hw2 = 0 :=
    (Module.forall_dual_apply_eq_zero_iff ℚ (c⁻¹ * stokesDefect n c1 c2 w1 w2 hw1 hw2)).1
      (fun r => H n r c1 c2 w1 w2 hw1 hw2)
  exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero hc)

end Final

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
