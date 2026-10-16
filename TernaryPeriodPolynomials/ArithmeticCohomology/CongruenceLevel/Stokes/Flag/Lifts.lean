module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.CoordNat
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Pairs
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.PointLevel

@[expose] public section


/-!
# Mixed classes at an orbit of lines or planes: the flag coordinates of the cut class vanish

Formalized by Claude Sonnet 5.5.

For an equivariant map `α` from the complete flags to a label set `Z` (lines or planes), a class at the orbit `o` of `Z` is *mixed* if its restriction to the stabilizer of every
flag over the representative `o.out` vanishes (`MixedModel`).  Cutting a class of the resolution of `Z` to the orbit, its pullback to the flags has vanishing Shapiro coordinates
exactly when the class is mixed (`flag_coord_vanish`): at a flag over another orbit by the vanishing of the cut, over the orbit by the conjugation formula of `CoordNat`.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.EquivariantSingularSmall

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section Mixed

variable {W : Rep.{0} ℚ Γ6}

theorem iso_inv_eq_zero {X Y : ModuleCat.{0} ℚ} (e : X ≅ Y) (t : Y) (h : e.inv.hom t = 0) : t = 0 := by
  have h' : e.hom.hom (e.inv.hom t) = t := congrArg (fun m => m.hom t) e.inv_hom_id
  rw [← h', h, map_zero]

/-- The vanishing of the Mathlib restriction transports to the bar homology. -/
theorem barChainMap_inclusion_zero (S S' : Subgroup Γ6) (h : S' ≤ S)
    (x : groupCohomology (Rep.res S.subtype W) 2)
    (hx : (groupCohomology.map (Subgroup.inclusion h) (𝟙 (Rep.res S'.subtype W)) 2).hom x = 0) :
    (HomologicalComplex.homologyMap
      (barChainMap (Subgroup.inclusion h) (𝟙 (Rep.res (Subgroup.inclusion h) (Rep.res S.subtype W)))) 2).hom
      ((gisoBar (Rep.res S.subtype W) 2).hom x) = 0 := by
  have h1 := barChainMap_homology (Subgroup.inclusion h) (𝟙 (Rep.res (Subgroup.inclusion h) (Rep.res S.subtype W))) 2
  have h2 := congrArg (fun m => m.hom ((gisoBar (Rep.res S.subtype W) 2).hom x)) h1
  have h3 : (gisoBar (Rep.res S.subtype W) 2).inv.hom ((gisoBar (Rep.res S.subtype W) 2).hom x) = x :=
    congrArg (fun m => m.hom x) (gisoBar (Rep.res S.subtype W) 2).hom_inv_id
  apply iso_inv_eq_zero (gisoBar (Rep.res (Subgroup.inclusion h) (Rep.res S.subtype W)) 2)
  refine Eq.trans h2 ?_
  change (groupCohomology.map (Subgroup.inclusion h) (𝟙 (Rep.res (Subgroup.inclusion h) (Rep.res S.subtype W))) 2).hom
    ((gisoBar (Rep.res S.subtype W) 2).inv.hom ((gisoBar (Rep.res S.subtype W) 2).hom x)) = 0
  rw [h3]
  exact hx


end Mixed

section Generic

variable {W : Rep.{0} ℚ Γ6}
variable {Z : Type} [MulAction Γ6 Z] (α : Flag → Z) (hα : ∀ (γ : Γ6) (F : Flag), α (γ • F) = γ • α F)

include hα

theorem stab_flag_le_stab_pt (F : Flag) :
    MulAction.stabilizer Γ6 F ≤ MulAction.stabilizer Γ6 (α F) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← hα, MulAction.mem_stabilizer_iff.1 hg]

theorem hzF (F : Flag) : ∀ g : MulAction.stabilizer Γ6 F, g • α F = α F :=
  fun g => MulAction.mem_stabilizer_iff.1 (stab_flag_le_stab_pt α hα F g.2)

/-- A class at the orbit `o` is *mixed* if its restriction to the stabilizer of every complete flag over the representative of `o` vanishes. -/
def MixedModel (o : labelOrbits Γ6 Z)
    (x : groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype W) 2) : Prop :=
  ∀ (F : Flag) (hF : α F = o.out),
    (groupCohomology.map (Subgroup.inclusion (by
        have := stab_flag_le_stab_pt α hα F
        rw [hF] at this
        exact this : MulAction.stabilizer Γ6 F ≤ stabilizer Γ6 o.out))
      (𝟙 (Rep.res (MulAction.stabilizer Γ6 F).subtype W)) 2).hom x = 0

/-- Conjugating by `γ` maps the stabilizer of the flag `F` into the stabilizer of `γ⁻¹ F`. -/
def stabConj (γ : Γ6) (F : Flag) : ↥(MulAction.stabilizer Γ6 F) →* ↥(MulAction.stabilizer Γ6 (γ⁻¹ • F)) where
  toFun s := ⟨γ⁻¹ * s * γ, by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, smul_inv_smul, MulAction.mem_stabilizer_iff.1 s.2]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change γ⁻¹ * ((a : Γ6) * (b : Γ6)) * γ = γ⁻¹ * (a : Γ6) * γ * (γ⁻¹ * (b : Γ6) * γ)
    group)

/-- **The coordinates of the flag pullback of a cut class vanish if the class is mixed.** -/
theorem flag_coord_vanish (o : labelOrbits Γ6 Z) (Y0 : (homCochains (prodComplex Γ6 RationalGL3 Z) W).homology 2)
    (hmix : MixedModel α hα o
      ((faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom Y0))
    (F : Flag) :
    (HomologicalComplex.homologyMap (stabCoord (MulAction.stabilizer Γ6 F) W (1 : RationalGL3) (α F) (hzF α hα F)) 2).hom
      ((HomologicalComplex.homologyMap (homPullback (cutChain Γ6 RationalGL3 Z (labelOrbit Γ6 Z o)
        (labelOrbit_invariant o)) W) 2).hom Y0) = 0 := by
  classical
  by_cases hℓ : α F ∈ labelOrbit Γ6 Z o
  swap
  · have := congrArg (fun m => m.hom Y0) (HomologicalComplex.homologyMap_comp
      (homPullback (cutChain Γ6 RationalGL3 Z (labelOrbit Γ6 Z o) (labelOrbit_invariant o)) W)
      (stabCoord (MulAction.stabilizer Γ6 F) W (1 : RationalGL3) (α F) (hzF α hα F)) 2)
    rw [stabCoord_cut_chain_not_mem (labelOrbit Γ6 Z o) (labelOrbit_invariant o)
      (MulAction.stabilizer Γ6 F) W (1 : RationalGL3) (α F) (hzF α hα F) hℓ] at this
    simpa using this.symm
  · have hc := congrArg (fun m => m.hom Y0) (HomologicalComplex.homologyMap_comp
      (homPullback (cutChain Γ6 RationalGL3 Z (labelOrbit Γ6 Z o) (labelOrbit_invariant o)) W)
      (stabCoord (MulAction.stabilizer Γ6 F) W (1 : RationalGL3) (α F) (hzF α hα F)) 2)
    rw [stabCoord_cut_chain_mem (labelOrbit Γ6 Z o) (labelOrbit_invariant o)
      (MulAction.stabilizer Γ6 F) W (1 : RationalGL3) (α F) (hzF α hα F) hℓ] at hc
    -- `hc : H(stabCoord) Y0 = H(stabCoord) (H(cut) Y0)`
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.1 hℓ
    have key : ∀ (p : Z) (hp : γ • o.out = p) (hz : ∀ g : MulAction.stabilizer Γ6 F, g • p = p),
        (HomologicalComplex.homologyMap
          (stabCoord (MulAction.stabilizer Γ6 F) W (1 : RationalGL3) p hz) 2).hom Y0 = 0 := by
      intro p hp hz
      subst hp
      have hF1 : α (γ⁻¹ • F) = o.out := by
        rw [hα, ← hγ, inv_smul_smul]
      have hle : MulAction.stabilizer Γ6 (γ⁻¹ • F) ≤ MulAction.stabilizer Γ6 o.out := by
        have := stab_flag_le_stab_pt α hα (γ⁻¹ • F)
        rw [hF1] at this
        exact this
      have hS₁ : ∀ g : MulAction.stabilizer Γ6 (γ⁻¹ • F), g • o.out = o.out :=
        fun g => MulAction.mem_stabilizer_iff.1 (hle g.2)
      have hz₀ : ∀ g : MulAction.stabilizer Γ6 o.out, g • o.out = o.out := fun g => g.2
      have hmx := barChainMap_inclusion_zero (W := W) (MulAction.stabilizer Γ6 o.out)
        (MulAction.stabilizer Γ6 (γ⁻¹ • F)) hle
        ((faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom Y0)
        (hmix (γ⁻¹ • F) hF1)
      have hcoord : (HomologicalComplex.homologyMap (stabCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out
          (fun g => g.2)) 2).hom Y0 =
          (gisoBar (Rep.res (stabilizer Γ6 o.out).subtype W) 2).hom
            ((faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom Y0) := by
        have e := congrArg (fun m => m.hom Y0)
          (faceCoord_eq_homologyMap_stabCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out
            (fun g => g.2) 2)
        have e2 : (faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom Y0 =
            (gisoBar (Rep.res (stabilizer Γ6 o.out).subtype W) 2).inv.hom
              ((HomologicalComplex.homologyMap (stabCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out
                (fun g => g.2)) 2).hom Y0) := e
        rw [e2]
        exact (congrArg (fun m => m.hom ((HomologicalComplex.homologyMap (stabCoord (stabilizer Γ6 o.out) W
          (1 : RationalGL3) o.out (fun g => g.2)) 2).hom Y0))
          (gisoBar (Rep.res (stabilizer Γ6 o.out).subtype W) 2).inv_hom_id).symm
      have hz1 : (HomologicalComplex.homologyMap (stabCoord (MulAction.stabilizer Γ6 (γ⁻¹ • F)) W
          (1 : RationalGL3) o.out hS₁) 2).hom Y0 = 0 := by
        rw [stabCoord_sub (MulAction.stabilizer Γ6 o.out) (MulAction.stabilizer Γ6 (γ⁻¹ • F)) hle W
          (1 : RationalGL3) o.out hz₀ hS₁]
        erw [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hcoord]
        exact hmx
      rw [homologyMap_stabCoord_conj W (1 : RationalGL3) o.out γ (MulAction.stabilizer Γ6 (γ⁻¹ • F))
        (MulAction.stabilizer Γ6 F) hS₁ hz (stabConj γ F) (fun s => rfl) vertexAction_free' 2,
        ModuleCat.hom_comp, LinearMap.comp_apply, hz1, map_zero]
    exact hc.symm.trans (key (α F) hγ (hzF α hα F))



end Generic

section Lifts

variable {W : Rep.{0} ℚ Γ6}

/-- **Lifts exist for every mixed class**: a class at the orbit `o` of lines whose restrictions to the stabilizers of the flags over `o.out` vanish
is the coordinate at `o` of a line datum supported on `o`. -/
theorem LineMixedModel_liftable (o : labelOrbits Γ6 Line)
    (x : groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype W) 2) (hx : MixedModel flagLineOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant o x) :
    ∃ d : LineDatum W, d.IsOn (labelOrbit Γ6 Line o) ∧ d.coord o = x := by
  classical
  -- a class of the line resolution with the given coordinate at `o` and zero elsewhere
  obtain ⟨Z, hZ⟩ := (faceCoord_product_bijective (Γ := Γ6) (V := RationalGL3) (Z := Line) (1 : RationalGL3)
    vertexAction_free' W).2 (Function.update (0 : ∀ o' : labelOrbits Γ6 Line,
      groupCohomology (Rep.res (stabilizer Γ6 o'.out).subtype W) 2) o x)
  obtain ⟨z, hz, rfl⟩ := exists_cls2 (LineCochains W) Z
  have hco : (faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom
      (cls2 (LineCochains W) z hz) = x := by
    have := congrFun hZ o
    simpa using this
  have hmix : MixedModel flagLineOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant o ((faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom
      (cls2 (LineCochains W) z hz)) := by
    rw [hco]; exact hx
  -- the cut class
  set S := labelOrbit Γ6 Line o with hS
  have hSinv := labelOrbit_invariant (Γ := Γ6) (Z := Line) o
  have hzc : ((LineCochains W).d 2 3).hom (cutHom Γ6 RationalGL3 Line S hSinv 2 ≫ z) = 0 := by
    change (prodComplex Γ6 RationalGL3 Line).d 3 2 ≫ cutHom Γ6 RationalGL3 Line S hSinv 2 ≫ z = 0
    erw [← Category.assoc, cutHom_comm_d, Category.assoc]
    have : (prodComplex Γ6 RationalGL3 Line).d 3 2 ≫ z = 0 := hz
    erw [this, comp_zero]
  have hcls : cls2 (LineCochains W) (cutHom Γ6 RationalGL3 Line S hSinv 2 ≫ z) hzc =
      (HomologicalComplex.homologyMap (homPullback (cutChain Γ6 RationalGL3 Line S hSinv) W) 2).hom
        (cls2 (LineCochains W) z hz) := by
    have e := cls2_map (LineCochains W) (homPullback (cutChain Γ6 RationalGL3 Line S hSinv) W) z hz
      (map_cocycle _ _ _ hz)
    rw [e]
    rfl
  -- the flag pullback of the cut class vanishes
  have hflag : (HomologicalComplex.homologyMap (homPullback flagLineHom.hom W) 2).hom
      (cls2 (LineCochains W) (cutHom Γ6 RationalGL3 Line S hSinv 2 ≫ z) hzc) = 0 := by
    rw [hcls]
    have hinj := (faceCoord_product_bijective (Γ := Γ6) (V := RationalGL3) (Z := Flag) (1 : RationalGL3)
      vertexAction_free' W).1
    apply hinj
    funext oF
    change (faceCoord (stabilizer Γ6 oF.out) W (1 : RationalGL3) oF.out (fun g => g.2) 2).hom _ =
      (faceCoord (stabilizer Γ6 oF.out) W (1 : RationalGL3) oF.out (fun g => g.2) 2).hom 0
    rw [map_zero]
    have hpb := stabCoord_pullback (Γ := Γ6) (V := RationalGL3) (Z := Flag) (Z' := Line) flagLineOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant (MulAction.stabilizer Γ6 oF.out) W
      (1 : RationalGL3) oF.out (fun g => g.2) (hzF flagLineOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant oF.out)
    set Q0 := (HomologicalComplex.homologyMap (homPullback (cutChain Γ6 RationalGL3 Line S hSinv) W) 2).hom
      (cls2 (LineCochains W) z hz) with hQ0
    have h1 : (HomologicalComplex.homologyMap (stabCoord (MulAction.stabilizer Γ6 oF.out) W (1 : RationalGL3) oF.out
          (fun g => g.2)) 2).hom
        ((HomologicalComplex.homologyMap (homPullback flagLineHom.hom W) 2).hom Q0) =
        (HomologicalComplex.homologyMap (stabCoord (MulAction.stabilizer Γ6 oF.out) W (1 : RationalGL3) (flagLineOf oF.out)
          (hzF flagLineOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant oF.out)) 2).hom Q0 := by
      have := congrArg (fun m => ModuleCat.Hom.hom (HomologicalComplex.homologyMap m 2) Q0) hpb
      erw [HomologicalComplex.homologyMap_comp] at this
      exact this
    have h2 := flag_coord_vanish (W := W) flagLineOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant o (cls2 (LineCochains W) z hz) hmix oF.out
    have h3 : (HomologicalComplex.homologyMap (stabCoord (MulAction.stabilizer Γ6 oF.out) W (1 : RationalGL3) oF.out
          (fun g => g.2)) 2).hom
        ((HomologicalComplex.homologyMap (homPullback flagLineHom.hom W) 2).hom Q0) = 0 := h1.trans h2
    have e := congrArg (fun m => m.hom ((HomologicalComplex.homologyMap (homPullback flagLineHom.hom W) 2).hom Q0))
      (faceCoord_eq_homologyMap_stabCoord (stabilizer Γ6 oF.out) W (1 : RationalGL3) oF.out (fun g => g.2) 2)
    refine e.trans ?_
    change (gisoBar (Rep.res (stabilizer Γ6 oF.out).subtype W) 2).inv.hom
      ((HomologicalComplex.homologyMap (stabCoord (MulAction.stabilizer Γ6 oF.out) W (1 : RationalGL3) oF.out
          (fun g => g.2)) 2).hom
        ((HomologicalComplex.homologyMap (homPullback flagLineHom.hom W) 2).hom Q0)) = 0
    rw [h3, map_zero]
  -- the flag primitive
  have hzc' : (prodComplex Γ6 RationalGL3 Line).d 3 2 ≫ (cutHom Γ6 RationalGL3 Line S hSinv 2 ≫ z) = 0 := hzc
  have hprim : cls2 (homCochains (prodComplex Γ6 RationalGL3 Flag) W)
      (flagLineHom.hom.f 2 ≫ (cutHom Γ6 RationalGL3 Line S hSinv 2 ≫ z))
      (map_cocycle (LineCochains W) (homPullback flagLineHom.hom W) _ hzc) = 0 := by
    have e := cls2_map (LineCochains W) (homPullback flagLineHom.hom W)
      (cutHom Γ6 RationalGL3 Line S hSinv 2 ≫ z) hzc (map_cocycle _ _ _ hzc)
    exact e.symm.trans hflag
  obtain ⟨w, hw⟩ := (cls2_eq_zero_iff _ _ _).1 hprim
  let d0 : LineDatum W := ⟨cutHom Γ6 RationalGL3 Line S hSinv 2 ≫ z, hzc', w, hw⟩
  refine ⟨d0.cut S hSinv, LineDatum.cut_isOn S hSinv d0, ?_⟩
  have hc0 : (d0.cut S hSinv).coord o = d0.coord o := LineDatum.cut_coord o d0
  rw [hc0]
  have h4 : d0.coord o = (faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom
      ((HomologicalComplex.homologyMap (homPullback (cutChain Γ6 RationalGL3 Line S hSinv) W) 2).hom
        (cls2 (LineCochains W) z hz)) := by
    unfold LineDatum.coord LineDatum.cls
    rw [← hcls]
  rw [h4]
  have := congrArg (fun m => m.hom (cls2 (LineCochains W) z hz))
    (faceCoord_cut_mem S hSinv (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2)
      (out_mem_labelOrbit o) 2)
  exact this.trans hco


/-- **Lifts exist for every mixed class**: a class at the orbit `o` of lines whose restrictions to the stabilizers of the flags over `o.out` vanish
is the coordinate at `o` of a line datum supported on `o`. -/
theorem PlaneMixedModel_liftable (o : labelOrbits Γ6 Plane)
    (x : groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype W) 2) (hx : MixedModel flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant o x) :
    ∃ d : PlaneDatum W, d.IsOn (labelOrbit Γ6 Plane o) ∧ d.coord o = x := by
  classical
  -- a class of the line resolution with the given coordinate at `o` and zero elsewhere
  obtain ⟨Z, hZ⟩ := (faceCoord_product_bijective (Γ := Γ6) (V := RationalGL3) (Z := Plane) (1 : RationalGL3)
    vertexAction_free' W).2 (Function.update (0 : ∀ o' : labelOrbits Γ6 Plane,
      groupCohomology (Rep.res (stabilizer Γ6 o'.out).subtype W) 2) o x)
  obtain ⟨z, hz, rfl⟩ := exists_cls2 (PlaneCochains W) Z
  have hco : (faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom
      (cls2 (PlaneCochains W) z hz) = x := by
    have := congrFun hZ o
    simpa using this
  have hmix : MixedModel flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant o ((faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom
      (cls2 (PlaneCochains W) z hz)) := by
    rw [hco]; exact hx
  -- the cut class
  set S := labelOrbit Γ6 Plane o with hS
  have hSinv := labelOrbit_invariant (Γ := Γ6) (Z := Plane) o
  have hzc : ((PlaneCochains W).d 2 3).hom (cutHom Γ6 RationalGL3 Plane S hSinv 2 ≫ z) = 0 := by
    change (prodComplex Γ6 RationalGL3 Plane).d 3 2 ≫ cutHom Γ6 RationalGL3 Plane S hSinv 2 ≫ z = 0
    erw [← Category.assoc, cutHom_comm_d, Category.assoc]
    have : (prodComplex Γ6 RationalGL3 Plane).d 3 2 ≫ z = 0 := hz
    erw [this, comp_zero]
  have hcls : cls2 (PlaneCochains W) (cutHom Γ6 RationalGL3 Plane S hSinv 2 ≫ z) hzc =
      (HomologicalComplex.homologyMap (homPullback (cutChain Γ6 RationalGL3 Plane S hSinv) W) 2).hom
        (cls2 (PlaneCochains W) z hz) := by
    have e := cls2_map (PlaneCochains W) (homPullback (cutChain Γ6 RationalGL3 Plane S hSinv) W) z hz
      (map_cocycle _ _ _ hz)
    rw [e]
    rfl
  -- the flag pullback of the cut class vanishes
  have hflag : (HomologicalComplex.homologyMap (homPullback flagPlaneHom.hom W) 2).hom
      (cls2 (PlaneCochains W) (cutHom Γ6 RationalGL3 Plane S hSinv 2 ≫ z) hzc) = 0 := by
    rw [hcls]
    have hinj := (faceCoord_product_bijective (Γ := Γ6) (V := RationalGL3) (Z := Flag) (1 : RationalGL3)
      vertexAction_free' W).1
    apply hinj
    funext oF
    change (faceCoord (stabilizer Γ6 oF.out) W (1 : RationalGL3) oF.out (fun g => g.2) 2).hom _ =
      (faceCoord (stabilizer Γ6 oF.out) W (1 : RationalGL3) oF.out (fun g => g.2) 2).hom 0
    rw [map_zero]
    have hpb := stabCoord_pullback (Γ := Γ6) (V := RationalGL3) (Z := Flag) (Z' := Plane) flagPlaneOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant (MulAction.stabilizer Γ6 oF.out) W
      (1 : RationalGL3) oF.out (fun g => g.2) (hzF flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant oF.out)
    set Q0 := (HomologicalComplex.homologyMap (homPullback (cutChain Γ6 RationalGL3 Plane S hSinv) W) 2).hom
      (cls2 (PlaneCochains W) z hz) with hQ0
    have h1 : (HomologicalComplex.homologyMap (stabCoord (MulAction.stabilizer Γ6 oF.out) W (1 : RationalGL3) oF.out
          (fun g => g.2)) 2).hom
        ((HomologicalComplex.homologyMap (homPullback flagPlaneHom.hom W) 2).hom Q0) =
        (HomologicalComplex.homologyMap (stabCoord (MulAction.stabilizer Γ6 oF.out) W (1 : RationalGL3) (flagPlaneOf oF.out)
          (hzF flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant oF.out)) 2).hom Q0 := by
      have := congrArg (fun m => ModuleCat.Hom.hom (HomologicalComplex.homologyMap m 2) Q0) hpb
      erw [HomologicalComplex.homologyMap_comp] at this
      exact this
    have h2 := flag_coord_vanish (W := W) flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant o (cls2 (PlaneCochains W) z hz) hmix oF.out
    have h3 : (HomologicalComplex.homologyMap (stabCoord (MulAction.stabilizer Γ6 oF.out) W (1 : RationalGL3) oF.out
          (fun g => g.2)) 2).hom
        ((HomologicalComplex.homologyMap (homPullback flagPlaneHom.hom W) 2).hom Q0) = 0 := h1.trans h2
    have e := congrArg (fun m => m.hom ((HomologicalComplex.homologyMap (homPullback flagPlaneHom.hom W) 2).hom Q0))
      (faceCoord_eq_homologyMap_stabCoord (stabilizer Γ6 oF.out) W (1 : RationalGL3) oF.out (fun g => g.2) 2)
    refine e.trans ?_
    change (gisoBar (Rep.res (stabilizer Γ6 oF.out).subtype W) 2).inv.hom
      ((HomologicalComplex.homologyMap (stabCoord (MulAction.stabilizer Γ6 oF.out) W (1 : RationalGL3) oF.out
          (fun g => g.2)) 2).hom
        ((HomologicalComplex.homologyMap (homPullback flagPlaneHom.hom W) 2).hom Q0)) = 0
    rw [h3, map_zero]
  -- the flag primitive
  have hzc' : (prodComplex Γ6 RationalGL3 Plane).d 3 2 ≫ (cutHom Γ6 RationalGL3 Plane S hSinv 2 ≫ z) = 0 := hzc
  have hprim : cls2 (homCochains (prodComplex Γ6 RationalGL3 Flag) W)
      (flagPlaneHom.hom.f 2 ≫ (cutHom Γ6 RationalGL3 Plane S hSinv 2 ≫ z))
      (map_cocycle (PlaneCochains W) (homPullback flagPlaneHom.hom W) _ hzc) = 0 := by
    have e := cls2_map (PlaneCochains W) (homPullback flagPlaneHom.hom W)
      (cutHom Γ6 RationalGL3 Plane S hSinv 2 ≫ z) hzc (map_cocycle _ _ _ hzc)
    exact e.symm.trans hflag
  obtain ⟨w, hw⟩ := (cls2_eq_zero_iff _ _ _).1 hprim
  let d0 : PlaneDatum W := ⟨cutHom Γ6 RationalGL3 Plane S hSinv 2 ≫ z, hzc', w, hw⟩
  refine ⟨d0.cut S hSinv, PlaneDatum.cut_isOn S hSinv d0, ?_⟩
  have hc0 : (d0.cut S hSinv).coord o = d0.coord o := PlaneDatum.cut_coord o d0
  rw [hc0]
  have h4 : d0.coord o = (faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom
      ((HomologicalComplex.homologyMap (homPullback (cutChain Γ6 RationalGL3 Plane S hSinv) W) 2).hom
        (cls2 (PlaneCochains W) z hz)) := by
    unfold PlaneDatum.coord PlaneDatum.cls
    rw [← hcls]
  rw [h4]
  have := congrArg (fun m => m.hom (cls2 (PlaneCochains W) z hz))
    (faceCoord_cut_mem S hSinv (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2)
      (out_mem_labelOrbit o) 2)
  exact this.trans hco


end Lifts

end TernaryPeriodPolynomials.Argument.GammaNStokes
