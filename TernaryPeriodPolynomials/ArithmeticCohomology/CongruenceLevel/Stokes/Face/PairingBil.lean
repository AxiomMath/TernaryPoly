module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.PairingLifts
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.CoefNat

@[expose] public section


/-!
# The face pairings are `ℂ`-bilinear on the mixed classes

Formalized by Claude Sonnet 5.5.

On the mixed classes `lineMixedSub ρ i`, `lineMixedSub ρ.dual i` of a line face (and likewise for planes) the face pairing `lineFacePairM ρ i` is biadditive and `ℂ`-homogeneous in each
argument: lifts exist (`lineFace_exists_lifts`), lifts of a sum are the sums of lifts, lifts of a scalar multiple are the images of lifts under multiplication by the scalar
(`LineDatum.map`, `faceTauQ_smul`), and the cone pairing is additive and `ℂ`-homogeneous (`conePairC_mulC_left/right`).  Hence `lineFacePairBil ρ i` is an honest `ℂ`-bilinear map.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPoly.EquivariantSingularSmall
open GeneralEisenstein

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section DatumAdd

variable {W : Rep.{0} ℚ Γ6}

/-- The sum of two line data. -/
def LineDatum.add (d e : LineDatum W) : LineDatum W where
  z := d.z + e.z
  hz := by rw [Preadditive.comp_add, d.hz, e.hz, add_zero]
  w := d.w + e.w
  hw := by rw [Preadditive.comp_add, d.hw, e.hw, Preadditive.comp_add]

/-- The sum of two plane data. -/
def PlaneDatum.add (d e : PlaneDatum W) : PlaneDatum W where
  z := d.z + e.z
  hz := by rw [Preadditive.comp_add, d.hz, e.hz, add_zero]
  w := d.w + e.w
  hw := by rw [Preadditive.comp_add, d.hw, e.hw, Preadditive.comp_add]

theorem LineDatum.add_cone (d e : LineDatum W) : (d.add e).cone = d.cone + e.cone :=
  lineCone_add d.w e.w d.z e.z

theorem PlaneDatum.add_cone (d e : PlaneDatum W) : (d.add e).cone = d.cone + e.cone :=
  planeCone_add d.w e.w d.z e.z

theorem LineDatum.add_isOn (S : Set Line) (d e : LineDatum W) (hd : d.IsOn S) (he : e.IsOn S) : (d.add e).IsOn S :=
  ⟨fun u ℓ hℓ => by
    change d.z.hom (MonoidAlgebra.single (u, ℓ) 1) + e.z.hom (MonoidAlgebra.single (u, ℓ) 1) = 0
    rw [hd.1 u ℓ hℓ, he.1 u ℓ hℓ, add_zero],
   fun u F hF => by
    change d.w.hom (MonoidAlgebra.single (u, F) 1) + e.w.hom (MonoidAlgebra.single (u, F) 1) = 0
    rw [hd.2 u F hF, he.2 u F hF, add_zero]⟩

theorem PlaneDatum.add_isOn (S : Set Plane) (d e : PlaneDatum W) (hd : d.IsOn S) (he : e.IsOn S) : (d.add e).IsOn S :=
  ⟨fun u ℓ hℓ => by
    change d.z.hom (MonoidAlgebra.single (u, ℓ) 1) + e.z.hom (MonoidAlgebra.single (u, ℓ) 1) = 0
    rw [hd.1 u ℓ hℓ, he.1 u ℓ hℓ, add_zero],
   fun u F hF => by
    change d.w.hom (MonoidAlgebra.single (u, F) 1) + e.w.hom (MonoidAlgebra.single (u, F) 1) = 0
    rw [hd.2 u F hF, he.2 u F hF, add_zero]⟩

theorem LineDatum.add_coord (o : labelOrbits Γ6 Line) (d e : LineDatum W) :
    (d.add e).coord o = d.coord o + e.coord o := by
  unfold LineDatum.coord LineDatum.cls
  have hd : ((LineCochains W).d 2 3).hom d.z = 0 := d.hz
  have he : ((LineCochains W).d 2 3).hom e.z = 0 := e.hz
  rw [← map_add, ← cls2_add (LineCochains W) d.z e.z hd he (by erw [map_add, hd, he, add_zero])]
  rfl

theorem PlaneDatum.add_coord (o : labelOrbits Γ6 Plane) (d e : PlaneDatum W) :
    (d.add e).coord o = d.coord o + e.coord o := by
  unfold PlaneDatum.coord PlaneDatum.cls
  have hd : ((PlaneCochains W).d 2 3).hom d.z = 0 := d.hz
  have he : ((PlaneCochains W).d 2 3).hom e.z = 0 := e.hz
  rw [← map_add, ← cls2_add (PlaneCochains W) d.z e.z hd he (by erw [map_add, hd, he, add_zero])]
  rfl

end DatumAdd

section LineBil

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

/-- The Shapiro-transported class at the representative of the orbit, of a class of the line group (coefficients `E`). -/
abbrev lineTau (i : LineFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ))) :=
  faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
    (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
    (fun i => lineEmb_range i.rep) (rep6 ρ) i
    (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x)

/-- … for the dual coefficient module `E^*`. -/
abbrev lineTauD (i : LineFaces 6)
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual))) :=
  faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
    (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
    (fun i => lineEmb_range i.rep) (rep6 ρ).dual i
    (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) y)

variable (i : LineFaces 6)

theorem lineTau_add (x x' : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ))) :
    lineTau ρ i (x + x') = lineTau ρ i x + lineTau ρ i x' := by
  unfold lineTau
  exact (congrArg _ (map_add _ _ _)).trans (map_add _ _ _)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem lineTauD_add (y y' : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual))) :
    lineTauD ρ i (y + y') = lineTauD ρ i y + lineTauD ρ i y' := by
  unfold lineTauD
  exact (congrArg _ (map_add _ _ _)).trans (map_add _ _ _)

theorem lineTau_smul (c : ℂ) (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ))) :
    lineTau ρ i (c • x) = (groupCohomology.map (MonoidHom.id (stabilizer Γ6 (lineFacesEquivOrbits i).out))
      (Rep.resMap (stabilizer Γ6 (lineFacesEquivOrbits i).out).subtype (mulC (MonoidHom.id Γ6) (rep6 ρ) c)) 2).hom
        (lineTau ρ i x) := by
  unfold lineTau
  rw [map_smul]
  exact faceTauQ_smul _ _ _ _ _ _ _ (rep6 ρ) i c _

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem lineTauD_smul (c : ℂ) (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual))) :
    lineTauD ρ i (c • y) = (groupCohomology.map (MonoidHom.id (stabilizer Γ6 (lineFacesEquivOrbits i).out))
      (Rep.resMap (stabilizer Γ6 (lineFacesEquivOrbits i).out).subtype (mulC (MonoidHom.id Γ6) (rep6 ρ).dual c)) 2).hom
        (lineTauD ρ i y) := by
  unfold lineTauD
  rw [map_smul]
  exact faceTauQ_smul _ _ _ _ _ _ _ (rep6 ρ).dual i c _

theorem lineFacePairM_add_left (x x' : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hx : x ∈ lineMixedSub ρ i) (hx' : x' ∈ lineMixedSub ρ i) (hy : y ∈ lineMixedSub ρ.dual i) :
    lineFacePairM ρ i (x + x') y = lineFacePairM ρ i x y + lineFacePairM ρ i x' y := by
  obtain ⟨d, e, hd, he, hdc, hec⟩ := lineFace_exists_lifts ρ i x y hx hy
  obtain ⟨d', e', hd', he', hdc', hec'⟩ := lineFace_exists_lifts ρ i x' y hx' hy
  have h1 := lineFace_pair_eq_cone ρ i (x + x') y (d.add d') e (LineDatum.add_isOn _ d d' hd hd') he
    (by rw [LineDatum.add_coord, hdc, hdc']; exact (lineTau_add ρ i x x').symm) hec
  rw [h1, lineFace_pair_eq_cone ρ i x y d e hd he hdc hec, lineFace_pair_eq_cone ρ i x' y d' e hd' he hdc' hec,
    LineDatum.add_cone, conePairC_add_left]

theorem lineFacePairM_add_right (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y y' : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hx : x ∈ lineMixedSub ρ i) (hy : y ∈ lineMixedSub ρ.dual i) (hy' : y' ∈ lineMixedSub ρ.dual i) :
    lineFacePairM ρ i x (y + y') = lineFacePairM ρ i x y + lineFacePairM ρ i x y' := by
  obtain ⟨d, e, hd, he, hdc, hec⟩ := lineFace_exists_lifts ρ i x y hx hy
  obtain ⟨d', e', hd', he', hdc', hec'⟩ := lineFace_exists_lifts ρ i x y' hx hy'
  have h1 := lineFace_pair_eq_cone ρ i x (y + y') d (e.add e') hd (LineDatum.add_isOn _ e e' he he') hdc
    (by rw [LineDatum.add_coord, hec, hec']; exact (lineTauD_add ρ i y y').symm)
  rw [h1, lineFace_pair_eq_cone ρ i x y d e hd he hdc hec, lineFace_pair_eq_cone ρ i x y' d e' hd he' hdc hec',
    LineDatum.add_cone, conePairC_add_right]

theorem lineFacePairM_smul_left (c : ℂ) (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hx : x ∈ lineMixedSub ρ i) (hy : y ∈ lineMixedSub ρ.dual i) :
    lineFacePairM ρ i (c • x) y = c * lineFacePairM ρ i x y := by
  obtain ⟨d, e, hd, he, hdc, hec⟩ := lineFace_exists_lifts ρ i x y hx hy
  have h1 := lineFace_pair_eq_cone ρ i (c • x) y (d.map (mulC (MonoidHom.id Γ6) (rep6 ρ) c)) e
    (LineDatum.map_isOn _ _ d hd) he
    (by rw [LineDatum.map_coord, hdc]; exact (lineTau_smul ρ i c x).symm) hec
  rw [h1, lineFace_pair_eq_cone ρ i x y d e hd he hdc hec, LineDatum.map_cone, conePairC_mulC_left]

theorem lineFacePairM_smul_right (c : ℂ) (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hx : x ∈ lineMixedSub ρ i) (hy : y ∈ lineMixedSub ρ.dual i) :
    lineFacePairM ρ i x (c • y) = c * lineFacePairM ρ i x y := by
  obtain ⟨d, e, hd, he, hdc, hec⟩ := lineFace_exists_lifts ρ i x y hx hy
  have h1 := lineFace_pair_eq_cone ρ i x (c • y) d (e.map (mulC (MonoidHom.id Γ6) (rep6 ρ).dual c)) hd
    (LineDatum.map_isOn _ _ e he) hdc
    (by rw [LineDatum.map_coord, hec]; exact (lineTauD_smul ρ i c y).symm)
  rw [h1, lineFace_pair_eq_cone ρ i x y d e hd he hdc hec, LineDatum.map_cone, conePairC_mulC_right]

/-- **The face pairing of the line face `i` is a `ℂ`-bilinear map on the mixed classes.** -/
def lineFacePairBil : lineMixedSub ρ i →ₗ[ℂ] lineMixedSub ρ.dual i →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y => lineFacePairM ρ i x.1 y.1)
    (fun x x' y => lineFacePairM_add_left ρ i x.1 x'.1 y.1 x.2 x'.2 y.2)
    (fun c x y => lineFacePairM_smul_left ρ i c x.1 y.1 x.2 y.2)
    (fun x y y' => lineFacePairM_add_right ρ i x.1 y.1 y'.1 x.2 y.2 y'.2)
    (fun c x y => lineFacePairM_smul_right ρ i c x.1 y.1 x.2 y.2)

theorem lineFacePairBil_apply (x : lineMixedSub ρ i) (y : lineMixedSub ρ.dual i) :
    lineFacePairBil ρ i x y = lineFacePairM ρ i x.1 y.1 := rfl

end LineBil

section PlaneBil

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

/-- The Shapiro-transported class at the representative of the orbit, of a class of the plane group (coefficients `E`). -/
abbrev planeTau (i : PlaneFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ))) :=
  faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
    (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
    (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i
    (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x)

/-- … for the dual coefficient module `E^*`. -/
abbrev planeTauD (i : PlaneFaces 6)
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual))) :=
  faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
    (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
    (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i
    (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y)

variable (i : PlaneFaces 6)

theorem planeTau_add (x x' : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ))) :
    planeTau ρ i (x + x') = planeTau ρ i x + planeTau ρ i x' := by
  unfold planeTau
  exact (congrArg _ (map_add _ _ _)).trans (map_add _ _ _)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem planeTauD_add (y y' : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual))) :
    planeTauD ρ i (y + y') = planeTauD ρ i y + planeTauD ρ i y' := by
  unfold planeTauD
  exact (congrArg _ (map_add _ _ _)).trans (map_add _ _ _)

theorem planeTau_smul (c : ℂ) (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ))) :
    planeTau ρ i (c • x) = (groupCohomology.map (MonoidHom.id (stabilizer Γ6 (planeFacesEquivOrbits i).out))
      (Rep.resMap (stabilizer Γ6 (planeFacesEquivOrbits i).out).subtype (mulC (MonoidHom.id Γ6) (rep6 ρ) c)) 2).hom
        (planeTau ρ i x) := by
  unfold planeTau
  rw [map_smul]
  exact faceTauQ_smul _ _ _ _ _ _ _ (rep6 ρ) i c _

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem planeTauD_smul (c : ℂ) (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual))) :
    planeTauD ρ i (c • y) = (groupCohomology.map (MonoidHom.id (stabilizer Γ6 (planeFacesEquivOrbits i).out))
      (Rep.resMap (stabilizer Γ6 (planeFacesEquivOrbits i).out).subtype (mulC (MonoidHom.id Γ6) (rep6 ρ).dual c)) 2).hom
        (planeTauD ρ i y) := by
  unfold planeTauD
  rw [map_smul]
  exact faceTauQ_smul _ _ _ _ _ _ _ (rep6 ρ).dual i c _

theorem planeFacePairM_add_left (x x' : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (hx : x ∈ planeMixedSub ρ i) (hx' : x' ∈ planeMixedSub ρ i) (hy : y ∈ planeMixedSub ρ.dual i) :
    planeFacePairM ρ i (x + x') y = planeFacePairM ρ i x y + planeFacePairM ρ i x' y := by
  obtain ⟨d, e, hd, he, hdc, hec⟩ := planeFace_exists_lifts ρ i x y hx hy
  obtain ⟨d', e', hd', he', hdc', hec'⟩ := planeFace_exists_lifts ρ i x' y hx' hy
  have h1 := planeFace_pair_eq_cone ρ i (x + x') y (d.add d') e (PlaneDatum.add_isOn _ d d' hd hd') he
    (by rw [PlaneDatum.add_coord, hdc, hdc']; exact (planeTau_add ρ i x x').symm) hec
  rw [h1, planeFace_pair_eq_cone ρ i x y d e hd he hdc hec, planeFace_pair_eq_cone ρ i x' y d' e hd' he hdc' hec,
    PlaneDatum.add_cone, conePairC_add_left]

theorem planeFacePairM_add_right (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (y y' : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (hx : x ∈ planeMixedSub ρ i) (hy : y ∈ planeMixedSub ρ.dual i) (hy' : y' ∈ planeMixedSub ρ.dual i) :
    planeFacePairM ρ i x (y + y') = planeFacePairM ρ i x y + planeFacePairM ρ i x y' := by
  obtain ⟨d, e, hd, he, hdc, hec⟩ := planeFace_exists_lifts ρ i x y hx hy
  obtain ⟨d', e', hd', he', hdc', hec'⟩ := planeFace_exists_lifts ρ i x y' hx hy'
  have h1 := planeFace_pair_eq_cone ρ i x (y + y') d (e.add e') hd (PlaneDatum.add_isOn _ e e' he he') hdc
    (by rw [PlaneDatum.add_coord, hec, hec']; exact (planeTauD_add ρ i y y').symm)
  rw [h1, planeFace_pair_eq_cone ρ i x y d e hd he hdc hec, planeFace_pair_eq_cone ρ i x y' d e' hd he' hdc hec',
    PlaneDatum.add_cone, conePairC_add_right]

theorem planeFacePairM_smul_left (c : ℂ) (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (hx : x ∈ planeMixedSub ρ i) (hy : y ∈ planeMixedSub ρ.dual i) :
    planeFacePairM ρ i (c • x) y = c * planeFacePairM ρ i x y := by
  obtain ⟨d, e, hd, he, hdc, hec⟩ := planeFace_exists_lifts ρ i x y hx hy
  have h1 := planeFace_pair_eq_cone ρ i (c • x) y (d.map (mulC (MonoidHom.id Γ6) (rep6 ρ) c)) e
    (PlaneDatum.map_isOn _ _ d hd) he
    (by rw [PlaneDatum.map_coord, hdc]; exact (planeTau_smul ρ i c x).symm) hec
  rw [h1, planeFace_pair_eq_cone ρ i x y d e hd he hdc hec, PlaneDatum.map_cone, conePairC_mulC_left]

theorem planeFacePairM_smul_right (c : ℂ) (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (hx : x ∈ planeMixedSub ρ i) (hy : y ∈ planeMixedSub ρ.dual i) :
    planeFacePairM ρ i x (c • y) = c * planeFacePairM ρ i x y := by
  obtain ⟨d, e, hd, he, hdc, hec⟩ := planeFace_exists_lifts ρ i x y hx hy
  have h1 := planeFace_pair_eq_cone ρ i x (c • y) d (e.map (mulC (MonoidHom.id Γ6) (rep6 ρ).dual c)) hd
    (PlaneDatum.map_isOn _ _ e he) hdc
    (by rw [PlaneDatum.map_coord, hec]; exact (planeTauD_smul ρ i c y).symm)
  rw [h1, planeFace_pair_eq_cone ρ i x y d e hd he hdc hec, PlaneDatum.map_cone, conePairC_mulC_right]

/-- **The face pairing of the plane face `i` is a `ℂ`-bilinear map on the mixed classes.** -/
def planeFacePairBil : planeMixedSub ρ i →ₗ[ℂ] planeMixedSub ρ.dual i →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y => planeFacePairM ρ i x.1 y.1)
    (fun x x' y => planeFacePairM_add_left ρ i x.1 x'.1 y.1 x.2 x'.2 y.2)
    (fun c x y => planeFacePairM_smul_left ρ i c x.1 y.1 x.2 y.2)
    (fun x y y' => planeFacePairM_add_right ρ i x.1 y.1 y'.1 x.2 y.2 y'.2)
    (fun c x y => planeFacePairM_smul_right ρ i c x.1 y.1 x.2 y.2)

theorem planeFacePairBil_apply (x : planeMixedSub ρ i) (y : planeMixedSub ρ.dual i) :
    planeFacePairBil ρ i x y = planeFacePairM ρ i x.1 y.1 := rfl

end PlaneBil

end TernaryPeriodPolynomials.Argument.GammaNStokes

