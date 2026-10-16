module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrbitStokes
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.PointLevel

@[expose] public section


/-!
# The orbit pairings as functions of the Shapiro coordinates, and Stokes in coordinates

Formalized by Claude Sonnet 5.5.

For a rational representation `W` of `Γ(6)`, a pairing `π : W ⊗ W' ⟶ trivial ℂ` and a coinvariant cycle `v` of the model cone, `lineOrbitPair π v o x y` is the value of
the cone pairing of any two line data supported on the orbit `o` of lines with Shapiro coordinates `x`, `y` at `o` (and `0` if there are none); it is well defined by
`LineDatum.pairC_eq_of_coord_eq`.  `stokes_orbit_coordinates` is the Stokes relation for the coordinates of two classes of the point resolution whose restrictions to the
complete flags vanish.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.EquivariantSingularSmall

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section OrbitPair

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ Rep.trivial ℚ Γ6 ℂ) (v : coneR.X 4)

open Classical in
/-- The pairing at the orbit `o` of lines of two classes of the cohomology of the stabilizer of its representative. -/
def lineOrbitPair (o : labelOrbits Γ6 Line)
    (x : groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype W) 2)
    (y : groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype W') 2) : ℂ :=
  if h : ∃ (d : LineDatum W) (e : LineDatum W'), d.IsOn (labelOrbit Γ6 Line o) ∧ e.IsOn (labelOrbit Γ6 Line o) ∧
      d.coord o = x ∧ e.coord o = y then
    conePairC π v (Classical.choose h).cone (Classical.choose (Classical.choose_spec h)).cone
  else 0

open Classical in
/-- The pairing at the orbit `o` of planes. -/
def planeOrbitPair (o : labelOrbits Γ6 Plane)
    (x : groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype W) 2)
    (y : groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype W') 2) : ℂ :=
  if h : ∃ (d : PlaneDatum W) (e : PlaneDatum W'), d.IsOn (labelOrbit Γ6 Plane o) ∧ e.IsOn (labelOrbit Γ6 Plane o) ∧
      d.coord o = x ∧ e.coord o = y then
    conePairC π v (Classical.choose h).cone (Classical.choose (Classical.choose_spec h)).cone
  else 0

variable (hv : IsCoinvCycle v)

include hv in
theorem lineOrbitPair_eq (o : labelOrbits Γ6 Line) (d : LineDatum W) (e : LineDatum W')
    (hd : d.IsOn (labelOrbit Γ6 Line o)) (he : e.IsOn (labelOrbit Γ6 Line o)) :
    lineOrbitPair π v o (d.coord o) (e.coord o) = conePairC π v d.cone e.cone := by
  have h : ∃ (d' : LineDatum W) (e' : LineDatum W'), d'.IsOn (labelOrbit Γ6 Line o) ∧
      e'.IsOn (labelOrbit Γ6 Line o) ∧ d'.coord o = d.coord o ∧ e'.coord o = e.coord o :=
    ⟨d, e, hd, he, rfl, rfl⟩
  unfold lineOrbitPair
  rw [dite_eq_left h]
  obtain ⟨hd', he', hdc, hec⟩ := (Classical.choose_spec (Classical.choose_spec h))
  exact LineDatum.pairC_eq_of_coord_eq π v hv o _ _ _ _ hd' hd he' he hdc hec

include hv in
theorem planeOrbitPair_eq (o : labelOrbits Γ6 Plane) (d : PlaneDatum W) (e : PlaneDatum W')
    (hd : d.IsOn (labelOrbit Γ6 Plane o)) (he : e.IsOn (labelOrbit Γ6 Plane o)) :
    planeOrbitPair π v o (d.coord o) (e.coord o) = conePairC π v d.cone e.cone := by
  have h : ∃ (d' : PlaneDatum W) (e' : PlaneDatum W'), d'.IsOn (labelOrbit Γ6 Plane o) ∧
      e'.IsOn (labelOrbit Γ6 Plane o) ∧ d'.coord o = d.coord o ∧ e'.coord o = e.coord o :=
    ⟨d, e, hd, he, rfl, rfl⟩
  unfold planeOrbitPair
  rw [dite_eq_left h]
  obtain ⟨hd', he', hdc, hec⟩ := (Classical.choose_spec (Classical.choose_spec h))
  exact PlaneDatum.pairC_eq_of_coord_eq π v hv o _ _ _ _ hd' hd he' he hdc hec

end OrbitPair


section Coordinates

variable {W : Rep.{0} ℚ Γ6}

open Classical in
theorem LineDatum.cls_cut_eq (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S) (d : LineDatum W) :
    (d.cut S hS).cls =
      (HomologicalComplex.homologyMap (homPullback (cutChain Γ6 RationalGL3 Line S hS) W) 2).hom d.cls := by
  have hc : ((LineCochains W).d 2 3).hom d.z = 0 := d.hz
  have e := cls2_map (LineCochains W) (homPullback (cutChain Γ6 RationalGL3 Line S hS) W) d.z hc
    (map_cocycle _ _ _ hc)
  unfold LineDatum.cls
  rw [e]
  rfl

open Classical in
theorem PlaneDatum.cls_cut_eq (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S) (d : PlaneDatum W) :
    (d.cut S hS).cls =
      (HomologicalComplex.homologyMap (homPullback (cutChain Γ6 RationalGL3 Plane S hS) W) 2).hom d.cls := by
  have hc : ((PlaneCochains W).d 2 3).hom d.z = 0 := d.hz
  have e := cls2_map (PlaneCochains W) (homPullback (cutChain Γ6 RationalGL3 Plane S hS) W) d.z hc
    (map_cocycle _ _ _ hc)
  unfold PlaneDatum.cls
  rw [e]
  rfl

theorem out_mem_labelOrbit {Z : Type} [MulAction Γ6 Z] (o : labelOrbits Γ6 Z) : o.out ∈ labelOrbit Γ6 Z o :=
  MulAction.mem_orbit_self _

/-- The cut of a line datum to an orbit has the same coordinate at that orbit. -/
theorem LineDatum.cut_coord (o : labelOrbits Γ6 Line) (d : LineDatum W) :
    ((d.cut (labelOrbit Γ6 Line o) (labelOrbit_invariant o))).coord o = d.coord o := by
  classical
  unfold LineDatum.coord
  rw [LineDatum.cls_cut_eq]
  have := congrArg (fun m => m.hom d.cls)
    (faceCoord_cut_mem (labelOrbit Γ6 Line o) (labelOrbit_invariant o) (stabilizer Γ6 o.out) W
      (1 : RationalGL3) o.out (fun g => g.2) (out_mem_labelOrbit o) 2)
  exact this

theorem PlaneDatum.cut_coord (o : labelOrbits Γ6 Plane) (d : PlaneDatum W) :
    ((d.cut (labelOrbit Γ6 Plane o) (labelOrbit_invariant o))).coord o = d.coord o := by
  classical
  unfold PlaneDatum.coord
  rw [PlaneDatum.cls_cut_eq]
  have := congrArg (fun m => m.hom d.cls)
    (faceCoord_cut_mem (labelOrbit Γ6 Plane o) (labelOrbit_invariant o) (stabilizer Γ6 o.out) W
      (1 : RationalGL3) o.out (fun g => g.2) (out_mem_labelOrbit o) 2)
  exact this

end Coordinates



section OfGlobal

variable {W : Rep.{0} ℚ Γ6}
  (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ W) (hf : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0)
  (w : A.X 1 ⟶ W) (hw : A.d 2 1 ≫ w = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f)

theorem LineDatum.ofGlobal_cls :
    (LineDatum.ofGlobal f hf w hw).cls =
      (HomologicalComplex.homologyMap (homPullback (ptMap Line) W) 2).hom
        (cls2 (homCochains (prodComplex Γ6 RationalGL3 PUnit) W) f hf) := by
  have hc : ((homCochains (prodComplex Γ6 RationalGL3 PUnit) W).d 2 3).hom f = 0 := hf
  have e := cls2_map (homCochains (prodComplex Γ6 RationalGL3 PUnit) W) (homPullback (ptMap Line) W) f hc
    (map_cocycle _ _ _ hc)
  rw [e]
  rfl

include hw in
theorem PlaneDatum.ofGlobal_cls :
    (PlaneDatum.ofGlobal f hf w hw).cls =
      (HomologicalComplex.homologyMap (homPullback (ptMap Plane) W) 2).hom
        (cls2 (homCochains (prodComplex Γ6 RationalGL3 PUnit) W) f hf) := by
  have hc : ((homCochains (prodComplex Γ6 RationalGL3 PUnit) W).d 2 3).hom f = 0 := hf
  have e := cls2_map (homCochains (prodComplex Γ6 RationalGL3 PUnit) W) (homPullback (ptMap Plane) W) f hc
    (map_cocycle _ _ _ hc)
  rw [e]
  rfl

end OfGlobal

section StokesCoordinates

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ Γ6 V)
  [Fintype (labelOrbits Γ6 Line)] [Fintype (labelOrbits Γ6 Plane)]

/-- The Shapiro coordinate at the orbit `o` of lines of the line restriction of a class of the point resolution. -/
def lineCoord (W : Rep.{0} ℚ Γ6) (X : (homCochains (prodComplex Γ6 RationalGL3 PUnit) W).homology 2)
    (o : labelOrbits Γ6 Line) : groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype W) 2 :=
  (faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom
    ((HomologicalComplex.homologyMap (homPullback (ptMap Line) W) 2).hom X)

/-- … and of planes. -/
def planeCoord (W : Rep.{0} ℚ Γ6) (X : (homCochains (prodComplex Γ6 RationalGL3 PUnit) W).homology 2)
    (o : labelOrbits Γ6 Plane) : groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype W) 2 :=
  (faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom
    ((HomologicalComplex.homologyMap (homPullback (ptMap Plane) W) 2).hom X)

/-- **Lemma `ar:lem:stokes` at level `Γ(6)` in Shapiro coordinates.**  For classes `X`, `X'` of the point resolution with coefficients `E_ℚ`, `(E^*)_ℚ` whose restrictions to
the complete flags vanish, the sum over the orbits of lines of the orbit pairings of the line coordinates of `X`, `X'` plus the sum over the orbits of planes of the orbit pairings
of their plane coordinates vanishes. -/
theorem stokes_orbit_coordinates
    (X : (homCochains (prodComplex Γ6 RationalGL3 PUnit) (qRep (MonoidHom.id Γ6) ρ)).homology 2)
    (X' : (homCochains (prodComplex Γ6 RationalGL3 PUnit) (qRep (MonoidHom.id Γ6) ρ.dual)).homology 2)
    (hX : (HomologicalComplex.homologyMap (homPullback (ptMap Flag) (qRep (MonoidHom.id Γ6) ρ)) 2).hom X = 0)
    (hX' : (HomologicalComplex.homologyMap (homPullback (ptMap Flag) (qRep (MonoidHom.id Γ6) ρ.dual)) 2).hom X' = 0) :
    ∑ o : labelOrbits Γ6 Line,
        lineOrbitPair (evalC (MonoidHom.id Γ6) ρ) stokesCycle o
          (lineCoord _ X o) (lineCoord _ X' o) +
      ∑ p : labelOrbits Γ6 Plane,
        planeOrbitPair (evalC (MonoidHom.id Γ6) ρ) stokesCycle p
          (planeCoord _ X p) (planeCoord _ X' p) = 0 := by
  classical
  obtain ⟨f, hf, rfl⟩ := exists_cls2 _ X
  obtain ⟨f', hf', rfl⟩ := exists_cls2 _ X'
  have hf1 : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0 := hf
  have hf1' : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f' = 0 := hf'
  have hflagf : (ptMap Flag).f 2 ≫ f = (flagLineHom.hom.f 2 ≫ (ptMap Line).f 2) ≫ f := by
    rw [← flagLine_ptMap]; rfl
  have hprim : ∀ {W : Rep.{0} ℚ Γ6} (g : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ W)
      (hg : ((homCochains (prodComplex Γ6 RationalGL3 PUnit) W).d 2 3).hom g = 0),
      (HomologicalComplex.homologyMap (homPullback (ptMap Flag) W) 2).hom
        (cls2 (homCochains (prodComplex Γ6 RationalGL3 PUnit) W) g hg) = 0 →
      ∃ u : A.X 1 ⟶ W, A.d 2 1 ≫ u = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ g := by
    intro W g hg h0
    have e := cls2_map (homCochains (prodComplex Γ6 RationalGL3 PUnit) W) (homPullback (ptMap Flag) W) g hg
      (map_cocycle _ _ _ hg)
    rw [e] at h0
    obtain ⟨u, hu⟩ := (cls2_eq_zero_iff _ _ _).1 h0
    refine ⟨u, ?_⟩
    have hu' : A.d 2 1 ≫ u = (ptMap Flag).f 2 ≫ g := hu
    rw [hu', ← flagLine_ptMap]
    simp only [HomologicalComplex.comp_f, Category.assoc]
  obtain ⟨w, hw⟩ := hprim f hf hX
  obtain ⟨w', hw'⟩ := hprim f' hf' hX'
  have key := cone_stokes_orbits (MonoidHom.id Γ6) ρ f hf1 f' hf1' w hw w' hw'
  rw [← key]
  congr 1
  · refine Finset.sum_congr rfl (fun o _ => ?_)
    have e1 : lineCoord (qRep (MonoidHom.id Γ6) ρ) (cls2 _ f hf) o =
        (((LineDatum.ofGlobal f hf1 w hw).cut (labelOrbit Γ6 Line o) (labelOrbit_invariant o))).coord o := by
      rw [LineDatum.cut_coord]
      unfold lineCoord LineDatum.coord
      erw [LineDatum.ofGlobal_cls]
    have e2 : lineCoord (qRep (MonoidHom.id Γ6) ρ.dual) (cls2 _ f' hf') o =
        (((LineDatum.ofGlobal f' hf1' w' hw').cut (labelOrbit Γ6 Line o) (labelOrbit_invariant o))).coord o := by
      rw [LineDatum.cut_coord]
      unfold lineCoord LineDatum.coord
      erw [LineDatum.ofGlobal_cls]
    rw [e1, e2]
    exact lineOrbitPair_eq _ stokesCycle stokesCycle_isCoinvCycle o _ _
      (LineDatum.cut_isOn _ _ _) (LineDatum.cut_isOn _ _ _)
  · refine Finset.sum_congr rfl (fun o _ => ?_)
    have e1 : planeCoord (qRep (MonoidHom.id Γ6) ρ) (cls2 _ f hf) o =
        (((PlaneDatum.ofGlobal f hf1 w hw).cut (labelOrbit Γ6 Plane o) (labelOrbit_invariant o))).coord o := by
      rw [PlaneDatum.cut_coord]
      unfold planeCoord PlaneDatum.coord
      erw [PlaneDatum.ofGlobal_cls]
    have e2 : planeCoord (qRep (MonoidHom.id Γ6) ρ.dual) (cls2 _ f' hf') o =
        (((PlaneDatum.ofGlobal f' hf1' w' hw').cut (labelOrbit Γ6 Plane o) (labelOrbit_invariant o))).coord o := by
      rw [PlaneDatum.cut_coord]
      unfold planeCoord PlaneDatum.coord
      erw [PlaneDatum.ofGlobal_cls]
    rw [e1, e2]
    exact planeOrbitPair_eq _ stokesCycle stokesCycle_isCoinvCycle o _ _
      (PlaneDatum.cut_isOn _ _ _) (PlaneDatum.cut_isOn _ _ _)

end StokesCoordinates

end TernaryPeriodPolynomials.Argument.GammaNStokes
