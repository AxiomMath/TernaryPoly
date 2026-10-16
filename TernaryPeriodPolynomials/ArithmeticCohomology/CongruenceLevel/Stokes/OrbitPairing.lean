module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Orth
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ComplexStokes
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ShapiroCut
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ShapiroProduct
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cls

@[expose] public section


/-!
# Face pairings by orbit: complex-valued pairing, orbit decomposition and dependence on the Shapiro coordinates

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open GeneralEisenstein
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPoly.BoundaryFaceResolutionComparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section Orbits

variable {Γ : Type} [Group Γ] {Z : Type} [MulAction Γ Z]

theorem mem_labelOrbit_iff (o : labelOrbits Γ Z) (z : Z) :
    z ∈ labelOrbit Γ Z o ↔ (Quotient.mk'' z : labelOrbits Γ Z) = o := by
  rw [← MulAction.orbitRel.Quotient.mem_orbit]
  have h := MulAction.orbitRel.Quotient.orbit_eq_orbit_out o (φ := Quotient.out) (Quotient.out_eq)
  rw [h]

theorem labelOrbit_invariant (o : labelOrbits Γ Z) (γ : Γ) (z : Z) :
    γ • z ∈ labelOrbit Γ Z o ↔ z ∈ labelOrbit Γ Z o := by
  rw [mem_labelOrbit_iff, mem_labelOrbit_iff]
  have h : (Quotient.mk'' (γ • z) : labelOrbits Γ Z) = Quotient.mk'' z :=
    MulAction.orbitRel.Quotient.quotient_smul_eq
  rw [h]

theorem labelOrbit_partition (z : Z) : ∃! o : labelOrbits Γ Z, z ∈ labelOrbit Γ Z o := by
  refine ⟨Quotient.mk'' z, (mem_labelOrbit_iff _ z).2 rfl, fun o ho => ?_⟩
  exact ((mem_labelOrbit_iff o z).1 ho).symm

end Orbits


section ComplexPair

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ Rep.trivial ℚ Γ6 ℂ) (v : coneR.X 4)

theorem conePairC_eq_of_rat {X X' : coneR.X 2 ⟶ W} {Y Y' : coneR.X 2 ⟶ W'}
    (h : ∀ r : ℂ →ₗ[ℚ] ℚ, conePair (π ≫ rHom r) v X Y = conePair (π ≫ rHom r) v X' Y') :
    conePairC π v X Y = conePairC π v X' Y' := by
  have := eq_zero_of_forall_rat_functional
    (z := conePairC π v X Y - conePairC π v X' Y') (fun r => by
      rw [map_sub, rHom_conePairC, rHom_conePairC, h r, sub_self])
  exact sub_eq_zero.mp this

theorem LineDatum.pairC_congr (hv : IsCoinvCycle v) (d1 d2 : LineDatum W) (e1 e2 : LineDatum W')
    (ζ : (prodComplex Γ6 RationalGL3 Line).X 1 ⟶ W)
    (h : d1.z = d2.z + (prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ ζ)
    (ζ' : (prodComplex Γ6 RationalGL3 Line).X 1 ⟶ W')
    (h' : e1.z = e2.z + (prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ ζ') :
    conePairC π v d1.cone e1.cone = conePairC π v d2.cone e2.cone :=
  conePairC_eq_of_rat π v (fun r => LineDatum.pair_congr (π ≫ rHom r) v d1 d2 e1 e2 ζ h ζ' h' hv)

theorem PlaneDatum.pairC_congr (hv : IsCoinvCycle v) (d1 d2 : PlaneDatum W) (e1 e2 : PlaneDatum W')
    (ζ : (prodComplex Γ6 RationalGL3 Plane).X 1 ⟶ W)
    (h : d1.z = d2.z + (prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ ζ)
    (ζ' : (prodComplex Γ6 RationalGL3 Plane).X 1 ⟶ W')
    (h' : e1.z = e2.z + (prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ ζ') :
    conePairC π v d1.cone e1.cone = conePairC π v d2.cone e2.cone :=
  conePairC_eq_of_rat π v (fun r => PlaneDatum.pair_congr (π ≫ rHom r) v d1 d2 e1 e2 ζ h ζ' h' hv)

variable {ι : Type} [Fintype ι]

theorem LineDatum.pairC_eq_sum (S : ι → Set Line)
    (hS : ∀ (i : ι) (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S i ↔ ℓ ∈ S i) (hpart : ∀ ℓ : Line, ∃! i, ℓ ∈ S i)
    (d : LineDatum W) (e : LineDatum W') :
    conePairC π v d.cone e.cone =
      ∑ i, conePairC π v (d.cut (S i) (hS i)).cone (e.cut (S i) (hS i)).cone := by
  have := eq_zero_of_forall_rat_functional
    (z := conePairC π v d.cone e.cone -
      ∑ i, conePairC π v (d.cut (S i) (hS i)).cone (e.cut (S i) (hS i)).cone) (fun r => by
      rw [map_sub, map_sum, rHom_conePairC]
      simp only [rHom_conePairC]
      rw [LineDatum.pair_eq_sum (π ≫ rHom r) v S hS hpart d e, sub_self])
  exact sub_eq_zero.mp this

theorem PlaneDatum.pairC_eq_sum (S : ι → Set Plane)
    (hS : ∀ (i : ι) (γ : Γ6) (P : Plane), γ • P ∈ S i ↔ P ∈ S i) (hpart : ∀ P : Plane, ∃! i, P ∈ S i)
    (d : PlaneDatum W) (e : PlaneDatum W') :
    conePairC π v d.cone e.cone =
      ∑ i, conePairC π v (d.cut (S i) (hS i)).cone (e.cut (S i) (hS i)).cone := by
  have := eq_zero_of_forall_rat_functional
    (z := conePairC π v d.cone e.cone -
      ∑ i, conePairC π v (d.cut (S i) (hS i)).cone (e.cut (S i) (hS i)).cone) (fun r => by
      rw [map_sub, map_sum, rHom_conePairC]
      simp only [rHom_conePairC]
      rw [PlaneDatum.pair_eq_sum (π ≫ rHom r) v S hS hpart d e, sub_self])
  exact sub_eq_zero.mp this

end ComplexPair


section Support

variable {W : Rep.{0} ℚ Γ6}

/-- A line datum supported on a set of lines (and the flags over them). -/
def LineDatum.IsOn (S : Set Line) (d : LineDatum W) : Prop :=
  (∀ (u : Fin 3 → RationalGL3) (ℓ : Line), ℓ ∉ S → d.z.hom (MonoidAlgebra.single (u, ℓ) 1) = 0) ∧
    ∀ (u : Fin 2 → RationalGL3) (F : Flag), flagLineOf F ∉ S → d.w.hom (MonoidAlgebra.single (u, F) 1) = 0

/-- A plane datum supported on a set of planes (and the flags over them). -/
def PlaneDatum.IsOn (S : Set Plane) (d : PlaneDatum W) : Prop :=
  (∀ (u : Fin 3 → RationalGL3) (P : Plane), P ∉ S → d.z.hom (MonoidAlgebra.single (u, P) 1) = 0) ∧
    ∀ (u : Fin 2 → RationalGL3) (F : Flag), flagPlaneOf F ∉ S → d.w.hom (MonoidAlgebra.single (u, F) 1) = 0

open Classical in
theorem LineDatum.cut_isOn (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S) (d : LineDatum W) :
    (d.cut S hS).IsOn S :=
  ⟨fun u ℓ h => by rw [LineDatum.cut_z_single, ite_eq_right h],
    fun u F h => by rw [LineDatum.cut_w_single, ite_eq_right h]⟩

open Classical in
theorem PlaneDatum.cut_isOn (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S) (d : PlaneDatum W) :
    (d.cut S hS).IsOn S :=
  ⟨fun u P h => by rw [PlaneDatum.cut_z_single, ite_eq_right h],
    fun u F h => by rw [PlaneDatum.cut_w_single, ite_eq_right h]⟩

open Classical in
theorem LineDatum.cut_z_of_isOn (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S)
    (d : LineDatum W) (h : d.IsOn S) : cutHom Γ6 RationalGL3 Line S hS 2 ≫ d.z = d.z := by
  refine hom_ext_single ((Fin 3 → RationalGL3) × Line) _ (fun y => ?_)
  obtain ⟨u, ℓ⟩ := y
  change d.z.hom ((cutHom Γ6 RationalGL3 Line S hS 2).hom (MonoidAlgebra.single (u, ℓ) 1)) = _
  by_cases hℓ : ℓ ∈ S
  · erw [cutHom_single, ite_eq_left hℓ]
    rfl
  · erw [cutHom_single, ite_eq_right hℓ, map_zero]
    exact (h.1 u ℓ hℓ).symm

open Classical in
theorem PlaneDatum.cut_z_of_isOn (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S)
    (d : PlaneDatum W) (h : d.IsOn S) : cutHom Γ6 RationalGL3 Plane S hS 2 ≫ d.z = d.z := by
  refine hom_ext_single ((Fin 3 → RationalGL3) × Plane) _ (fun y => ?_)
  obtain ⟨u, P⟩ := y
  change d.z.hom ((cutHom Γ6 RationalGL3 Plane S hS 2).hom (MonoidAlgebra.single (u, P) 1)) = _
  by_cases hP : P ∈ S
  · erw [cutHom_single, ite_eq_left hP]
    rfl
  · erw [cutHom_single, ite_eq_right hP, map_zero]
    exact (h.1 u P hP).symm

end Support


section Coordinates

open TernaryPoly.EquivariantSingularSmall

variable {W : Rep.{0} ℚ Γ6}

/-- The Hom cochains of the line resolution. -/
abbrev LineCochains (W : Rep.{0} ℚ Γ6) : CochainComplex (ModuleCat.{0} ℚ) ℕ :=
  homCochains (prodComplex Γ6 RationalGL3 Line) W

/-- The Hom cochains of the plane resolution. -/
abbrev PlaneCochains (W : Rep.{0} ℚ Γ6) : CochainComplex (ModuleCat.{0} ℚ) ℕ :=
  homCochains (prodComplex Γ6 RationalGL3 Plane) W

/-- The cohomology class of the cocycle of a line datum. -/
def LineDatum.cls (d : LineDatum W) : (LineCochains W).homology 2 :=
  cls2 (LineCochains W) d.z d.hz

/-- The cohomology class of the cocycle of a plane datum. -/
def PlaneDatum.cls (d : PlaneDatum W) : (PlaneCochains W).homology 2 :=
  cls2 (PlaneCochains W) d.z d.hz

/-- The Shapiro coordinate of a line datum at the orbit `o` of lines. -/
def LineDatum.coord (o : labelOrbits Γ6 Line) (d : LineDatum W) :
    groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype W) 2 :=
  (faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom d.cls

/-- The Shapiro coordinate of a plane datum at the orbit `o` of planes. -/
def PlaneDatum.coord (o : labelOrbits Γ6 Plane) (d : PlaneDatum W) :
    groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype W) 2 :=
  (faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 2).hom d.cls

theorem LineDatum.exists_coboundary_of_cls_eq (d e : LineDatum W) (h : d.cls = e.cls) :
    ∃ ζ : (prodComplex Γ6 RationalGL3 Line).X 1 ⟶ W,
      d.z = e.z + (prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ ζ := by
  have hd : ((LineCochains W).d 2 3).hom d.z = 0 := d.hz
  have he : ((LineCochains W).d 2 3).hom e.z = 0 := e.hz
  have h1 : ((LineCochains W).d 2 3).hom (d.z - e.z) = 0 := by erw [map_sub, hd, he, sub_zero]
  have h2 : cls2 (LineCochains W) (d.z - e.z) h1 + cls2 (LineCochains W) e.z he =
      cls2 (LineCochains W) d.z hd := by
    rw [← cls2_add _ _ _ h1 he (by erw [map_add, h1, he, add_zero])]
    exact cls2_congr _ _ _ (sub_add_cancel _ _)
  have h3 : cls2 (LineCochains W) (d.z - e.z) h1 = 0 := by
    have : cls2 (LineCochains W) d.z hd = cls2 (LineCochains W) e.z he := h
    rw [this] at h2
    exact add_right_cancel (h2.trans (zero_add _).symm)
  obtain ⟨b, hb⟩ := (cls2_eq_zero_iff _ _ h1).1 h3
  refine ⟨b, ?_⟩
  have hb' : (prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ b = d.z - e.z := hb
  rw [hb']
  abel

theorem PlaneDatum.exists_coboundary_of_cls_eq (d e : PlaneDatum W) (h : d.cls = e.cls) :
    ∃ ζ : (prodComplex Γ6 RationalGL3 Plane).X 1 ⟶ W,
      d.z = e.z + (prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ ζ := by
  have hd : ((PlaneCochains W).d 2 3).hom d.z = 0 := d.hz
  have he : ((PlaneCochains W).d 2 3).hom e.z = 0 := e.hz
  have h1 : ((PlaneCochains W).d 2 3).hom (d.z - e.z) = 0 := by erw [map_sub, hd, he, sub_zero]
  have h2 : cls2 (PlaneCochains W) (d.z - e.z) h1 + cls2 (PlaneCochains W) e.z he =
      cls2 (PlaneCochains W) d.z hd := by
    rw [← cls2_add _ _ _ h1 he (by erw [map_add, h1, he, add_zero])]
    exact cls2_congr _ _ _ (sub_add_cancel _ _)
  have h3 : cls2 (PlaneCochains W) (d.z - e.z) h1 = 0 := by
    have : cls2 (PlaneCochains W) d.z hd = cls2 (PlaneCochains W) e.z he := h
    rw [this] at h2
    exact add_right_cancel (h2.trans (zero_add _).symm)
  obtain ⟨b, hb⟩ := (cls2_eq_zero_iff _ _ h1).1 h3
  refine ⟨b, ?_⟩
  have hb' : (prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ b = d.z - e.z := hb
  rw [hb']
  abel


open Classical in
theorem LineDatum.cls_cut (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S)
    (d : LineDatum W) (h : d.IsOn S) :
    (HomologicalComplex.homologyMap (homPullback (cutChain Γ6 RationalGL3 Line S hS) W) 2).hom d.cls = d.cls := by
  have hc : ((LineCochains W).d 2 3).hom d.z = 0 := d.hz
  have e := cls2_map (LineCochains W) (homPullback (cutChain Γ6 RationalGL3 Line S hS) W) d.z hc
    (map_cocycle _ _ _ hc)
  unfold LineDatum.cls
  rw [e]
  exact cls2_congr _ _ _ (LineDatum.cut_z_of_isOn S hS d h)

open Classical in
theorem PlaneDatum.cls_cut (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S)
    (d : PlaneDatum W) (h : d.IsOn S) :
    (HomologicalComplex.homologyMap (homPullback (cutChain Γ6 RationalGL3 Plane S hS) W) 2).hom d.cls = d.cls := by
  have hc : ((PlaneCochains W).d 2 3).hom d.z = 0 := d.hz
  have e := cls2_map (PlaneCochains W) (homPullback (cutChain Γ6 RationalGL3 Plane S hS) W) d.z hc
    (map_cocycle _ _ _ hc)
  unfold PlaneDatum.cls
  rw [e]
  exact cls2_congr _ _ _ (PlaneDatum.cut_z_of_isOn S hS d h)

/-- **A line datum supported on one orbit is determined, up to coboundary, by its Shapiro coordinate at that orbit.** -/
theorem LineDatum.cls_eq_of_coord_eq (o : labelOrbits Γ6 Line) (d e : LineDatum W)
    (hd : d.IsOn (labelOrbit Γ6 Line o)) (he : e.IsOn (labelOrbit Γ6 Line o))
    (h : d.coord o = e.coord o) : d.cls = e.cls := by
  have hinj := (faceCoord_product_bijective (Γ := Γ6) (V := RationalGL3) (Z := Line) (1 : RationalGL3)
    vertexAction_free' W).1
  apply hinj
  funext o'
  by_cases hoo : o' = o
  · subst hoo
    exact h
  · have key : ∀ d : LineDatum W, d.IsOn (labelOrbit Γ6 Line o) →
        (faceCoord (stabilizer Γ6 o'.out) W (1 : RationalGL3) o'.out (fun g => g.2) 2).hom d.cls = 0 := by
      intro d hd
      have hnot : o'.out ∉ labelOrbit Γ6 Line o := by
        intro hmem
        exact hoo (((labelOrbit_partition (Γ := Γ6) (Z := Line) o'.out).unique
          ((mem_labelOrbit_iff _ _).2 (Quotient.out_eq o')) hmem))
      have := congrArg (fun m => m.hom d.cls)
        (faceCoord_cut_not_mem (labelOrbit Γ6 Line o) (labelOrbit_invariant o) (stabilizer Γ6 o'.out) W
          (1 : RationalGL3) o'.out (fun g => g.2) hnot 2)
      rw [← LineDatum.cls_cut _ (labelOrbit_invariant o) d hd]
      exact this
    exact (key d hd).trans (key e he).symm

open Classical in
/-- … and the same for planes. -/
theorem PlaneDatum.cls_eq_of_coord_eq (o : labelOrbits Γ6 Plane) (d e : PlaneDatum W)
    (hd : d.IsOn (labelOrbit Γ6 Plane o)) (he : e.IsOn (labelOrbit Γ6 Plane o))
    (h : d.coord o = e.coord o) : d.cls = e.cls := by
  have hinj := (faceCoord_product_bijective (Γ := Γ6) (V := RationalGL3) (Z := Plane) (1 : RationalGL3)
    vertexAction_free' W).1
  apply hinj
  funext o'
  by_cases hoo : o' = o
  · subst hoo
    exact h
  · have key : ∀ d : PlaneDatum W, d.IsOn (labelOrbit Γ6 Plane o) →
        (faceCoord (stabilizer Γ6 o'.out) W (1 : RationalGL3) o'.out (fun g => g.2) 2).hom d.cls = 0 := by
      intro d hd
      have hnot : o'.out ∉ labelOrbit Γ6 Plane o := by
        intro hmem
        exact hoo (((labelOrbit_partition (Γ := Γ6) (Z := Plane) o'.out).unique
          ((mem_labelOrbit_iff _ _).2 (Quotient.out_eq o')) hmem))
      have := congrArg (fun m => m.hom d.cls)
        (faceCoord_cut_not_mem (labelOrbit Γ6 Plane o) (labelOrbit_invariant o) (stabilizer Γ6 o'.out) W
          (1 : RationalGL3) o'.out (fun g => g.2) hnot 2)
      rw [← PlaneDatum.cls_cut _ (labelOrbit_invariant o) d hd]
      exact this
    exact (key d hd).trans (key e he).symm

end Coordinates


section Pairs

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ Rep.trivial ℚ Γ6 ℂ) (v : coneR.X 4) (hv : IsCoinvCycle v)

include hv in
theorem LineDatum.pairC_eq_of_coord_eq (o : labelOrbits Γ6 Line) (d1 d2 : LineDatum W) (e1 e2 : LineDatum W')
    (hd1 : d1.IsOn (labelOrbit Γ6 Line o)) (hd2 : d2.IsOn (labelOrbit Γ6 Line o))
    (he1 : e1.IsOn (labelOrbit Γ6 Line o)) (he2 : e2.IsOn (labelOrbit Γ6 Line o))
    (hd : d1.coord o = d2.coord o) (he : e1.coord o = e2.coord o) :
    conePairC π v d1.cone e1.cone = conePairC π v d2.cone e2.cone := by
  obtain ⟨ζ, h⟩ := LineDatum.exists_coboundary_of_cls_eq d1 d2 (LineDatum.cls_eq_of_coord_eq o d1 d2 hd1 hd2 hd)
  obtain ⟨ζ', h'⟩ := LineDatum.exists_coboundary_of_cls_eq e1 e2 (LineDatum.cls_eq_of_coord_eq o e1 e2 he1 he2 he)
  exact LineDatum.pairC_congr π v hv d1 d2 e1 e2 ζ h ζ' h'

include hv in
theorem PlaneDatum.pairC_eq_of_coord_eq (o : labelOrbits Γ6 Plane) (d1 d2 : PlaneDatum W) (e1 e2 : PlaneDatum W')
    (hd1 : d1.IsOn (labelOrbit Γ6 Plane o)) (hd2 : d2.IsOn (labelOrbit Γ6 Plane o))
    (he1 : e1.IsOn (labelOrbit Γ6 Plane o)) (he2 : e2.IsOn (labelOrbit Γ6 Plane o))
    (hd : d1.coord o = d2.coord o) (he : e1.coord o = e2.coord o) :
    conePairC π v d1.cone e1.cone = conePairC π v d2.cone e2.cone := by
  obtain ⟨ζ, h⟩ := PlaneDatum.exists_coboundary_of_cls_eq d1 d2 (PlaneDatum.cls_eq_of_coord_eq o d1 d2 hd1 hd2 hd)
  obtain ⟨ζ', h'⟩ := PlaneDatum.exists_coboundary_of_cls_eq e1 e2 (PlaneDatum.cls_eq_of_coord_eq o e1 e2 he1 he2 he)
  exact PlaneDatum.pairC_congr π v hv d1 d2 e1 e2 ζ h ζ' h'

end Pairs

end TernaryPeriodPolynomials.Argument.GammaNStokes
