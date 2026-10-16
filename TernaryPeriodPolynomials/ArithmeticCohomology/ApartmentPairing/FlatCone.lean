module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.FlatChain
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FacesLabels
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVFaces
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVComplete
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceAugmentationModels
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceAugmentationNaturality
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeTotal
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.GeometricEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonApartment
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullConeCoordinates
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullConeComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.CofiberSequence

@[expose] public section


/-!
# The boundary hexagon of the flat as a cycle of the geometric face cone

The twelve arcs of the boundary hexagon of the compactified diagonal flat lie in the closed line
faces and plane faces of the bordification boundary, and its six Borel vertices in the flag faces.
With the signs of the geometric face cone `faceCone` they form a degree-one cycle `coneCycle`
(`coneChain_d`); its literal Mayer--Vietoris edge is the alternating sum of the six chamber flags
(`coneCycle_edge_flags`). The image of the cone chain in the singular chains of the bordification is
the hexagon of arcs (`hexBoundaryChain_upstairs`), i.e. exactly the boundary of the flat chain.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory AlgebraicTopology
open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceFlagCoordinates
  TernaryPoly.SymmetricSpaceRationalAction TernaryPoly.SymmetricSpaceRationalCharts
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.EquivariantSingularResolution
  TernaryPoly.FreeActionLinearization
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology TernaryPoly.OrdinaryTopBoundaryComparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33

/-! ### The boundary hexagon on the closed faces -/

open TernaryPoly.SymmetricSpaceBoundaryFaces TernaryPoly.SymmetricSpaceBoundaryMV
  TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation TernaryPoly.SymmetricSpaceBoundaryGeometricCone

theorem affSimplex_apply {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) {n : ℕ} (p : Fin (n + 1) → ℝ × ℝ)
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    X.toSSetObjEquiv _ (affSimplex f p) z = f (affineMap n p z) := by
  simp [affSimplex]

/-- A singular simplex of the sum of closed faces `Σ j, F j`, from a simplex of `Glued` lying in
the `i`-th face. -/
def liftSimplex {ι : Type} (F : ι → Set Glued) (i : ι) {n : ℕ}
    (σ : SingularSimplex (TopCat.of Glued) n)
    (h : ∀ z, (TopCat.of Glued).toSSetObjEquiv _ σ z ∈ F i) :
    SingularSimplex (TopCat.of (Σ j, ↥(F j))) n :=
  ((TopCat.of (Σ j, ↥(F j))).toSSetObjEquiv _).symm
    ⟨fun z => ⟨i, ⟨(TopCat.of Glued).toSSetObjEquiv _ σ z, h z⟩⟩,
      continuous_sigmaMk.comp (((TopCat.of Glued).toSSetObjEquiv _ σ).continuous.subtype_mk _)⟩

theorem liftSimplex_δ {ι : Type} (F : ι → Set Glued) (i : ι) {n : ℕ}
    (σ : SingularSimplex (TopCat.of Glued) (n + 1))
    (h : ∀ z, (TopCat.of Glued).toSSetObjEquiv _ σ z ∈ F i) (j : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of (Σ j, ↥(F j)))).δ j (liftSimplex F i σ h) =
      liftSimplex F i ((TopCat.toSSet.obj (TopCat.of Glued)).δ j σ)
        (fun z => by
          rw [TopCat.toSSetObjEquiv_δ_apply]
          exact h _) := by
  apply ((TopCat.of (Σ j, ↥(F j))).toSSetObjEquiv _).injective
  refine ContinuousMap.ext (fun z => ?_)
  rw [TopCat.toSSetObjEquiv_δ_apply]
  simp only [liftSimplex, Equiv.apply_symm_apply]
  rfl

theorem liftSimplex_congr {ι : Type} (F : ι → Set Glued) {i i' : ι} (hi : i = i') {n : ℕ}
    {σ σ' : SingularSimplex (TopCat.of Glued) n} (hσ : σ = σ')
    (h : ∀ z, (TopCat.of Glued).toSSetObjEquiv _ σ z ∈ F i)
    (h' : ∀ z, (TopCat.of Glued).toSSetObjEquiv _ σ' z ∈ F i') :
    liftSimplex F i σ h = liftSimplex F i' σ' h' := by
  subst hi hσ
  rfl

theorem seg_face0 {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) (a b : ℝ × ℝ) :
    (TopCat.toSSet.obj X).δ 0 (seg f a b) = vert f b := by
  rw [seg, affSimplex_face]
  congr 1

theorem seg_face1 {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) (a b : ℝ × ℝ) :
    (TopCat.toSSet.obj X).δ 1 (seg f a b) = vert f a := by
  rw [seg, affSimplex_face]
  congr 1
  funext i
  fin_cases i
  rfl

theorem chamber_line_mem (g : RationalGL) (r : ℝ) : chamber g (0, r) ∈ lineFace (lineLabel g) := by
  change chamberH g (clampH 0, clampH r) ∈ _
  exact (lineFace_chart_iff _ g _).mpr ⟨by simp [clampH], rfl⟩

theorem chamber_plane_mem (g : RationalGL) (r : ℝ) :
    chamber g (r, 0) ∈ planeFace (planeLabel g) := by
  change chamberH g (clampH r, clampH 0) ∈ _
  exact (planeFace_chart_iff _ g _).mpr ⟨by simp [clampH], rfl⟩

theorem chamber_flag_mem (g : RationalGL) : chamber g (0, 0) ∈ flagFace (flagLabel g) :=
  ⟨chamber_line_mem g 0, chamber_plane_mem g 0⟩

theorem seg_line_mem (g : RationalGL) (z : Convexity.StdSimplex ℝ (Fin 2)) :
    (TopCat.of Glued).toSSetObjEquiv _ (seg (chamber g) pv pb) z ∈ lineFace (lineLabel g) := by
  have e : affineMap 1 ![pv, pb] z = (0, z.weights 1) := by
    simp only [affineMap, ContinuousMap.coe_mk, pv, pb]
    ext <;> simp
  rw [seg, affSimplex_apply, e]
  exact chamber_line_mem g _

theorem seg_plane_mem (g : RationalGL) (z : Convexity.StdSimplex ℝ (Fin 2)) :
    (TopCat.of Glued).toSSetObjEquiv _ (seg (chamber g) pv pa) z ∈ planeFace (planeLabel g) := by
  have e : affineMap 1 ![pv, pa] z = (z.weights 1, 0) := by
    simp only [affineMap, ContinuousMap.coe_mk, pv, pa]
    ext <;> simp
  rw [seg, affSimplex_apply, e]
  exact chamber_plane_mem g _

theorem vert_mem (F : Set Glued) (x : ℝ × ℝ) (g : C(ℝ × ℝ, TopCat.of Glued))
    (h : g x ∈ F) (z : Convexity.StdSimplex ℝ (Fin 1)) :
    (TopCat.of Glued).toSSetObjEquiv _ (vert g x) z ∈ F := by
  rw [vert, affSimplex_apply, affineMap_zero]
  exact h


/-! ### Arcs and corners in the sums of closed faces -/

theorem vert_congr {X : TopCat.{0}} (f g : C(ℝ × ℝ, X)) (a : ℝ × ℝ) (h : f a = g a) :
    vert f a = vert g a := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  rw [vert, vert, affSimplex_apply, affSimplex_apply, affineMap_zero, h]

/-- The plane-side arc of the `k`-th chamber, as a simplex of the plane faces. -/
def planeArc (k : ℕ) : SingularSimplex (TopCat.of PlaneFaceSum) 1 :=
  liftSimplex planeFace (planeLabel (hexW k)) (seg (fk k) pv pa) (seg_plane_mem (hexW k))

/-- The corner of the `k`-th chamber, as a simplex of the plane faces. -/
def planeBase (k : ℕ) : SingularSimplex (TopCat.of PlaneFaceSum) 0 :=
  liftSimplex planeFace (planeLabel (hexW k)) (vert (fk k) pv)
    (vert_mem _ pv (fk k) (chamber_plane_mem (hexW k) 0))

/-- The far end of the plane-side arc of the `k`-th chamber. -/
def planeEnd (k : ℕ) : SingularSimplex (TopCat.of PlaneFaceSum) 0 :=
  liftSimplex planeFace (planeLabel (hexW k)) (vert (fk k) pa)
    (vert_mem _ pa (fk k) (chamber_plane_mem (hexW k) 1))

/-- The line-side arc of the `k`-th chamber, as a simplex of the line faces. -/
def lineArc (k : ℕ) : SingularSimplex (TopCat.of LineFaceSum) 1 :=
  liftSimplex lineFace (lineLabel (hexW k)) (seg (fk k) pv pb) (seg_line_mem (hexW k))

/-- The corner of the `k`-th chamber, as a simplex of the line faces. -/
def lineBase (k : ℕ) : SingularSimplex (TopCat.of LineFaceSum) 0 :=
  liftSimplex lineFace (lineLabel (hexW k)) (vert (fk k) pv)
    (vert_mem _ pv (fk k) (chamber_line_mem (hexW k) 0))

/-- The far end of the line-side arc of the `k`-th chamber. -/
def lineEnd (k : ℕ) : SingularSimplex (TopCat.of LineFaceSum) 0 :=
  liftSimplex lineFace (lineLabel (hexW k)) (vert (fk k) pb)
    (vert_mem _ pb (fk k) (chamber_line_mem (hexW k) 1))

/-- The corner (Borel vertex) of the `k`-th chamber, as a simplex of the flag faces. -/
def cornerPt (k : ℕ) : SingularSimplex (TopCat.of CornerFaceSum) 0 :=
  liftSimplex flagFace (flagLabel (hexW k)) (vert (fk k) pv)
    (vert_mem _ pv (fk k) (chamber_flag_mem (hexW k)))

theorem d_planeArc (k : ℕ) :
    ((underlyingChains (TopCat.of PlaneFaceSum)).d 1 0).hom (sing _ (planeArc k)) =
      sing _ (planeEnd k) - sing _ (planeBase k) := by
  rw [d_sing, Fin.sum_univ_two]
  have h0 : (TopCat.toSSet.obj (TopCat.of PlaneFaceSum)).δ 0 (planeArc k) = planeEnd k := by
    unfold planeArc planeEnd
    rw [liftSimplex_δ]
    exact liftSimplex_congr planeFace rfl (seg_face0 _ _ _) _ _
  have h1 : (TopCat.toSSet.obj (TopCat.of PlaneFaceSum)).δ 1 (planeArc k) = planeBase k := by
    unfold planeArc planeBase
    rw [liftSimplex_δ]
    exact liftSimplex_congr planeFace rfl (seg_face1 _ _ _) _ _
  rw [h0, h1]
  simp [sub_eq_add_neg]

theorem d_lineArc (k : ℕ) :
    ((underlyingChains (TopCat.of LineFaceSum)).d 1 0).hom (sing _ (lineArc k)) =
      sing _ (lineEnd k) - sing _ (lineBase k) := by
  rw [d_sing, Fin.sum_univ_two]
  have h0 : (TopCat.toSSet.obj (TopCat.of LineFaceSum)).δ 0 (lineArc k) = lineEnd k := by
    unfold lineArc lineEnd
    rw [liftSimplex_δ]
    exact liftSimplex_congr lineFace rfl (seg_face0 _ _ _) _ _
  have h1 : (TopCat.toSSet.obj (TopCat.of LineFaceSum)).δ 1 (lineArc k) = lineBase k := by
    unfold lineArc lineBase
    rw [liftSimplex_δ]
    exact liftSimplex_congr lineFace rfl (seg_face1 _ _ _) _ _
  rw [h0, h1]
  simp [sub_eq_add_neg]

/-- Adjacent chambers share the end of their plane-side arcs (wall `t₁ = 1`). -/
theorem planeEnd_succ (k : ℕ) (hk : Even k) : planeEnd (k + 1) = planeEnd k := by
  have hpt : fk (k + 1) pa = fk k pa := by
    rw [fk, fk, hexW_succ_even k hk]
    exact chamber_wall_one _ 0
  have hlab : planeLabel (hexW (k + 1)) = planeLabel (hexW k) := by
    apply planeFace_unique (x := fk (k + 1) pa)
    · exact chamber_plane_mem (hexW (k + 1)) 1
    · rw [hpt]
      exact chamber_plane_mem (hexW k) 1
  unfold planeEnd
  exact liftSimplex_congr planeFace hlab (vert_congr _ _ pa hpt) _ _

/-- Adjacent chambers share the end of their line-side arcs (wall `t₂ = 1`). -/
theorem lineEnd_succ (k : ℕ) (hk : ¬ Even k) : lineEnd (k + 1) = lineEnd k := by
  have hpt : fk (k + 1) pb = fk k pb := by
    rw [fk, fk, hexW_succ_odd k hk]
    exact chamber_wall_two _ 0
  have hlab : lineLabel (hexW (k + 1)) = lineLabel (hexW k) := by
    apply lineFace_unique (x := fk (k + 1) pb)
    · exact chamber_line_mem (hexW (k + 1)) 1
    · rw [hpt]
      exact chamber_line_mem (hexW k) 1
  unfold lineEnd
  exact liftSimplex_congr lineFace hlab (vert_congr _ _ pb hpt) _ _

theorem lineEnd_six : lineEnd 6 = lineEnd 0 := by
  have hpt : fk 6 pb = fk 0 pb := by rw [fk_six]
  have hlab : lineLabel (hexW 6) = lineLabel (hexW 0) := by rw [hexW_six]
  unfold lineEnd
  exact liftSimplex_congr lineFace hlab (vert_congr _ _ pb hpt) _ _

theorem lineChainMap_cornerPt (k : ℕ) :
    ((SingularCoverNaturality.underlyingMap lineFaceMap).f 0).hom
        (sing (TopCat.of CornerFaceSum) (cornerPt k)) = sing _ (lineBase k) := by
  have h := congrArg (fun m => m.hom (1 : ℚ))
    (SingularCoverNaturality.generator_map lineFaceMap 0 (cornerPt k))
  have hs : (TopCat.toSSet.map lineFaceMap).app _ (cornerPt k) = lineBase k := by
    apply ((TopCat.of LineFaceSum).toSSetObjEquiv _).injective
    refine ContinuousMap.ext (fun z => ?_)
    exact cornerToLineSum_apply _ _
  rw [hs] at h
  exact h

theorem planeChainMap_cornerPt (k : ℕ) :
    ((SingularCoverNaturality.underlyingMap planeFaceMap).f 0).hom
        (sing (TopCat.of CornerFaceSum) (cornerPt k)) = sing _ (planeBase k) := by
  have h := congrArg (fun m => m.hom (1 : ℚ))
    (SingularCoverNaturality.generator_map planeFaceMap 0 (cornerPt k))
  have hs : (TopCat.toSSet.map planeFaceMap).app _ (cornerPt k) = planeBase k := by
    apply ((TopCat.of PlaneFaceSum).toSSetObjEquiv _).injective
    refine ContinuousMap.ext (fun z => ?_)
    exact cornerToPlaneSum_apply _ _
  rw [hs] at h
  exact h

/-! ### The cone cycle of the hexagon -/

open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.BoundaryFaceResolutionComparison
  TernaryPoly.OrdinaryBoundaryActualEvaluation TernaryPoly.IntegralGL3Congruence
  CategoryTheory Limits HomologicalComplex

local instance : HasForget₂ (Rep.{0} ℚ principalSix) Ab :=
  HasForget₂.trans (Rep ℚ principalSix) (ModuleCat ℚ) Ab

local instance : (forget₂ (Rep.{0} ℚ principalSix) Ab).Additive :=
  inferInstanceAs ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).Additive)

local instance : (forget₂ (Rep.{0} ℚ principalSix) Ab).PreservesHomology :=
  inferInstanceAs ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).PreservesHomology)

/-- The line part of the cone cycle: minus the alternating sum of the line-side arcs. -/
def lflat : (underlyingChains (TopCat.of LineFaceSum)).X 1 :=
  -(sing _ (lineArc 0) - sing _ (lineArc 1) + sing _ (lineArc 2) - sing _ (lineArc 3) +
    sing _ (lineArc 4) - sing _ (lineArc 5))

/-- The plane part of the cone cycle: minus the alternating sum of the plane-side arcs. -/
def pflat : (underlyingChains (TopCat.of PlaneFaceSum)).X 1 :=
  -(sing _ (planeArc 0) - sing _ (planeArc 1) + sing _ (planeArc 2) - sing _ (planeArc 3) +
    sing _ (planeArc 4) - sing _ (planeArc 5))

/-- The corner part of the cone cycle: minus the alternating sum of the six Borel vertices. -/
def cflat : (underlyingChains (TopCat.of CornerFaceSum)).X 0 :=
  -(sing _ (cornerPt 0) - sing _ (cornerPt 1) + sing _ (cornerPt 2) - sing _ (cornerPt 3) +
    sing _ (cornerPt 4) - sing _ (cornerPt 5))

theorem d_lflat :
    ((underlyingChains (TopCat.of LineFaceSum)).d 1 0).hom lflat =
      -((lineChainMap.f 0).hom cflat) := by
  have e1 : lineEnd 2 = lineEnd 1 := lineEnd_succ 1 (by decide)
  have e3 : lineEnd 4 = lineEnd 3 := lineEnd_succ 3 (by decide)
  have e5 : lineEnd 6 = lineEnd 5 := lineEnd_succ 5 (by decide)
  rw [lineEnd_six] at e5
  change _ = -(((SingularCoverNaturality.underlyingMap lineFaceMap).f 0).hom cflat)
  simp only [lflat, cflat, map_neg, map_add, map_sub, d_lineArc, lineChainMap_cornerPt]
  rw [e1, e3, e5]
  abel

theorem d_pflat :
    ((underlyingChains (TopCat.of PlaneFaceSum)).d 1 0).hom pflat =
      -((planeChainMap.f 0).hom cflat) := by
  have e0 : planeEnd 1 = planeEnd 0 := planeEnd_succ 0 (by decide)
  have e2 : planeEnd 3 = planeEnd 2 := planeEnd_succ 2 (by decide)
  have e4 : planeEnd 5 = planeEnd 4 := planeEnd_succ 4 (by decide)
  change _ = -(((SingularCoverNaturality.underlyingMap planeFaceMap).f 0).hom cflat)
  simp only [pflat, cflat, map_neg, map_add, map_sub, d_planeArc, planeChainMap_cornerPt]
  rw [e0, e2, e4]
  abel

/-- The explicit chain of the geometric cone: corner minus the line and plane arcs. -/
def coneChain : faceCone.X 1 :=
  (signedCornerInclusion lineChainMap planeChainMap 0).hom cflat +
    (signedLineInclusion lineChainMap planeChainMap 1).hom lflat -
    (signedPlaneInclusion lineChainMap planeChainMap 1).hom pflat

theorem coneChain_d : faceCone.d 1 0 coneChain = 0 := by
  have hc := congrArg (fun f => f.hom cflat)
    (signedCornerInclusion_d_zero lineChainMap planeChainMap)
  have hl := congrArg (fun f => f.hom lflat)
    (signedLineInclusion_d lineChainMap planeChainMap 1 0)
  have hp := congrArg (fun f => f.hom pflat)
    (signedPlaneInclusion_d lineChainMap planeChainMap 1 0)
  change faceCone.d 1 0 ((signedCornerInclusion _ _ 0).hom cflat) =
    (signedLineInclusion _ _ 0).hom ((lineChainMap.f 0).hom cflat) -
      (signedPlaneInclusion _ _ 0).hom ((planeChainMap.f 0).hom cflat) at hc
  change faceCone.d 1 0 ((signedLineInclusion _ _ 1).hom lflat) =
    (signedLineInclusion _ _ 0).hom ((lineChains.d 1 0).hom lflat) at hl
  change faceCone.d 1 0 ((signedPlaneInclusion _ _ 1).hom pflat) =
    (signedPlaneInclusion _ _ 0).hom ((planeChains.d 1 0).hom pflat) at hp
  change faceCone.d 1 0 ((signedLineInclusion _ _ 1).hom lflat) =
    (signedLineInclusion _ _ 0).hom (((underlyingChains (TopCat.of LineFaceSum)).d 1 0).hom lflat) at hl
  change faceCone.d 1 0 ((signedPlaneInclusion _ _ 1).hom pflat) =
    (signedPlaneInclusion _ _ 0).hom (((underlyingChains (TopCat.of PlaneFaceSum)).d 1 0).hom pflat) at hp
  rw [d_lflat, map_neg] at hl
  rw [d_pflat, map_neg] at hp
  have hzero (x y : faceCone.X 0) : (x - y) + (-x) - (-y) = 0 := by abel
  erw [coneChain, map_sub, map_add, hc, hl, hp]
  exact hzero _ _

/-- The hexagon as a degree-one cycle of the geometric face cone. -/
def coneCycle : faceCone.cycles 1 :=
  (faceCone.sc 1).cyclesMk coneChain (by
    change faceCone.d 1 ((ComplexShape.down ℕ).next 1) coneChain = 0
    rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
    exact coneChain_d)

theorem coneCycle_value : faceCone.iCycles 1 coneCycle = coneChain :=
  (faceCone.sc 1).i_cyclesMk _ _


/-! ### The edge of the hexagon cycle -/

theorem coneChain_first : (CofiberSequence.first faceArrow 0).hom coneChain = cflat := by
  have hc : signedCornerInclusion lineChainMap planeChainMap 0 ≫
      CofiberSequence.first faceArrow 0 = 𝟙 _ :=
    homotopyCofiber.inlX_fstX faceArrow 0 1 rfl
  have hl : signedLineInclusion lineChainMap planeChainMap 1 ≫
      CofiberSequence.first faceArrow 0 = 0 := by
    unfold signedLineInclusion CofiberSequence.first
    erw [Category.assoc, homotopyCofiber.inrX_fstX, comp_zero]
  have hp : signedPlaneInclusion lineChainMap planeChainMap 1 ≫
      CofiberSequence.first faceArrow 0 = 0 := by
    unfold signedPlaneInclusion CofiberSequence.first
    erw [Category.assoc, homotopyCofiber.inrX_fstX, comp_zero]
  have hca := congrArg (fun f => f.hom cflat) hc
  have hla := congrArg (fun f => f.hom lflat) hl
  have hpa := congrArg (fun f => f.hom pflat) hp
  change (CofiberSequence.first faceArrow 0).hom
    ((signedCornerInclusion _ _ 0).hom cflat) = cflat at hca
  change (CofiberSequence.first faceArrow 0).hom
    ((signedLineInclusion _ _ 1).hom lflat) = 0 at hla
  change (CofiberSequence.first faceArrow 0).hom
    ((signedPlaneInclusion _ _ 1).hom pflat) = 0 at hpa
  erw [coneChain, map_sub, map_add, hca, hla, hpa, add_zero, sub_zero]

/-- The literal MV edge of the hexagon cone cycle is minus the augmentation of its corner. -/
theorem coneCycle_edge :
    boundaryEdgeMap (homologyMap faceConeToBoundary 1 (faceCone.homologyπ 1 coneCycle)) =
      -(flagAugmentation.hom cflat) := by
  have h := congrArg (fun f => f.hom coneCycle) geometricCone_boundary_edge_projection
  change boundaryEdgeMap (homologyMap faceConeToBoundary 1 (faceCone.homologyπ 1 coneCycle)) =
    -(flagAugmentation.hom ((CofiberSequence.first faceArrow 0).hom
      (faceCone.iCycles 1 coneCycle))) at h
  rw [coneCycle_value, coneChain_first] at h
  exact h

theorem flagAugmentation_cornerPt (k : ℕ) :
    flagAugmentation.hom (sing (TopCat.of CornerFaceSum) (cornerPt k)) =
      MonoidAlgebra.single (flagLabel (hexW k)) (1 : ℚ) := by
  have h := flagAugmentation_single (cornerPt k) 1
  rw [degreeLinearEquiv_single] at h
  exact h

/-- The flag augmentation as a plain linear map on the underlying singular chains. -/
def faLin : (underlyingChains (TopCat.of CornerFaceSum)).X 0 →ₗ[ℚ] MonoidAlgebra ℚ Flag :=
  flagAugmentation.hom.toLinearMap

theorem flagAugmentation_cflat :
    flagAugmentation.hom cflat =
      -(MonoidAlgebra.single (flagLabel (hexW 0)) (1 : ℚ) - MonoidAlgebra.single (flagLabel (hexW 1)) 1 +
        MonoidAlgebra.single (flagLabel (hexW 2)) 1 - MonoidAlgebra.single (flagLabel (hexW 3)) 1 +
        MonoidAlgebra.single (flagLabel (hexW 4)) 1 - MonoidAlgebra.single (flagLabel (hexW 5)) 1) := by
  change faLin cflat = _
  have h : ∀ k, faLin (sing (TopCat.of CornerFaceSum) (cornerPt k)) =
      MonoidAlgebra.single (flagLabel (hexW k)) (1 : ℚ) := flagAugmentation_cornerPt
  simp only [cflat, map_neg, map_add, map_sub, h]

/-- The hexagon class has the alternating sum of the six chamber flags as MV edge. -/
theorem coneCycle_edge_flags :
    boundaryEdgeMap (homologyMap faceConeToBoundary 1 (faceCone.homologyπ 1 coneCycle)) =
      MonoidAlgebra.single (flagLabel (hexW 0)) (1 : ℚ) - MonoidAlgebra.single (flagLabel (hexW 1)) 1 +
        MonoidAlgebra.single (flagLabel (hexW 2)) 1 - MonoidAlgebra.single (flagLabel (hexW 3)) 1 +
        MonoidAlgebra.single (flagLabel (hexW 4)) 1 - MonoidAlgebra.single (flagLabel (hexW 5)) 1 := by
  rw [coneCycle_edge, flagAugmentation_cflat, neg_neg]


/-! ### From the cone cycle to the chain of the flat in the bordification -/

open TernaryPoly.EquivariantSingularMayerVietoris TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularBoundaryRestriction

/-- The forgetful continuous map from the sum of closed line faces to the bordification. -/
def lineToGlued : TopCat.of LineFaceSum ⟶ TopCat.of Glued :=
  TopCat.ofHom ⟨fun x => x.2.val, continuous_sigma (fun _ => continuous_subtype_val)⟩

/-- The forgetful continuous map from the sum of closed plane faces to the bordification. -/
def planeToGlued : TopCat.of PlaneFaceSum ⟶ TopCat.of Glued :=
  TopCat.ofHom ⟨fun x => x.2.val, continuous_sigma (fun _ => continuous_subtype_val)⟩

theorem lineToGlued_equivariant (g : principalSix) (x : LineFaceSum) :
    lineToGlued (g • x) = g • lineToGlued x :=
  lineFaceSum_smul_val g x

theorem planeToGlued_equivariant (g : principalSix) (x : PlaneFaceSum) :
    planeToGlued (g • x) = g • planeToGlued x :=
  planeFaceSum_smul_val g x

abbrev leftCover := leftToCover principalSix ambient lineOpen planeOpen lineOpen_invariant
  planeOpen_invariant opens_cover

abbrev rightCover := rightToCover principalSix ambient lineOpen planeOpen lineOpen_invariant
  planeOpen_invariant opens_cover

theorem smallEquiv_hom_eq : smallEquiv.hom = smallInclusion principalSix ambient _
    (twoSetCover_invariant principalSix ambient lineOpen planeOpen lineOpen_invariant
      planeOpen_invariant opens_cover) :=
  smallHomotopyEquiv_hom _ _ _ _

theorem lineToOpen_chain :
    lineToOpen ≫ leftCover ≫ smallEquiv.hom ≫ upstairsBoundaryChainMap =
      SingularCoverNaturality.chainMap lineToGlued lineToGlued_equivariant := by
  rw [smallEquiv_hom_eq]
  apply HomologicalComplex.hom_ext
  intro n
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  have hΦ : lineToGlued = lineInclusion ≫ SphereOddDegree.sInclusion
      (UpstairsLine : Set BoundaryCover) ≫ boundaryInclusion := by
    ext x
    rfl
  have h := congrArg (fun F => ((SingularCoverNaturality.underlyingMap F).f n).hom c) hΦ
  simp only [SingularCoverNaturality.underlyingMap, Functor.map_comp, HomologicalComplex.comp_f,
    ModuleCat.hom_comp] at h
  exact h.symm

theorem planeToOpen_chain :
    planeToOpen ≫ rightCover ≫ smallEquiv.hom ≫ upstairsBoundaryChainMap =
      SingularCoverNaturality.chainMap planeToGlued planeToGlued_equivariant := by
  rw [smallEquiv_hom_eq]
  apply HomologicalComplex.hom_ext
  intro n
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  have hΦ : planeToGlued = planeInclusion ≫ SphereOddDegree.sInclusion
      (UpstairsPlane : Set BoundaryCover) ≫ boundaryInclusion := by
    ext x
    rfl
  have h := congrArg (fun F => ((SingularCoverNaturality.underlyingMap F).f n).hom c) hΦ
  simp only [SingularCoverNaturality.underlyingMap, Functor.map_comp, HomologicalComplex.comp_f,
    ModuleCat.hom_comp] at h
  exact h.symm

theorem inl_facesToOpen_g : (biprod.inl : lineChains ⟶ lineChains ⊞ planeChains) ≫ facesToOpen ≫
    mvComplex.g = lineToOpen ≫ leftCover := by
  have h1 : (biprod.inl : lineChains ⟶ lineChains ⊞ planeChains) ≫ facesToOpen =
      lineToOpen ≫ (biprod.inl : leftComplex ⟶ leftComplex ⊞ rightComplex) :=
    biprod.inl_map _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ mvComplex.g) h1).trans
    ((Category.assoc _ _ _).trans (congrArg (fun m => lineToOpen ≫ m) (biprod.inl_desc _ _))))

theorem inr_facesToOpen_g : (biprod.inr : planeChains ⟶ lineChains ⊞ planeChains) ≫ facesToOpen ≫
    mvComplex.g = planeToOpen ≫ rightCover := by
  have h1 : (biprod.inr : planeChains ⟶ lineChains ⊞ planeChains) ≫ facesToOpen =
      planeToOpen ≫ (biprod.inr : rightComplex ⟶ leftComplex ⊞ rightComplex) :=
    biprod.inr_map _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ mvComplex.g) h1).trans
    ((Category.assoc _ _ _).trans (congrArg (fun m => planeToOpen ≫ m) (biprod.inr_desc _ _))))

theorem signedLine_faceCone (n : ℕ) :
    signedLineInclusion lineChainMap planeChainMap n ≫ faceConeToBoundary.f n =
      (lineToOpen ≫ leftCover ≫ smallEquiv.hom).f n := by
  have h := congrArg (fun m => (biprod.inl : lineChains ⟶ lineChains ⊞ planeChains).f n ≫ m.f n)
    faceConeToBoundary_inr
  have h2 := congrArg (fun m => (m ≫ smallEquiv.hom).f n) inl_facesToOpen_g
  simp only [HomologicalComplex.comp_f, Category.assoc] at h h2
  exact h.trans h2

theorem signedPlane_faceCone (n : ℕ) :
    signedPlaneInclusion lineChainMap planeChainMap n ≫ faceConeToBoundary.f n =
      (planeToOpen ≫ rightCover ≫ smallEquiv.hom).f n := by
  have h := congrArg (fun m => (biprod.inr : planeChains ⟶ lineChains ⊞ planeChains).f n ≫ m.f n)
    faceConeToBoundary_inr
  have h2 := congrArg (fun m => (m ≫ smallEquiv.hom).f n) inr_facesToOpen_g
  simp only [HomologicalComplex.comp_f, Category.assoc] at h h2
  exact h.trans h2

theorem lineInclusion_chain (n : ℕ) (c : lineChains.X n) :
    (upstairsBoundaryChainMap.f n).hom
      ((faceConeToBoundary.f n).hom ((signedLineInclusion lineChainMap planeChainMap n).hom c)) =
        ((SingularCoverNaturality.chainMap lineToGlued lineToGlued_equivariant).f n).hom c := by
  have h := congrArg (fun m => (m.f n).hom c) lineToOpen_chain
  have h2 := congrArg (fun m => ((m ≫ upstairsBoundaryChainMap.f n).hom c)) (signedLine_faceCone n)
  simp only [HomologicalComplex.comp_f, Category.assoc] at h h2
  exact h2.trans h

theorem planeInclusion_chain (n : ℕ) (c : planeChains.X n) :
    (upstairsBoundaryChainMap.f n).hom
      ((faceConeToBoundary.f n).hom ((signedPlaneInclusion lineChainMap planeChainMap n).hom c)) =
        ((SingularCoverNaturality.chainMap planeToGlued planeToGlued_equivariant).f n).hom c := by
  have h := congrArg (fun m => (m.f n).hom c) planeToOpen_chain
  have h2 := congrArg (fun m => ((m ≫ upstairsBoundaryChainMap.f n).hom c)) (signedPlane_faceCone n)
  simp only [HomologicalComplex.comp_f, Category.assoc] at h h2
  exact h2.trans h


/-- The image of the hexagon cone chain in the singular chains of the boundary. -/
def hexBoundaryChain : boundaryChains.X 1 := (faceConeToBoundary.f 1).hom coneChain


/-! ### The relative class of the flat and its boundary -/

theorem lineToGlued_lineArc (k : ℕ) :
    ((SingularCoverNaturality.underlyingMap lineToGlued).f 1).hom (sing _ (lineArc k)) =
      sing (TopCat.of Glued) (seg (fk k) pv pb) := by
  have h := congrArg (fun m => m.hom (1 : ℚ))
    (SingularCoverNaturality.generator_map lineToGlued 1 (lineArc k))
  have hs : (TopCat.toSSet.map lineToGlued).app _ (lineArc k) = seg (fk k) pv pb := by
    apply ((TopCat.of Glued).toSSetObjEquiv _).injective
    exact ContinuousMap.ext (fun z => rfl)
  rw [hs] at h
  exact h

theorem planeToGlued_planeArc (k : ℕ) :
    ((SingularCoverNaturality.underlyingMap planeToGlued).f 1).hom (sing _ (planeArc k)) =
      sing (TopCat.of Glued) (seg (fk k) pv pa) := by
  have h := congrArg (fun m => m.hom (1 : ℚ))
    (SingularCoverNaturality.generator_map planeToGlued 1 (planeArc k))
  have hs : (TopCat.toSSet.map planeToGlued).app _ (planeArc k) = seg (fk k) pv pa := by
    apply ((TopCat.of Glued).toSSetObjEquiv _).injective
    exact ContinuousMap.ext (fun z => rfl)
  rw [hs] at h
  exact h

/-- The image in the singular chains of the bordification of the boundary chain of the hexagon
cone cycle is the hexagon of twelve arcs. -/
theorem hexBoundaryChain_upstairs :
    (upstairsBoundaryChainMap.f 1).hom hexBoundaryChain = hexBoundary := by
  have hc : (faceConeToBoundary.f 1).hom ((signedCornerInclusion lineChainMap planeChainMap 0).hom cflat) = 0 := by
    have := congrArg (fun f => f.hom cflat) (frozenConeMap_inl 0)
    exact this
  have e : hexBoundaryChain =
      (faceConeToBoundary.f 1).hom ((signedLineInclusion lineChainMap planeChainMap 1).hom lflat) -
        (faceConeToBoundary.f 1).hom ((signedPlaneInclusion lineChainMap planeChainMap 1).hom pflat) := by
    unfold hexBoundaryChain
    erw [coneChain, map_sub, map_add, hc, zero_add]
  rw [e]
  erw [map_sub, lineInclusion_chain, planeInclusion_chain]
  change ((SingularCoverNaturality.underlyingMap lineToGlued).f 1).hom lflat -
    ((SingularCoverNaturality.underlyingMap planeToGlued).f 1).hom pflat = _
  simp only [lflat, pflat, map_neg, map_add, map_sub, lineToGlued_lineArc, planeToGlued_planeArc,
    hexBoundary]
  abel

end TernaryPeriodPolynomials.Argument.Lemma33
