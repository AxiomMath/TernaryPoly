module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cone.Stokes

@[expose] public section


/-!
# Face pairings on classes, generic in the coefficient system

Formalized by Claude Sonnet 5.5.

For `V : Rep ℚ Γ(6)` a **line datum** (`LineDatum V`) is a line 2-cocycle `z` with a primitive `w` of its restriction to the complete flags; its cone cochain is
`(w, z, 0)`; a **plane datum** has cone cochain `(-w, 0, z)`.  The face pairing of two data is the cone pairing `conePair` of their cone cochains on a coinvariant
cycle of the model cone.  Proved, for every coefficient system and every coinvariant cycle:

* `LineDatum.pair_congr`, `PlaneDatum.pair_congr`: the pairing depends only on the cohomology classes `[z]`, `[z']` of the line (plane) cocycles, not on the flag
  primitives `w`, `w'` nor on the representatives (the difference of two cone cochains with cohomologous `z` is a coboundary plus a corner cocycle `(u, 0, 0)`,
  and corner cocycles are orthogonal to pure-type cocycles by `cone_cross_zero`, `conePair_linePlane_zero`);
* `lineDatum_planeDatum_orthogonal`, `planeDatum_lineDatum_orthogonal`: line data and plane data are orthogonal in both orders;
* `lineCone_add`, `planeCone_add`, `lineCone_coboundary`, `planeCone_coboundary`: the linear structure of the lifts.
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

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section Linear

variable {W : Rep.{0} ℚ Γ6}

theorem lineCone_add (w w' : A.X 1 ⟶ W) (z z' : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W) :
    lineCone (w + w') (z + z') = lineCone w z + lineCone w' z' := by
  unfold lineCone
  rw [← map_add]
  congr 1
  simp

theorem planeCone_add (w w' : A.X 1 ⟶ W) (z z' : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) :
    planeCone (w + w') (z + z') = planeCone w z + planeCone w' z' := by
  unfold planeCone
  rw [← map_add]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change -(w + w') = -w + -w'
    abel
  · simp
  · rfl

theorem planeCone_eq_add_corner (w w' : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) :
    planeCone w z = planeCone w' z + lineCone (w' - w) 0 := by
  unfold planeCone lineCone
  rw [← map_add]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change -w = -w' + (w' - w)
    abel
  · simp
  · simp

/-- The cone coboundary of the degree-one line cochain `(0, ζ, 0)`. -/
theorem lineCone_coboundary (ζ : (prodComplex Γ6 RationalGL3 Line).X 1 ⟶ W) :
    coneR.d 2 1 ≫ (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 0).symm (0, ζ, 0) =
      lineCone (flagLineHom.hom.f 1 ≫ ζ) ((prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ ζ) := by
  apply (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1).injective
  rw [cone_coboundary_coordinates]
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 0
      ((signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 0).symm (0, ζ, 0)) = (0, ζ, 0) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc]
  have hc' : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1
      (lineCone (flagLineHom.hom.f 1 ≫ ζ) ((prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ ζ)) =
      (flagLineHom.hom.f 1 ≫ ζ, (prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ ζ, 0) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc']
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change -(resFlag.complex.d 1 0 ≫ (0 : (prodComplex Γ6 RationalGL3 Flag).X 0 ⟶ W)) +
      flagLineHom.hom.f 1 ≫ ζ - flagPlaneHom.hom.f 1 ≫ (0 : (prodComplex Γ6 RationalGL3 Plane).X 1 ⟶ W) = _
    simp
  · rfl
  · change (prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ (0 : (prodComplex Γ6 RationalGL3 Plane).X 1 ⟶ W) = 0
    simp

/-- The cone coboundary of the degree-one plane cochain `(0, 0, ζ)`. -/
theorem planeCone_coboundary (ζ : (prodComplex Γ6 RationalGL3 Plane).X 1 ⟶ W) :
    coneR.d 2 1 ≫ (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 0).symm (0, 0, ζ) =
      planeCone (flagPlaneHom.hom.f 1 ≫ ζ) ((prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ ζ) := by
  apply (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1).injective
  rw [cone_coboundary_coordinates]
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 0
      ((signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 0).symm (0, 0, ζ)) = (0, 0, ζ) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc]
  have hc' : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1
      (planeCone (flagPlaneHom.hom.f 1 ≫ ζ) ((prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ ζ)) =
      (-(flagPlaneHom.hom.f 1 ≫ ζ), 0, (prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ ζ) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc']
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change -(resFlag.complex.d 1 0 ≫ (0 : (prodComplex Γ6 RationalGL3 Flag).X 0 ⟶ W)) +
      flagLineHom.hom.f 1 ≫ (0 : (prodComplex Γ6 RationalGL3 Line).X 1 ⟶ W) - flagPlaneHom.hom.f 1 ≫ ζ = _
    simp
  · change (prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ (0 : (prodComplex Γ6 RationalGL3 Line).X 1 ⟶ W) = 0
    simp
  · rfl

end Linear

section Data

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (v : coneR.X 4)

/-- A line datum: a line 2-cocycle `z` with a flag primitive `w` of its restriction to the flags. -/
structure LineDatum (W : Rep.{0} ℚ Γ6) where
  z : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W
  hz : (prodComplex Γ6 RationalGL3 Line).d 3 2 ≫ z = 0
  w : A.X 1 ⟶ W
  hw : A.d 2 1 ≫ w = flagLineHom.hom.f 2 ≫ z

/-- A plane datum. -/
structure PlaneDatum (W : Rep.{0} ℚ Γ6) where
  z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W
  hz : (prodComplex Γ6 RationalGL3 Plane).d 3 2 ≫ z = 0
  w : A.X 1 ⟶ W
  hw : A.d 2 1 ≫ w = flagPlaneHom.hom.f 2 ≫ z

def LineDatum.cone (d : LineDatum W) : coneR.X 2 ⟶ W := lineCone d.w d.z
def PlaneDatum.cone (d : PlaneDatum W) : coneR.X 2 ⟶ W := planeCone d.w d.z

theorem LineDatum.cone_cocycle (d : LineDatum W) : coneR.d 3 2 ≫ d.cone = 0 :=
  lineCone_cocycle d.w d.z d.hz d.hw

theorem PlaneDatum.cone_cocycle (d : PlaneDatum W) : coneR.d 3 2 ≫ d.cone = 0 :=
  planeCone_cocycle d.w d.z d.hz d.hw

theorem LineDatum.cone_plane (d : LineDatum W) : modelPush.iP 2 ≫ d.cone = 0 := lineCone_plane _ _
theorem PlaneDatum.cone_line (d : PlaneDatum W) : modelPush.iL 2 ≫ d.cone = 0 := planeCone_line _ _

/-- A corner cocycle `(u, 0, 0)`. -/
theorem corner_cocycle (u : A.X 1 ⟶ W) (hu : A.d 2 1 ≫ u = 0) : coneR.d 3 2 ≫ lineCone u 0 = 0 :=
  lineCone_cocycle u 0 (comp_zero) (by rw [hu, comp_zero])

/-- Two line data with cohomologous cocycles differ, as cone cochains, by a coboundary and a corner cocycle. -/
theorem LineDatum.cone_eq_of_cohomologous (d1 d2 : LineDatum W)
    (ζ : (prodComplex Γ6 RationalGL3 Line).X 1 ⟶ W)
    (h : d1.z = d2.z + (prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ ζ) :
    ∃ u : A.X 1 ⟶ W, A.d 2 1 ≫ u = 0 ∧
      d1.cone = (d2.cone + lineCone u 0) +
        coneR.d 2 1 ≫ (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 0).symm (0, ζ, 0) := by
  refine ⟨d1.w - d2.w - flagLineHom.hom.f 1 ≫ ζ, ?_, ?_⟩
  · rw [Preadditive.comp_sub, Preadditive.comp_sub, d1.hw, d2.hw, h, ← Category.assoc,
      ← flagLineHom.hom.comm 2 1]
    simp only [Preadditive.comp_add, Category.assoc]
    abel
  · rw [lineCone_coboundary]
    unfold LineDatum.cone
    rw [← lineCone_add, ← lineCone_add]
    congr 1
    · abel
    · rw [h]
      abel

/-- Two line data with cohomologous cocycles pair equally with any line-type cone cocycle. -/
theorem LineDatum.pair_left_congr (d1 d2 : LineDatum W)
    (ζ : (prodComplex Γ6 RationalGL3 Line).X 1 ⟶ W)
    (h : d1.z = d2.z + (prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ ζ)
    (Y : coneR.X 2 ⟶ W') (hY : coneR.d 3 2 ≫ Y = 0) (hYP : modelPush.iP 2 ≫ Y = 0) (hv : IsCoinvCycle v) :
    conePair π v d1.cone Y = conePair π v d2.cone Y := by
  obtain ⟨u, hu, he⟩ := LineDatum.cone_eq_of_cohomologous d1 d2 ζ h
  have hc : coneR.d 3 2 ≫ (d2.cone + lineCone u 0) = 0 := by
    rw [Preadditive.comp_add, d2.cone_cocycle, corner_cocycle u hu, add_zero]
  have key := pair_cohomologous modelDiagSystem π hc hY _ he (y' := Y) 0 (by simp) v hv
  have e1 : conePair π v d1.cone Y = conePair π v (d2.cone + lineCone u 0) Y := key
  rw [e1, conePair_add_left]
  have e2 : conePair π v (lineCone u 0) Y = 0 :=
    cone_cross_zero π _ _ (corner_cocycle u hu) hY (lineCone_line _ _) hYP v hv
  rw [e2, add_zero]

/-- The same with the second argument varying. -/
theorem LineDatum.pair_right_congr (e1 e2 : LineDatum W')
    (ζ : (prodComplex Γ6 RationalGL3 Line).X 1 ⟶ W')
    (h : e1.z = e2.z + (prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ ζ)
    (X : coneR.X 2 ⟶ W) (hX : coneR.d 3 2 ≫ X = 0) (hXP : modelPush.iP 2 ≫ X = 0) (hv : IsCoinvCycle v) :
    conePair π v X e1.cone = conePair π v X e2.cone := by
  obtain ⟨u, hu, he⟩ := LineDatum.cone_eq_of_cohomologous e1 e2 ζ h
  have hc : coneR.d 3 2 ≫ (e2.cone + lineCone u 0) = 0 := by
    rw [Preadditive.comp_add, e2.cone_cocycle, corner_cocycle u hu, add_zero]
  have key := pair_cohomologous modelDiagSystem π (x := X) (x' := X) (y := e1.cone)
    (y' := e2.cone + lineCone u 0) hX e1.cone_cocycle (0 : coneR.X 1 ⟶ W) (by simp) _ he v hv
  have e1' : conePair π v X e1.cone = conePair π v X (e2.cone + lineCone u 0) := key
  rw [e1', conePair_add_right]
  have e2' : conePair π v X (lineCone u 0) = 0 :=
    conePair_linePlane_zero π v X _ hXP (lineCone_line _ _) hv
  rw [e2', add_zero]

theorem PlaneDatum.cone_eq_of_cohomologous (d1 d2 : PlaneDatum W)
    (ζ : (prodComplex Γ6 RationalGL3 Plane).X 1 ⟶ W)
    (h : d1.z = d2.z + (prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ ζ) :
    ∃ u : A.X 1 ⟶ W, A.d 2 1 ≫ u = 0 ∧
      d1.cone = (d2.cone + lineCone u 0) +
        coneR.d 2 1 ≫ (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 0).symm (0, 0, ζ) := by
  refine ⟨-(d1.w - d2.w - flagPlaneHom.hom.f 1 ≫ ζ), ?_, ?_⟩
  · rw [Preadditive.comp_neg, Preadditive.comp_sub, Preadditive.comp_sub, d1.hw, d2.hw, h, ← Category.assoc,
      ← flagPlaneHom.hom.comm 2 1]
    simp only [Preadditive.comp_add, Category.assoc]
    abel
  · rw [planeCone_coboundary]
    unfold PlaneDatum.cone
    rw [add_right_comm, ← planeCone_add, ← h,
      planeCone_eq_add_corner d1.w (d2.w + flagPlaneHom.hom.f 1 ≫ ζ) d1.z]
    congr 2
    abel

theorem PlaneDatum.pair_left_congr (d1 d2 : PlaneDatum W)
    (ζ : (prodComplex Γ6 RationalGL3 Plane).X 1 ⟶ W)
    (h : d1.z = d2.z + (prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ ζ)
    (Y : coneR.X 2 ⟶ W') (hY : coneR.d 3 2 ≫ Y = 0) (hYL : modelPush.iL 2 ≫ Y = 0) (hv : IsCoinvCycle v) :
    conePair π v d1.cone Y = conePair π v d2.cone Y := by
  obtain ⟨u, hu, he⟩ := PlaneDatum.cone_eq_of_cohomologous d1 d2 ζ h
  have hc : coneR.d 3 2 ≫ (d2.cone + lineCone u 0) = 0 := by
    rw [Preadditive.comp_add, d2.cone_cocycle, corner_cocycle u hu, add_zero]
  have key := pair_cohomologous modelDiagSystem π (x := d1.cone) (x' := d2.cone + lineCone u 0) (y := Y)
    (y' := Y) hc hY _ he (0 : coneR.X 1 ⟶ W') (by simp) v hv
  have e1 : conePair π v d1.cone Y = conePair π v (d2.cone + lineCone u 0) Y := key
  rw [e1, conePair_add_left]
  have e2 : conePair π v (lineCone u 0) Y = 0 :=
    conePair_linePlane_zero π v _ Y (lineCone_plane _ _) hYL hv
  rw [e2, add_zero]

theorem PlaneDatum.pair_right_congr (e1 e2 : PlaneDatum W')
    (ζ : (prodComplex Γ6 RationalGL3 Plane).X 1 ⟶ W')
    (h : e1.z = e2.z + (prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ ζ)
    (X : coneR.X 2 ⟶ W) (hX : coneR.d 3 2 ≫ X = 0) (hXL : modelPush.iL 2 ≫ X = 0) (hv : IsCoinvCycle v) :
    conePair π v X e1.cone = conePair π v X e2.cone := by
  obtain ⟨u, hu, he⟩ := PlaneDatum.cone_eq_of_cohomologous e1 e2 ζ h
  have key := pair_cohomologous modelDiagSystem π (x := X) (x' := X) (y := e1.cone)
    (y' := e2.cone + lineCone u 0) hX e1.cone_cocycle (0 : coneR.X 1 ⟶ W) (by simp) _ he v hv
  have e1' : conePair π v X e1.cone = conePair π v X (e2.cone + lineCone u 0) := key
  rw [e1', conePair_add_right]
  have e2' : conePair π v X (lineCone u 0) = 0 :=
    cone_cross_zero π _ _ hX (corner_cocycle u hu) hXL (lineCone_plane _ _) v hv
  rw [e2', add_zero]

/-- **The line face pairing depends only on the classes of the cocycles, not on the flag primitives.** -/
theorem LineDatum.pair_congr (d1 d2 : LineDatum W) (e1 e2 : LineDatum W')
    (ζ : (prodComplex Γ6 RationalGL3 Line).X 1 ⟶ W)
    (h : d1.z = d2.z + (prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ ζ)
    (ζ' : (prodComplex Γ6 RationalGL3 Line).X 1 ⟶ W')
    (h' : e1.z = e2.z + (prodComplex Γ6 RationalGL3 Line).d 2 1 ≫ ζ') (hv : IsCoinvCycle v) :
    conePair π v d1.cone e1.cone = conePair π v d2.cone e2.cone :=
  (LineDatum.pair_left_congr π v d1 d2 ζ h e1.cone e1.cone_cocycle e1.cone_plane hv).trans
    (LineDatum.pair_right_congr π v e1 e2 ζ' h' d2.cone d2.cone_cocycle d2.cone_plane hv)

/-- The plane analogue. -/
theorem PlaneDatum.pair_congr (d1 d2 : PlaneDatum W) (e1 e2 : PlaneDatum W')
    (ζ : (prodComplex Γ6 RationalGL3 Plane).X 1 ⟶ W)
    (h : d1.z = d2.z + (prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ ζ)
    (ζ' : (prodComplex Γ6 RationalGL3 Plane).X 1 ⟶ W')
    (h' : e1.z = e2.z + (prodComplex Γ6 RationalGL3 Plane).d 2 1 ≫ ζ') (hv : IsCoinvCycle v) :
    conePair π v d1.cone e1.cone = conePair π v d2.cone e2.cone :=
  (PlaneDatum.pair_left_congr π v d1 d2 ζ h e1.cone e1.cone_cocycle e1.cone_line hv).trans
    (PlaneDatum.pair_right_congr π v e1 e2 ζ' h' d2.cone d2.cone_cocycle d2.cone_line hv)

/-- **Orthogonality of the line lifts to the plane lifts, in both orders.** -/
theorem lineDatum_planeDatum_orthogonal (d : LineDatum W) (e : PlaneDatum W') (hv : IsCoinvCycle v) :
    conePair π v d.cone e.cone = 0 :=
  conePair_linePlane_zero π v _ _ d.cone_plane e.cone_line hv

theorem planeDatum_lineDatum_orthogonal (d : PlaneDatum W) (e : LineDatum W') (hv : IsCoinvCycle v) :
    conePair π v d.cone e.cone = 0 :=
  cone_cross_zero π _ _ d.cone_cocycle e.cone_cocycle d.cone_line e.cone_plane v hv

end Data


end TernaryPeriodPolynomials.Argument.GammaNStokes
