module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.ClassStd
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KSeries
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.UnfoldReal
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.Face
public import TernaryPeriodPolynomials.EisensteinSeries.Class.CoefTwist
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.LineFaces
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.Reflected

@[expose] public section


/-!
# `LineCuspBridge`: the line restriction of the classical series at every line cusp, from the standard line face of the series at the composed cusp

Formalized by Claude Sonnet 5.5.

For `h ∈ SL₃(ℤ)` the line cusp `h⁻¹ Q h` has the group `Γ_{h⁻¹Qh} = gammaNQAt N h`, acting on the face model `e(P)` through `p ↦ ȷ(h p h⁻¹) ∈ Γ_P` (`lineAtHom`), and
`x ↦ h⁻¹ · ȷ̃(i_P x)` maps the face equivariantly into `Ω` (`lineCuspMap`).
* `lineCuspForm`, `lineCuspForm_class`, `toPoly_lineCuspForm_basis`: the pullback to this face of a closed `Γ(N)`-equivariant form, its class (= group restriction), its coordinates.
* `lineCuspForm_eq_twist`: for the series of seed type `b` at the cusp `h'`, the pullback is the `ρ(h⁻¹)`-twist of the STANDARD line-face pullback of the series at `h' h⁻¹` (the `seriesFormK_comp`, `fPull_comp`).
* `lineCusp_class_real`: the same at the level of real classes (`comapInvG`, `deRhamClass_comapInvG`, `intertwines_rhoAtQ`, `deRhamClass_twist`).
* `lineAtMor`, `rLine_cxGen`, `cx_lineCusp_transport`: the complex coefficient transport and the compatibility of complexification with restriction and transport.
* **`rLine_series_cusp`**: `rLine N n h (ℰ^b_{h'}) = (lineAtHom, lineAtMor)_* (complexified class of lineFaceForm of ℰ^b_{h' h⁻¹})` for every `h, h'` and either seed type.
* `lineFaceForm_class_eq_avg`: the class of the standard line-face pullback equals that of its radical average (the `lineAvgK_coeff` gives the coordinates of the average).
-/

open scoped MatrixGroups ContDiff
open MvPolynomial
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open TernaryPeriodPolynomials.Argument.FormSeedBridge TernaryPeriodPolynomials.Argument.FormSeriesModel
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ))

omit [NeZero N] in
/-- `p ↦ ȷ(h p h⁻¹)`: the line group of the cusp `h⁻¹ Q h` onto `Γ_P`. -/
def lineAtHom : gammaNQAt N h →* gammaNP N where
  toFun p := ⟨jmath (h * p.1 * h⁻¹), jmath_mem_gammaNP_iff.2 p.2⟩
  map_one' := by apply Subtype.ext; simp [jmath_one]
  map_mul' p q := by
    apply Subtype.ext
    change jmath (h * (p.1 * q.1) * h⁻¹) = jmath (h * p.1 * h⁻¹) * jmath (h * q.1 * h⁻¹)
    rw [← jmath_mul]; congr 1; group

omit [NeZero N] in
/-- The inclusion `Γ_{h⁻¹Qh} ↪ Γ(N)`. -/
abbrev inclQ : gammaNQAt N h →* gammaN N := Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp)

/-- The action of `Γ_{h⁻¹Qh}` on the face model `e(P)` through `p ↦ ȷ(h p h⁻¹) ∈ Γ_P`. -/
def lineCuspAction : ZigZag.Action (gammaNQAt N h) faceSet :=
  actionComap (gammaNPlaneData N).action (lineAtHom N h)

/-- The inclusion of the face model of the line cusp `h⁻¹ Q h`: `x ↦ h⁻¹ · ȷ̃(i_P x)`. -/
def lineCuspPt (x : Face) : Fin 5 → ℝ := planeAct (realMat h⁻¹) (jFace x)

theorem contDiffOn_lineCuspPt : ContDiffOn ℝ ∞ (lineCuspPt h) faceSet :=
  (contDiffOn_planeAct _ (det_realMat h⁻¹)).comp contDiffOn_jFace fun _ hx => jPlane_mem (ptOf_mem hx)

/-- **The face model of the line cusp `h⁻¹ Q h` maps equivariantly into `Ω`** along `Γ_{h⁻¹Qh} ↪ Γ(N)`. -/
def lineCuspMap : EquivMap isOpen_faceSet isOpen_Omega (lineCuspAction N h) (gammaAct (gammaN N)) (inclQ N h) where
  φ := lineCuspPt h
  smooth := contDiffOn_lineCuspPt h
  mapsTo _ hx := planeAct_mem (det_realMat h⁻¹) (jPlane_mem (ptOf_mem hx))
  equiv p x hx := by
    have hy : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
    have e1 := (lineFaceMap N).equiv (lineAtHom N h p) x hx
    change planeAct (realMat h⁻¹) (jFace ((gammaNPlaneData N).act (lineAtHom N h p) x)) =
      planeAct (realMat p.1) (planeAct (realMat h⁻¹) (jFace x))
    have e2 : jFace ((gammaNPlaneData N).act (lineAtHom N h p) x) =
        planeAct (realMat (jmath (lineAtHom N h p).1)) (jFace x) := e1
    rw [e2]
    have hq : (realMat (jmath (lineAtHom N h p).1)).det = 1 := det_realMat _
    rw [← planeAct_mul hq hy, ← planeAct_mul (det_realMat h⁻¹) hy, ← realMat_mul, ← realMat_mul]
    congr 2
    change h⁻¹ * jmath (jmath (h * p.1 * h⁻¹)) = p.1 * h⁻¹
    rw [jmath_jmath]; group


variable (n : ℕ)

omit [NeZero N] in
/-- The coefficient representation `E_n` restricted to `Γ_{h⁻¹Qh}` (real model). -/
def rhoAtQ : Representation ℝ (gammaNQAt N h) (Coef n) :=
  (gammaRho (gammaN N) n).comp (inclQ N h)

/-- **The pullback of a closed `Γ(N)`-equivariant form to the face model of the line cusp `h⁻¹Qh`.** -/
def lineCuspForm (W : InvComponents (gammaN N) n) :
    ZigZag.invClosed isOpen_faceSet (lineCuspAction N h) (rhoAtQ N h n) :=
  pullInv (lineCuspMap N h) (fun _ => rfl) W.toInv

omit [NeZero N] in
/-- **The class of the pullback to the face of any line cusp is the group restriction of the class.** -/
theorem lineCuspForm_class (W : InvComponents (gammaN N) n) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (lineCuspAction N h)
        (rhoAtQ N h n) (lineCuspForm N h n W) =
      (groupCohomology.map (inclQ N h)
          (resMor (inclQ N h) (rhoAtQ N h n) (gammaRho (gammaN N) n) (fun _ => rfl)) 2).hom
        (ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct (gammaN N))
          (gammaRho (gammaN N) n) W.toInv) :=
  EisensteinClass.deRhamClass_natural (lineCuspMap N h) convex_faceSet faceSet_nonempty convex_Omega
    Omega_nonempty (fun _ => rfl) W.toInv

omit [NeZero N] in
/-- Coordinates of the pullback to the face of the line cusp `h⁻¹Qh`. -/
theorem toPoly_lineCuspForm_basis (W : InvComponents (gammaN N) n) {x : Face} (hx : x ∈ faceSet)
    (i j : Fin 4) :
    Coef.toPoly (((lineCuspForm N h n W : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
        ![Pi.single i 1, Pi.single j 1]) =
      fPull (lineCuspPt h) (fun y a b => Coef.toPoly (W.comp y a b)) x i j := by
  have hΩ : lineCuspPt h x ∈ Omega := planeAct_mem (det_realMat h⁻¹) (jPlane_mem (ptOf_mem hx))
  change Coef.toPoly ((pullBack isOpen_faceSet (lineCuspMap N h).smooth (lineCuspMap N h).mapsTo 2
    W.form : RawForm Face (Coef n) 2) x _) = _
  rw [pullBack_apply isOpen_faceSet _ _ _ hx]
  change Coef.toPoly (((W.form : RawForm (Fin 5 → ℝ) (Coef n) 2) (lineCuspPt h x)).compContinuousLinearMap
    (fderiv ℝ (lineCuspPt h) x) ![Pi.single i 1, Pi.single j 1]) = _
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, W.form_apply hΩ]
  have : (⇑(fderiv ℝ (lineCuspPt h) x) ∘ ![Pi.single i 1, Pi.single j 1]) =
      ![fderiv ℝ (lineCuspPt h) x (Pi.single i 1), fderiv ℝ (lineCuspPt h) x (Pi.single j 1)] := by
    funext k; fin_cases k <;> rfl
  rw [this, InvComponents.raw, altCLM_apply, altRaw_apply_of_antisymm _ (W.anti _),
    toPoly_finsetSum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [toPoly_finsetSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.coe_smul, Coef.toPoly_smul]
  simp

omit [NeZero N] in
theorem fPull_congr_at (Φ : Face → Fin 5 → ℝ) (W W' : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (x : Face) (hW : ∀ a b, W (Φ x) a b = W' (Φ x) a b) (i j : Fin 4) :
    fPull Φ W x i j = fPull Φ W' x i j := by
  unfold fPull
  simp only [hW]

omit [NeZero N] in
theorem rho_fPull (G : Matrix (Fin 3) (Fin 3) ℝ) (Φ : Face → Fin 5 → ℝ)
    (W : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (x : Face) (i j : Fin 4) :
    rho G (fPull Φ W x i j) = fPull Φ (fun y a b => rho G (W y a b)) x i j := by
  unfold fPull
  rw [rho_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rho_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rho_C_mul]

/-- **Cusp-twist identity for the line faces.**  The pullback to the face model of the line cusp `h⁻¹Qh` of the series (type `b`) at the cusp `h'` is the
`ρ(h⁻¹)`-twist of the standard line-face pullback of the series at the cusp `k = h' h⁻¹`. -/
theorem lineCuspForm_eq_twist (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) (b : Bool) (h' : SL(3, ℤ)) :
    ((lineCuspForm N h n (planeEisensteinAtComponents b (CuspData.ofSL h') (gammaN N) (leviGroup N) n f hn
        (leviInCusp_gammaN N h')) : ZigZag.invClosed isOpen_faceSet (lineCuspAction N h) (rhoAtQ N h n)) :
          Form (F := Coef n) faceSet 2) =
      ZigZag.twForm (rhoOfSL n h⁻¹) 2
        ((lineFaceForm N n (planeEisensteinAtComponents b (CuspData.ofSL (h' * h⁻¹)) (gammaN N) (leviGroup N) n f hn
          (leviInCusp_gammaN N (h' * h⁻¹))).toInv : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action (rhoQ N n)) :
            Form (F := Coef n) faceSet 2) := by
  apply Form.ext
  intro x hx
  rw [ZigZag.twForm_apply, coefficientFormMap_apply]
  apply ext2Face
  intro i j
  apply Coef.toPoly_injective
  have hy : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  rw [toPoly_lineCuspForm_basis N h n _ hx i j]
  show _ = Coef.toPoly (rhoOfSL n h⁻¹ _)
  rw [toPoly_rhoOfSL]
  refine Eq.trans ?_ (congrArg (rho (realMat h⁻¹)) (toPoly_lineFaceForm_basis N n
    (planeEisensteinAtComponents b (CuspData.ofSL (h' * h⁻¹)) (gammaN N) (leviGroup N) n f hn
      (leviInCusp_gammaN N (h' * h⁻¹))) hx i j)).symm
  rw [rho_fPull]
  have hc : lineCuspPt h = planeAct (realMat h⁻¹) ∘ jFace := rfl
  rw [hc, fPull_comp jFace (planeAct (realMat h⁻¹)) _ x (differentiableAt_jFace hx)
    (differentiableAt_planeAct (det_realMat _) hy)]
  refine fPull_congr_at jFace _ _ x (fun a c => ?_) i j
  exact seriesFormK_comp N n f hn b h h' hy a c


section Comap

variable {G G' : Type} [Group G] [Group G'] (A : ZigZag.Action G faceSet) (ρ : Representation ℝ G (Coef n))
  (β : G' →* G)

/-- An invariant closed form of `(A, ρ)` is an invariant closed form of the pulled-back data. -/
def comapInvG (F : ZigZag.invClosed isOpen_faceSet A ρ) :
    ZigZag.invClosed isOpen_faceSet (actionComap A β) (ρ.comp β) :=
  ⟨F.1, F.2.1, fun g => F.2.2 (β g)⟩

/-- The identity of the face as an equivariant map along `β`. -/
def idEquivMap : EquivMap isOpen_faceSet isOpen_faceSet (actionComap A β) A β where
  φ := id
  smooth := contDiffOn_id
  mapsTo _ hx := hx
  equiv _ _ _ := rfl

theorem pullInv_id_eq (F : ZigZag.invClosed isOpen_faceSet A ρ) :
    pullInv (idEquivMap A β) (fun _ => rfl) F = comapInvG n A ρ β F := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change (pullBack isOpen_faceSet (idEquivMap A β).smooth (idEquivMap A β).mapsTo 2 F.1 :
    RawForm Face (Coef n) 2) x = _
  rw [pullBack_apply isOpen_faceSet _ _ _ hx]
  exact pullRaw_id _ x

theorem deRhamClass_comapInvG (F : ZigZag.invClosed isOpen_faceSet A ρ) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (actionComap A β) (ρ.comp β)
        (comapInvG n A ρ β F) =
      (groupCohomology.map β (resMor β (ρ.comp β) ρ (fun _ => rfl)) 2).hom
        (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty A ρ F) := by
  rw [← pullInv_id_eq]
  exact EisensteinClass.deRhamClass_natural (idEquivMap A β) convex_faceSet faceSet_nonempty convex_faceSet
    faceSet_nonempty (fun _ => rfl) F

end Comap

omit [NeZero N] in
/-- `ρ(h⁻¹)` intertwines the transported standard line representation with the restricted one. -/
theorem intertwines_rhoAtQ :
    Intertwines (rhoOfSL n h⁻¹) ((rhoQ N n).comp (lineAtHom N h)) (rhoAtQ N h n) := by
  intro p v
  apply Coef.toPoly_injective
  have e1 : Coef.toPoly ((rhoAtQ N h n p) (rhoOfSL n h⁻¹ v)) =
      rho (realMat p.1) (rho (realMat h⁻¹) (Coef.toPoly v)) := by
    change Coef.toPoly (gammaRho (gammaN N) n (inclQ N h p) (rhoOfSL n h⁻¹ v)) = _
    rw [toPoly_gammaRho, toPoly_rhoOfSL]
    rfl
  have e2 : Coef.toPoly (rhoOfSL n h⁻¹ (((rhoQ N n).comp (lineAtHom N h)) p v)) =
      rho (realMat h⁻¹) (rho (realMat (h * p.1 * h⁻¹)) (Coef.toPoly v)) := by
    rw [toPoly_rhoOfSL]
    refine congrArg (rho (realMat h⁻¹)) ((toPoly_rhoQ N n (lineAtHom N h p) v).trans ?_)
    change rho (realMat (jmath (jmath (h * p.1 * h⁻¹)))) _ = _
    rw [jmath_jmath]
  rw [e1, e2, rho_mul, rho_mul, ← realMat_mul, ← realMat_mul]
  refine congrArg (fun m : SL(3, ℤ) => rho (realMat m) (Coef.toPoly v)) ?_
  group


/-- **The restriction of the real series class to the line group of the cusp `h⁻¹Qh`** is the `ρ(h⁻¹)`-twisted `lineAtHom`-pullback of the
class of the standard line-face pullback of the series at the cusp `k = h' h⁻¹` (real coefficients). -/
theorem lineCusp_class_real (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) (b : Bool) (h' : SL(3, ℤ)) :
    (groupCohomology.map (inclQ N h)
        (resMor (inclQ N h) (rhoAtQ N h n) (gammaRho (gammaN N) n) (fun _ => rfl)) 2).hom
      (ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct (gammaN N)) (gammaRho (gammaN N) n)
        (planeEisensteinAtComponents b (CuspData.ofSL h') (gammaN N) (leviGroup N) n f hn
          (leviInCusp_gammaN N h')).toInv) =
    (groupCohomology.map (MonoidHom.id (gammaNQAt N h)) (twMor (intertwines_rhoAtQ N h n)) 2).hom
      ((groupCohomology.map (lineAtHom N h)
          (resMor (lineAtHom N h) ((rhoQ N n).comp (lineAtHom N h)) (rhoQ N n) (fun _ => rfl)) 2).hom
        (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
          (lineFaceForm N n (planeEisensteinAtComponents b (CuspData.ofSL (h' * h⁻¹)) (gammaN N) (leviGroup N) n f hn
            (leviInCusp_gammaN N (h' * h⁻¹))).toInv))) := by
  have e : lineCuspForm N h n (planeEisensteinAtComponents b (CuspData.ofSL h') (gammaN N) (leviGroup N) n f hn
        (leviInCusp_gammaN N h')) =
      twInv (intertwines_rhoAtQ N h n)
        (comapInvG n (gammaNPlaneData N).action (rhoQ N n) (lineAtHom N h)
          (lineFaceForm N n (planeEisensteinAtComponents b (CuspData.ofSL (h' * h⁻¹)) (gammaN N) (leviGroup N) n f hn
            (leviInCusp_gammaN N (h' * h⁻¹))).toInv)) :=
    Subtype.ext (lineCuspForm_eq_twist N h n f hn b h')
  refine (lineCuspForm_class N h n _).symm.trans ?_
  rw [e]
  refine (EisensteinClass.deRhamClass_twist convex_faceSet faceSet_nonempty (intertwines_rhoAtQ N h n) _).trans ?_
  exact congrArg (fun x => (groupCohomology.map (MonoidHom.id (gammaNQAt N h)) (twMor (intertwines_rhoAtQ N h n)) 2).hom x)
    (deRhamClass_comapInvG n (gammaNPlaneData N).action (rhoQ N n) (lineAtHom N h) _)


/-- The complex coefficient comparison `E_n|_{Γ_P}(through ȷ) → E_n|_{Γ_{h⁻¹Qh}}`, `v ↦ ρ(h⁻¹) v`, along `lineAtHom`. -/
def lineAtMor : Rep.res (lineAtHom N h) (Rep.of (rhoQC N n)) ⟶ lineFaceRep N h n :=
  Rep.ofHom ⟨(faceT h n).toLinearMap, fun p => LinearMap.ext fun v =>
    (congrArg (faceT h n) (by
      change ambRep n (jmath (jmath (h * p.1 * h⁻¹))) v = ambRep n (h * p.1 * h⁻¹) v
      rw [jmath_jmath])).trans (lineFaceT_intertwines N h n p v)⟩

omit [NeZero N] in
/-- Complex restriction to the line group of the cusp `h⁻¹Qh` commutes with complexification. -/
theorem rLine_cxGen (x : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n))) :
    rLine N n h (cxGen (gammaRho (gammaN N) n) ((ambRep n).comp (gammaN N).subtype) (fun _ _ => rfl) x) =
      cxGen (rhoAtQ N h n) ((ambRep n).comp (gammaNQAt N h).subtype) (fun _ _ => rfl)
        ((groupCohomology.map (inclQ N h) (resMor (inclQ N h) (rhoAtQ N h n) (gammaRho (gammaN N) n) (fun _ => rfl)) 2).hom x) := by
  have e := cxGen_map (rhoAtQ N h n) ((ambRep n).comp (gammaNQAt N h).subtype) (fun _ _ => rfl)
    (gammaRho (gammaN N) n) ((ambRep n).comp (gammaN N).subtype) (fun _ _ => rfl) (inclQ N h) (fun _ => rfl)
    (fun _ => rfl) x
  refine Eq.trans ?_ e.symm
  generalize cxGen (gammaRho (gammaN N) n) ((ambRep n).comp (gammaN N).subtype) (fun _ _ => rfl) x = c
  induction c using groupCohomology.H2_induction_on with
  | h z =>
    have e1 : rLine N n h (groupCohomology.H2π (gammaNRepAll N n) z) =
        groupCohomology.H2π (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp)) (gammaNRepAll N n))
          (twoCocycleRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp)) (gammaNRepAll N n) z) :=
      twoCohomologyRestriction_apply _ _ z
    refine e1.trans ?_
    refine Eq.trans ?_ (groupCohomology.H2π_comp_map_apply _ _ _).symm
    rfl

/-- Complexification intertwines the real and the complex coefficient transports along `lineAtHom`. -/
theorem cx_lineCusp_transport (y : groupCohomology.H2 (Rep.of (rhoQ N n))) :
    cxGen (rhoAtQ N h n) ((ambRep n).comp (gammaNQAt N h).subtype) (fun _ _ => rfl)
        ((groupCohomology.map (MonoidHom.id (gammaNQAt N h)) (twMor (intertwines_rhoAtQ N h n)) 2).hom
          ((groupCohomology.map (lineAtHom N h)
            (resMor (lineAtHom N h) ((rhoQ N n).comp (lineAtHom N h)) (rhoQ N n) (fun _ => rfl)) 2).hom y)) =
      (groupCohomology.map (lineAtHom N h) (lineAtMor N h n) 2).hom
        (cxGen (rhoQ N n) (rhoQC N n) (fun _ _ => rfl) y) := by
  induction y using groupCohomology.H2_induction_on with
  | h z =>
    have h1 := groupCohomology.H2π_comp_map_apply (lineAtHom N h)
      (resMor (lineAtHom N h) ((rhoQ N n).comp (lineAtHom N h)) (rhoQ N n) (fun _ => rfl)) z
    have h2 := groupCohomology.H2π_comp_map_apply (MonoidHom.id (gammaNQAt N h)) (twMor (intertwines_rhoAtQ N h n))
      ((groupCohomology.mapCocycles₂ (lineAtHom N h)
        (resMor (lineAtHom N h) ((rhoQ N n).comp (lineAtHom N h)) (rhoQ N n) (fun _ => rfl))).hom z)
    have h3 := cxGen_H2π (rhoAtQ N h n) ((ambRep n).comp (gammaNQAt N h).subtype) (fun _ _ => rfl)
      ((groupCohomology.mapCocycles₂ (MonoidHom.id (gammaNQAt N h)) (twMor (intertwines_rhoAtQ N h n))).hom
        ((groupCohomology.mapCocycles₂ (lineAtHom N h)
          (resMor (lineAtHom N h) ((rhoQ N n).comp (lineAtHom N h)) (rhoQ N n) (fun _ => rfl))).hom z))
    have h4 := cxGen_H2π (rhoQ N n) (rhoQC N n) (fun _ _ => rfl) z
    have h5 := groupCohomology.H2π_comp_map_apply (lineAtHom N h) (lineAtMor N h n)
      (cxCocyclesGen (rhoQ N n) (rhoQC N n) (fun _ _ => rfl) z)
    refine ((congrArg (fun t => cxGen (rhoAtQ N h n) ((ambRep n).comp (gammaNQAt N h).subtype) (fun _ _ => rfl)
      ((groupCohomology.map (MonoidHom.id (gammaNQAt N h)) (twMor (intertwines_rhoAtQ N h n)) 2).hom t)) h1).trans
      ((congrArg _ h2).trans h3)).trans ?_
    refine Eq.trans ?_ ((congrArg (fun t => (groupCohomology.map (lineAtHom N h) (lineAtMor N h n) 2).hom t) h4).trans h5).symm
    refine congrArg (CategoryTheory.ConcreteCategory.hom (groupCohomology.H2π _)) ?_
    apply Subtype.ext
    funext p
    obtain ⟨a, b⟩ := p
    have hv : ∀ v : Coef n, Coef.val (rhoOfSL n h⁻¹ v) = faceT h n (Coef.val v) := fun v => by
      apply Subtype.ext
      change Coef.toPoly (rhoOfSL n h⁻¹ v) = ((GeneralEisenstein.realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ h⁻¹)
        (Coef.val v) : GeneralEisenstein.HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ)
      rw [toPoly_realCoefficient, mapGL_val]
      exact toPoly_rhoOfSL n h⁻¹ v
    exact hv _


/-- **The line restriction of the complexified series at any cusp, at any line cusp** (`LineCuspBridge`): for `h, h' ∈ SL₃(ℤ)` and either seed type `b`,
`r_{h⁻¹Qh} ℰ^b_{h'}` is the `ρ(h⁻¹)`-twisted pullback along `p ↦ ȷ(h p h⁻¹)` of the complexified class of the standard line-face pullback of the series at the cusp `h' h⁻¹`. -/
theorem rLine_series_cusp (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) (b : Bool) (h' : SL(3, ℤ)) :
    rLine N n h (cxGen (gammaRho (gammaN N) n) ((ambRep n).comp (gammaN N).subtype) (fun _ _ => rfl)
        (eisensteinAtClass b (CuspData.ofSL h') (gammaN N) (leviGroup N) n f hn (leviInCusp_gammaN N h'))) =
      (groupCohomology.map (lineAtHom N h) (lineAtMor N h n) 2).hom
        (cxGen (rhoQ N n) (rhoQC N n) (fun _ _ => rfl)
          (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
            (lineFaceForm N n (planeEisensteinAtInv b (CuspData.ofSL (h' * h⁻¹)) (gammaN N) (leviGroup N) n f hn
              (leviInCusp_gammaN N (h' * h⁻¹)))))) := by
  refine (rLine_cxGen N h n _).trans ?_
  refine (congrArg _ (lineCusp_class_real N h n f hn b h')).trans ?_
  exact cx_lineCusp_transport N h n _


theorem lineFaceForm_class_eq_avg (F : ZigZag.invClosed isOpen_Omega (gammaAct (gammaN N)) (gammaRho (gammaN N) n)) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
        (lineFaceForm N n F) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
        ((lineTwist N n).avInvT (lineFaceForm N n F)) :=
  (lineFaceForm_class N n F).trans (lineFace_avg_class N n F).symm

end TernaryPeriodPolynomials.Argument.FormClassK
