module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.BadPlaneFaceBridge
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.GoodPlane
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.GoodLine
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.StandardBadLineMixedCuspidal

@[expose] public section


/-!
# The face library's cusp subgroups at the other three reference faces

Paper: Lemma C.3 (`ar:lem:seed`),: `𝒞_R(E)` consists of the classes of `H¹(L_R, H¹(N_R, E))` whose restrictions at all
rational cusps of the binary Levi vanish.

`BadPlaneFaceBridge` treated the identity (bad) plane.  The level group has three further reference
faces: the standard bad line, the good plane (its image under the duality involution) and the good
line.  In each case the face library's cusp subgroups `faceCusp e` (Levi part of the stabilizer of the
complete flag `e` over the face) are the following subgroups of the Levi, so that `FaceCuspidal` is the
literal mixed cuspidal group `cuspidalFamily`:

* standard bad line, Levi `ℤˣ × Γ₁'(3)` (`binaryArithmeticLevel`): `ℤˣ × binaryCuspLevel F`
  (`leviCusp F`, `F ∈ GL₂(ℚ)`): `mem_faceCusp_badLine_iff`, `badLine_faceCusp_family_eq`,
  `badLine_faceCuspidal_iff`;
* good plane `⟨e₃, e₂⟩`, the same Levi: the cusp subgroup of `e` is that of the dual flag
  `dualEdge e` over the standard line, hence again `leviCusp F`: `mem_faceCusp_goodPlane_iff`,
  `goodPlane_faceCusp_family_eq`, `goodPlane_faceCuspidal_iff`;
* good line `ℚ e₃`, Levi `GL₂(ℤ)`: the flags over it are `w·binaryEdge F` for the long Weyl element
  `w`, and conjugating the Levi by `w` transposes the block, so the cusp subgroup is `cuspGL (J F)`
  with `J` the transposition: `mem_faceCusp_goodLine_iff`, `goodLine_faceCusp_family_eq`,
  `goodLine_faceCuspidal_iff`.

`locallyInner_iff_edge_mem_family` is the corresponding statement for locally inner classes of `H²`
for any face whose family of cusp subgroups is shown equal to an explicit family.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairingFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

section FaceCuspidalFamily

variable {Radical Levi : Type} [Group Radical] [Group Levi] (action : Levi →* MulAut Radical)
  (degree : ℕ) (character : RankOneCharacter) {side : Side} (F : Flags side)
  (ι : SemidirectProduct Radical Levi action ≃* fixedPointLevel rationalLevel F)

/-- A class of the crossed model is in `FaceCuspidal` iff its coordinate is in `cuspidalFamily` of
the Levi parts of the flag stabilizers. -/
theorem mem_faceCuspidal_iff_family
    (y : CrossedH1 (leviCrossedH1Representation action
      (Face.faceRep action degree character F ι))) :
    y ∈ Face.FaceCuspidal action degree character F ι ↔
      leviMixedEquiv action (Face.faceRep action degree character F ι) y ∈
        cuspidalFamily
          (fun e : {e : Edges // endpoint side e = F} => Face.faceCusp action F ι e.1)
          (splitRadicalH1Representation (SemidirectProduct.inr_splitting action)
            (Rep.of (Face.faceRep action degree character F ι))) := by
  rw [← faceCuspidal_map_eq action degree character F ι]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y', hy', h⟩
    have := (leviMixedEquiv action (Face.faceRep action degree character F ι)).injective h
    rw [← this]
    exact hy'

/-- `FaceCuspidal` with the family of cusp subgroups replaced by an equal family. -/
theorem mem_faceCuspidal_iff_family' {ι' : Type} (B : ι' → Subgroup Levi)
    (hB : ∀ V : Rep ℂ Levi,
      cuspidalFamily (fun e : {e : Edges // endpoint side e = F} => Face.faceCusp action F ι e.1) V =
        cuspidalFamily B V)
    (y : CrossedH1 (leviCrossedH1Representation action
      (Face.faceRep action degree character F ι))) :
    y ∈ Face.FaceCuspidal action degree character F ι ↔
      leviMixedEquiv action (Face.faceRep action degree character F ι) y ∈
        cuspidalFamily B (splitRadicalH1Representation (SemidirectProduct.inr_splitting action)
          (Rep.of (Face.faceRep action degree character F ι))) :=
  (mem_faceCuspidal_iff_family action degree character F ι y).trans
    (Iff.of_eq (congrArg (fun S => _ ∈ S) (hB _)))

/-- The locally inner characterization with the family of cusp subgroups replaced by an equal
family. -/
theorem locallyInner_iff_edge_mem_family {ι' : Type} (B : ι' → Subgroup Levi)
    (hB : ∀ V : Rep ℂ Levi,
      cuspidalFamily (fun e : {e : Edges // endpoint side e = F} => Face.faceCusp action F ι e.1) V =
        cuspidalFamily B V)
    (hfix : ∀ radical : Radical, ∀ e : Edges, endpoint side e = F →
      (ι (SemidirectProduct.inl radical)).val • e = e)
    (ψ : Levi →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (injective : Function.Injective ψ)
    (coordinate : GeneralEisenstein.Homogeneous.H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character)) :
    coordinate ∈ locallyInnerClasses degree character side F ↔
      ∃ hr : Face.faceH2Equiv action degree character F ι coordinate ∈
          (radicalRestrictionH2 action (Face.faceRep action degree character F ι)).ker,
        splitCohomologyEdge (SemidirectProduct.inr_splitting action)
            (Rep.of (Face.faceRep action degree character F ι))
            ⟨h2Equiv (Face.faceRep action degree character F ι)
              (Face.faceH2Equiv action degree character F ι coordinate),
              h2Equiv_mem_ker action _
                ⟨Face.faceH2Equiv action degree character F ι coordinate, hr⟩⟩ ∈
          cuspidalFamily B (splitRadicalH1Representation (SemidirectProduct.inr_splitting action)
            (Rep.of (Face.faceRep action degree character F ι))) :=
  (locallyInner_iff_edge_mem_cuspidalFamily action degree character F ι hfix ψ injective
    coordinate).trans
    (exists_congr fun _ => Iff.of_eq (congrArg (fun S => _ ∈ S) (hB _)))

end FaceCuspidalFamily

section BadLine

theorem mem_faceCusp_badLine_iff (frame : GL (Fin 2) ℚ) (l : ℤˣ × binaryArithmeticLevel) :
    l ∈ Face.faceCusp integralBadLineSplitting.conjAct standardBadLine
        standardBadLineSemidirectEquiv (binaryEdge frame) ↔ l ∈ leviCusp frame := by
  change SemidirectProduct.inr l ∈ standardBadLineEdgeSubgroup (binaryEdge frame) ↔ _
  rw [mem_edgeSubgroup_iff]
  simp [leviCusp, Subgroup.mem_prod]

/-- **The cusp subgroups at the standard bad line.** -/
theorem badLine_faceCusp_family_eq (V : Rep ℂ (ℤˣ × binaryArithmeticLevel)) :
    cuspidalFamily
        (fun e : {e : Edges // endpoint .line e = standardBadLine} =>
          Face.faceCusp integralBadLineSplitting.conjAct standardBadLine
            standardBadLineSemidirectEquiv e.1) V =
      cuspidalFamily leviCusp V := by
  apply cuspidalFamily_congr
  · rintro ⟨e, he⟩
    obtain ⟨F, rfl⟩ := exists_binaryEdge e he
    exact ⟨F, by ext l; exact mem_faceCusp_badLine_iff F l⟩
  · intro F
    exact ⟨⟨binaryEdge F, binaryEdge_endpoint F⟩, by ext l; exact (mem_faceCusp_badLine_iff F l).symm⟩

end BadLine

section GoodPlane

/-- The cusp subgroup of a complete flag over the good plane is that of its dual flag over the
standard bad line. -/
theorem mem_faceCusp_goodPlane_iff (e : Edges) (l : ℤˣ × binaryArithmeticLevel) :
    l ∈ Face.faceCusp integralBadLineSplitting.conjAct Face.goodPlaneFlag
        Face.goodPlaneSemidirectEquiv e ↔
      l ∈ Face.faceCusp integralBadLineSplitting.conjAct standardBadLine
        standardBadLineSemidirectEquiv (dualEdge e) := by
  have hval := Face.goodPlaneSemidirectEquiv_val (SemidirectProduct.inr l)
  have hg : (Face.goodPlaneSemidirectEquiv (SemidirectProduct.inr l)).val ∈ rationalLevel :=
    (Face.goodPlaneSemidirectEquiv (SemidirectProduct.inr l)).property.1
  have hb : (standardBadLineSemidirectEquiv (SemidirectProduct.inr l)).val ∈ rationalLevel :=
    (standardBadLineSemidirectEquiv (SemidirectProduct.inr l)).property.1
  change ((Face.goodPlaneSemidirectEquiv (SemidirectProduct.inr l)).val ∈ rationalLevel ∧
      (Face.goodPlaneSemidirectEquiv (SemidirectProduct.inr l)).val ∈
        MulAction.stabilizer RationalGL3 e) ↔
    ((standardBadLineSemidirectEquiv (SemidirectProduct.inr l)).val ∈ rationalLevel ∧
      (standardBadLineSemidirectEquiv (SemidirectProduct.inr l)).val ∈
        MulAction.stabilizer RationalGL3 (dualEdge e))
  rw [and_iff_right hg, and_iff_right hb, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, hval]
  constructor
  · intro h
    have h2 := congrArg dualEdge h
    rwa [dualEdge_smul, dualInvolution_involutive] at h2
  · intro h
    have h2 : dualEdge (dualInvolution (standardBadLineSemidirectEquiv (SemidirectProduct.inr l)).val • e) =
        dualEdge e := by
      rw [dualEdge_smul, dualInvolution_involutive]
      exact h
    have h3 := congrArg dualEdge h2
    rwa [Dual.dualEdge_dualEdge, Dual.dualEdge_dualEdge] at h3

/-- **The cusp subgroups at the good plane** are the same `ℤˣ × binaryCuspLevel` as at the
standard bad line. -/
theorem goodPlane_faceCusp_family_eq (V : Rep ℂ (ℤˣ × binaryArithmeticLevel)) :
    cuspidalFamily
        (fun e : {e : Edges // endpoint .plane e = Face.goodPlaneFlag} =>
          Face.faceCusp integralBadLineSplitting.conjAct Face.goodPlaneFlag
            Face.goodPlaneSemidirectEquiv e.1) V =
      cuspidalFamily leviCusp V := by
  apply cuspidalFamily_congr
  · rintro ⟨e, he⟩
    have he' : endpoint .line (dualEdge e) = standardBadLine := by
      rw [endpoint_line_dualEdge, he]
      exact Dual.dualPlaneFlag_dualFlag _
    obtain ⟨F, hF⟩ := exists_binaryEdge _ he'
    refine ⟨F, ?_⟩
    ext l
    rw [mem_faceCusp_goodPlane_iff, hF]
    exact mem_faceCusp_badLine_iff F l
  · intro F
    refine ⟨⟨dualEdge (binaryEdge F), ?_⟩, ?_⟩
    · rw [endpoint_plane_dualEdge, binaryEdge_endpoint]
      rfl
    · ext l
      change _ ↔ l ∈ Face.faceCusp _ Face.goodPlaneFlag _ (dualEdge (binaryEdge F))
      rw [mem_faceCusp_goodPlane_iff, Dual.dualEdge_dualEdge]
      exact (mem_faceCusp_badLine_iff F l).symm

end GoodPlane

section GoodLine

/-- The transposition `e₁ ↔ e₂` of `GL₂(ℚ)`. -/
def swapQ : GL (Fin 2) ℚ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

theorem swapQ_inv : swapQ⁻¹ = swapQ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapQ]

theorem goodLine_inr_val (l : GL (Fin 2) ℤ) :
    (Face.goodLineSemidirectEquivFixed (SemidirectProduct.inr l)).val =
      planeLevi (GeneralLinearGroup.map (Int.castRingHom ℚ) l) 1 := by
  change (goodLineRadicalInclusion 1 * goodLineSplitting l).val = _
  rw [map_one, one_mul]
  exact map_planeLevi_one (Int.castRingHom ℚ) l

/-- Conjugating the plane Levi by the long Weyl element gives a line Levi with the block
conjugated by the transposition. -/
theorem goodLine_conj_planeLevi (A : GL (Fin 2) ℚ) :
    rationalGoodLine⁻¹ * planeLevi A 1 * rationalGoodLine = lineLevi 1 (swapQ * A * swapQ) := by
  rw [rationalGoodLine_inverse]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalGoodLine, lineLevi_val, swapQ, planeLevi, planeBlock, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- A line Levi element fixes `binaryEdge F` iff `F⁻¹ C F` is upper triangular. -/
theorem lineLevi_smul_binaryEdge_iff (F C : GL (Fin 2) ℚ) :
    lineLevi 1 C • binaryEdge F = binaryEdge F ↔ (F⁻¹ * C * F).val 1 0 = 0 := by
  change (QuotientGroup.mk (lineLevi 1 C * binaryLineLeviHom ℚ F) : Edges) =
    QuotientGroup.mk (binaryLineLeviHom ℚ F) ↔ _
  rw [QuotientGroup.eq, ← inv_mem_iff (x := (_ * _)⁻¹ * _)]
  have h : ((lineLevi 1 C * binaryLineLeviHom ℚ F)⁻¹ * binaryLineLeviHom ℚ F)⁻¹ =
      binaryLineLeviHom ℚ (F⁻¹ * C * F) := by
    rw [map_mul, map_mul, map_inv]
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
    rfl
  rw [h]
  change binaryLineLeviHom ℚ (F⁻¹ * C * F) ∈ parabolic .plane ⊓ parabolic .line ↔ _
  constructor
  · intro hm
    have := hm.1
    change (lineLevi 1 (F⁻¹ * C * F)).val 2 0 = 0 ∧ (lineLevi 1 (F⁻¹ * C * F)).val 2 1 = 0 at this
    rw [lineLevi_val] at this
    simpa using this.2
  · intro hm
    refine ⟨?_, lineLevi_mem 1 _⟩
    change (lineLevi 1 (F⁻¹ * C * F)).val 2 0 = 0 ∧ (lineLevi 1 (F⁻¹ * C * F)).val 2 1 = 0
    rw [lineLevi_val]
    exact ⟨by simp, by simpa using hm⟩

theorem mem_faceCusp_goodLine_iff (F : GL (Fin 2) ℚ) (l : GL (Fin 2) ℤ) :
    l ∈ Face.faceCusp goodLineSplitting.conjAct Face.goodLineFlag Face.goodLineSemidirectEquivFixed
        (rationalGoodLine • binaryEdge F) ↔ l ∈ cuspGL (swapQ * F) := by
  have hlev : (Face.goodLineSemidirectEquivFixed (SemidirectProduct.inr l)).val ∈ rationalLevel :=
    (Face.goodLineSemidirectEquivFixed (SemidirectProduct.inr l)).property.1
  change ((Face.goodLineSemidirectEquivFixed (SemidirectProduct.inr l)).val ∈ rationalLevel ∧
      (Face.goodLineSemidirectEquivFixed (SemidirectProduct.inr l)).val ∈
        MulAction.stabilizer RationalGL3 (rationalGoodLine • binaryEdge F)) ↔ _
  rw [and_iff_right hlev, MulAction.mem_stabilizer_iff, goodLine_inr_val]
  set x := planeLevi (GeneralLinearGroup.map (Int.castRingHom ℚ) l) 1 with hx
  have h1 : x • rationalGoodLine • binaryEdge F = rationalGoodLine • binaryEdge F ↔
      (rationalGoodLine⁻¹ * x * rationalGoodLine) • binaryEdge F = binaryEdge F := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
  rw [h1, goodLine_conj_planeLevi, lineLevi_smul_binaryEdge_iff, mem_cuspGL_iff]
  have : (swapQ * F)⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) l * (swapQ * F) =
      F⁻¹ * (swapQ * GeneralLinearGroup.map (Int.castRingHom ℚ) l * swapQ) * F := by
    simp only [_root_.mul_inv_rev, swapQ_inv, mul_assoc]
  rw [this]

/-- **The cusp subgroups at the good line** are the stabilizers `cuspGL F` of `GL₂(ℤ)`. -/
theorem goodLine_faceCusp_family_eq (V : Rep ℂ (GL (Fin 2) ℤ)) :
    cuspidalFamily
        (fun e : {e : Edges // endpoint .line e = Face.goodLineFlag} =>
          Face.faceCusp goodLineSplitting.conjAct Face.goodLineFlag
            Face.goodLineSemidirectEquivFixed e.1) V =
      cuspidalFamily cuspGL V := by
  have hline : ∀ F : GL (Fin 2) ℚ,
      endpoint .line (rationalGoodLine • binaryEdge F) = Face.goodLineFlag := by
    intro F
    rw [endpoint_smul, binaryEdge_endpoint]
    change rationalGoodLine • (QuotientGroup.mk 1 : Flags .line) = QuotientGroup.mk rationalGoodLine
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  apply cuspidalFamily_congr
  · rintro ⟨e, he⟩
    have he' : endpoint .line (rationalGoodLine⁻¹ • e) = standardBadLine := by
      rw [endpoint_smul, he]
      change rationalGoodLine⁻¹ • (QuotientGroup.mk rationalGoodLine : Flags .line) =
        QuotientGroup.mk 1
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
    obtain ⟨F, hF⟩ := exists_binaryEdge _ he'
    have heq : e = rationalGoodLine • binaryEdge F := by
      rw [← hF, smul_inv_smul]
    refine ⟨swapQ * F, ?_⟩
    ext l
    change l ∈ Face.faceCusp _ _ _ e ↔ _
    rw [heq]
    exact mem_faceCusp_goodLine_iff F l
  · intro F'
    refine ⟨⟨rationalGoodLine • binaryEdge (swapQ * F'), hline _⟩, ?_⟩
    ext l
    change l ∈ cuspGL F' ↔ l ∈ Face.faceCusp _ _ _ (rationalGoodLine • binaryEdge (swapQ * F'))
    rw [mem_faceCusp_goodLine_iff, ← mul_assoc]
    have : swapQ * swapQ = 1 := by
      rw [← swapQ_inv]
      exact inv_mul_cancel swapQ
    rw [this, one_mul]

end GoodLine

section Faces

/-- **Standard bad line: `FaceCuspidal` is `cuspidalFamily` of `ℤˣ × binaryCuspLevel F`.** -/
theorem badLine_faceCuspidal_iff (n : ℕ) (character : RankOneCharacter)
    (y : CrossedH1 (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (Face.faceRep integralBadLineSplitting.conjAct n character standardBadLine
        standardBadLineSemidirectEquiv))) :
    y ∈ Face.FaceCuspidal integralBadLineSplitting.conjAct n character standardBadLine
        standardBadLineSemidirectEquiv ↔
      leviMixedEquiv integralBadLineSplitting.conjAct
        (Face.faceRep integralBadLineSplitting.conjAct n character standardBadLine
          standardBadLineSemidirectEquiv) y ∈ cuspidalFamily leviCusp
        (splitRadicalH1Representation
          (SemidirectProduct.inr_splitting integralBadLineSplitting.conjAct)
          (Rep.of (Face.faceRep integralBadLineSplitting.conjAct n character standardBadLine
            standardBadLineSemidirectEquiv))) :=
  mem_faceCuspidal_iff_family' _ n character standardBadLine _ leviCusp
    (badLine_faceCusp_family_eq) y

/-- **Good plane: `FaceCuspidal` is `cuspidalFamily` of `ℤˣ × binaryCuspLevel F`.** -/
theorem goodPlane_faceCuspidal_iff (n : ℕ) (character : RankOneCharacter)
    (y : CrossedH1 (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (Face.faceRep integralBadLineSplitting.conjAct n character Face.goodPlaneFlag
        Face.goodPlaneSemidirectEquiv))) :
    y ∈ Face.FaceCuspidal integralBadLineSplitting.conjAct n character Face.goodPlaneFlag
        Face.goodPlaneSemidirectEquiv ↔
      leviMixedEquiv integralBadLineSplitting.conjAct
        (Face.faceRep integralBadLineSplitting.conjAct n character Face.goodPlaneFlag
          Face.goodPlaneSemidirectEquiv) y ∈ cuspidalFamily leviCusp
        (splitRadicalH1Representation
          (SemidirectProduct.inr_splitting integralBadLineSplitting.conjAct)
          (Rep.of (Face.faceRep integralBadLineSplitting.conjAct n character Face.goodPlaneFlag
            Face.goodPlaneSemidirectEquiv))) :=
  mem_faceCuspidal_iff_family' _ n character Face.goodPlaneFlag _ leviCusp
    (goodPlane_faceCusp_family_eq) y

/-- **Good line: `FaceCuspidal` is `cuspidalFamily` of the cusp stabilizers `cuspGL F` of
`GL₂(ℤ)`.** -/
theorem goodLine_faceCuspidal_iff (n : ℕ) (character : RankOneCharacter)
    (y : CrossedH1 (leviCrossedH1Representation goodLineSplitting.conjAct
      (Face.faceRep goodLineSplitting.conjAct n character Face.goodLineFlag
        Face.goodLineSemidirectEquivFixed))) :
    y ∈ Face.FaceCuspidal goodLineSplitting.conjAct n character Face.goodLineFlag
        Face.goodLineSemidirectEquivFixed ↔
      leviMixedEquiv goodLineSplitting.conjAct
        (Face.faceRep goodLineSplitting.conjAct n character Face.goodLineFlag
          Face.goodLineSemidirectEquivFixed) y ∈ cuspidalFamily cuspGL
        (splitRadicalH1Representation
          (SemidirectProduct.inr_splitting goodLineSplitting.conjAct)
          (Rep.of (Face.faceRep goodLineSplitting.conjAct n character Face.goodLineFlag
            Face.goodLineSemidirectEquivFixed))) :=
  mem_faceCuspidal_iff_family' _ n character Face.goodLineFlag _ cuspGL
    (goodLine_faceCusp_family_eq) y

end Faces

end TernaryPeriodPolynomials.Argument.SeedC3S4c
