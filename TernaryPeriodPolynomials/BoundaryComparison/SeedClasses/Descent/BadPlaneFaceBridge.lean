module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.SemidirectModel
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.BadPlaneReflection
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.BadPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PlaneParabolicBinaryProjection

@[expose] public section



/-!
# The face library's mixed cuspidal group at the identity plane is the literal one

Paper: Lemma C.3 (`ar:lem:seed`),

(finite reflections).

At the identity (bad) plane of the paper's level group
`Γ = {g ∈ GL₃(ℤ) | e₃* g ≡ e₃* mod 3}` the stabilizer is `Λ₀ = ℤ² ⋊ GL₂(ℤ)`
(`identityPlaneSemidirectEquiv`).  Two descriptions of its mixed cuspidal group exist:

* the face library (`FacePairingFull.Face`): `FaceCuspidal` in the crossed model, with the cusp
  subgroups `faceCusp e` = Levi part of the stabilizer of the complete flag `e` over the plane, and the
  homogeneous-cochain `H²` of the stabilizer with `locallyInnerClasses`;
* `BadPlaneReflection`: `badPlaneCuspidal n`, Mathlib's `groupCohomology` on the split extension, with
  the cusp subgroups `cuspGL F` = stabilizer in `GL₂(ℤ)` of the rational cusp of a frame `F ∈ GL₂(ℚ)`.

This file proves they coincide (trivial character; no parity hypothesis for the first two):

* `mem_faceCusp_badPlane_iff`: `ℓ ∈ faceCusp (g·B)` iff `ℓ ∈ cuspGL F`, `F` the upper left block of
  the plane-parabolic element `g`; `badPlane_faceCusp_family_eq`: the two families of cusp subgroups
  have the same members, hence the same `cuspidalFamily`;
* `badPlane_faceCuspidal_iff`: a class of the crossed model lies in `FaceCuspidal` iff its image in
  Mathlib's `H¹` lies in `badPlaneCuspidal n`;
* `badPlaneH2Equiv`, `badPlaneH2Equiv_mem_locallyInner_iff`: for odd `n > 0`, the identification of
  Mathlib's `H²(Λ₀, E_n)` with the face library's `H²` maps `badPlaneCuspidalInH2 n` (classes with
  Hochschild--Serre edge in `badPlaneCuspidal n`) onto `locallyInnerClasses` (zero restriction to the
  stabilizer of every complete flag over the plane).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

/-- The ambient matrix of the Levi element `ℓ` of the identity plane. -/
theorem badPlane_inr_val (l : GL (Fin 2) ℤ) :
    (Face.badPlaneSemidirectEquiv (SemidirectProduct.inr l)).val =
      planeLevi (GeneralLinearGroup.map (Int.castRingHom ℚ) l) 1 := by
  change (identityPlaneRadicalInclusion 1 * identityPlaneSplitting l).val = _
  rw [map_one, one_mul]
  exact map_planeLevi_one (Int.castRingHom ℚ) l

theorem planeParabolicBinary_planeLevi (A : GL (Fin 2) ℚ) (d : ℚˣ) :
    planeParabolicBinary (⟨planeLevi A d, planeLevi_mem A d⟩ : planeParabolic ℚ) = A := by
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **The Levi part of the stabilizer of a complete flag over the identity plane is a cusp
stabilizer of `GL₂(ℤ)`.** For `g` in the plane parabolic the complete flag `g·B` lies over the
identity plane, and the elements `ℓ` of the Levi `GL₂(ℤ)` fixing it are those with `F⁻¹ ℓ F` upper
triangular, where `F` is the upper left block of `g`. -/
theorem mem_faceCusp_badPlane_iff (g : RationalGL3) (hg : g ∈ planeParabolic ℚ) (l : GL (Fin 2) ℤ) :
    l ∈ Face.faceCusp identityPlaneSplitting.conjAct Face.badPlaneFlag Face.badPlaneSemidirectEquiv
        (QuotientGroup.mk g) ↔
      l ∈ cuspGL (planeParabolicBinary (⟨g, hg⟩ : planeParabolic ℚ)) := by
  let pg : planeParabolic ℚ := ⟨g, hg⟩
  let pl : planeParabolic ℚ :=
    ⟨planeLevi (GeneralLinearGroup.map (Int.castRingHom ℚ) l) 1, planeLevi_mem _ _⟩
  let P : planeParabolic ℚ := pg⁻¹ * pl * pg
  have hP : P.val = g⁻¹ * planeLevi (GeneralLinearGroup.map (Int.castRingHom ℚ) l) 1 * g := rfl
  have hbin : planeParabolicBinary P =
      (planeParabolicBinary pg)⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) l *
        planeParabolicBinary pg := by
    rw [show P = pg⁻¹ * pl * pg from rfl, map_mul, map_mul, map_inv]
    congr 2
    exact planeParabolicBinary_planeLevi _ _
  rw [mem_cuspGL_iff, ← hbin]
  have h10 : (planeParabolicBinary P).val 1 0 = P.val.val 1 0 := rfl
  rw [h10]
  have hmem : l ∈ Face.faceCusp identityPlaneSplitting.conjAct Face.badPlaneFlag
      Face.badPlaneSemidirectEquiv (QuotientGroup.mk g) ↔
      g⁻¹ * planeLevi (GeneralLinearGroup.map (Int.castRingHom ℚ) l) 1 * g ∈
        parabolic .plane ⊓ parabolic .line := by
    have hlev : (Face.badPlaneSemidirectEquiv (SemidirectProduct.inr l)).val ∈ rationalLevel :=
      (Face.badPlaneSemidirectEquiv (SemidirectProduct.inr l)).property.1
    change ((Face.badPlaneSemidirectEquiv (SemidirectProduct.inr l)).val ∈ rationalLevel ∧
      (Face.badPlaneSemidirectEquiv (SemidirectProduct.inr l)).val ∈
        MulAction.stabilizer RationalGL3 (QuotientGroup.mk g : Edges)) ↔ _
    rw [badPlane_inr_val] at hlev ⊢
    rw [MulAction.mem_stabilizer_iff]
    change _ ∧ (QuotientGroup.mk (planeLevi (GeneralLinearGroup.map (Int.castRingHom ℚ) l) 1 * g) :
      Edges) = QuotientGroup.mk g ↔ _
    rw [QuotientGroup.eq, ← inv_mem_iff (x := _⁻¹ * g)]
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, and_iff_right hlev]
  rw [hmem, ← hP]
  constructor
  · intro h
    exact h.2.1
  · intro h
    exact ⟨P.property, h, P.property.1⟩

section Family

variable {L : Type} [Group L] {ι ι' : Type}

/-- The cuspidal subspace depends only on the set of cusp subgroups. -/
theorem cuspidalFamily_congr (B : ι → Subgroup L) (B' : ι' → Subgroup L) (V : Rep ℂ L)
    (h1 : ∀ i, ∃ j, B i = B' j) (h2 : ∀ j, ∃ i, B' j = B i) :
    cuspidalFamily B V = cuspidalFamily B' V := by
  unfold cuspidalFamily
  apply le_antisymm
  · refine le_iInf fun j => ?_
    obtain ⟨i, hi⟩ := h2 j
    rw [hi]
    exact iInf_le _ i
  · refine le_iInf fun i => ?_
    obtain ⟨j, hj⟩ := h1 i
    rw [hj]
    exact iInf_le _ j

end Family

/-- A complete flag over the identity plane is `g B` with `g` in the plane parabolic. -/
theorem exists_planeParabolic_of_endpoint (e : Edges) (he : endpoint .plane e = Face.badPlaneFlag) :
    ∃ g : RationalGL3, g ∈ planeParabolic ℚ ∧ e = QuotientGroup.mk g := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective e
  refine ⟨g, ?_, rfl⟩
  have h := QuotientGroup.eq.mp he
  have h' : g⁻¹ ∈ parabolic .plane := by simpa using h
  have h'' : g ∈ parabolic .plane := by simpa using (parabolic .plane).inv_mem h'
  exact h''

/-- **The cusp subgroups of the face library at the identity plane are the cusp stabilizers of
`GL₂(ℤ)`.** -/
theorem badPlane_faceCusp_family_eq (V : Rep ℂ (GL (Fin 2) ℤ)) :
    cuspidalFamily
        (fun e : {e : Edges // endpoint .plane e = Face.badPlaneFlag} =>
          Face.faceCusp identityPlaneSplitting.conjAct Face.badPlaneFlag
            Face.badPlaneSemidirectEquiv e.1) V =
      cuspidalFamily cuspGL V := by
  apply cuspidalFamily_congr
  · rintro ⟨e, he⟩
    obtain ⟨g, hg, rfl⟩ := exists_planeParabolic_of_endpoint e he
    refine ⟨planeParabolicBinary (⟨g, hg⟩ : planeParabolic ℚ), ?_⟩
    ext l
    exact mem_faceCusp_badPlane_iff g hg l
  · intro F
    have hmem : planeLevi F 1 ∈ planeParabolic ℚ := planeLevi_mem F 1
    refine ⟨⟨QuotientGroup.mk (planeLevi F 1), ?_⟩, ?_⟩
    · change (QuotientGroup.mk (planeLevi F 1) : Flags .plane) = QuotientGroup.mk 1
      apply QuotientGroup.eq.mpr
      simpa using (parabolic .plane).inv_mem hmem
    · ext l
      rw [mem_faceCusp_badPlane_iff (planeLevi F 1) hmem l,
        planeParabolicBinary_planeLevi F 1]

/-- At the identity plane the face library's coefficient representation (trivial character) is the
semidirect product model of the library's `identityPlaneCoefficientRep`. -/
theorem faceRep_badPlane (n : ℕ) :
    Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
        Face.badPlaneSemidirectEquiv =
      (semidirectRep identityPlaneSplitting (identityPlaneCoefficientRep n)).ρ := rfl

/-- **The face library's `FaceCuspidal` at the identity plane is `badPlaneCuspidal`.** A class of
`H¹(GL₂(ℤ), H¹(ℤ², E_n))` in the crossed model lies in `FaceCuspidal` (restricts to zero on the Levi
part of the stabilizer of every complete flag over the identity plane) iff its image in Mathlib's
`H¹` on the split extension `Λ₀ = ℤ² ⋊ GL₂(ℤ)` lies in the literal mixed cuspidal group
`badPlaneCuspidal n` (restricts to zero on the stabilizer in `GL₂(ℤ)` of every rational cusp). -/
theorem badPlane_faceCuspidal_iff (n : ℕ)
    (y : CrossedH1 (leviCrossedH1Representation identityPlaneSplitting.conjAct
      (Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
        Face.badPlaneSemidirectEquiv))) :
    y ∈ Face.FaceCuspidal identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
        Face.badPlaneSemidirectEquiv ↔
      (semidirectH1Equiv identityPlaneSplitting (identityPlaneCoefficientRep n)).symm
        (leviMixedEquiv identityPlaneSplitting.conjAct
          (Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
            Face.badPlaneSemidirectEquiv) y) ∈ badPlaneCuspidal n := by
  have hmap := faceCuspidal_map_eq identityPlaneSplitting.conjAct n trivialCharacter
    Face.badPlaneFlag Face.badPlaneSemidirectEquiv
  have h1 : y ∈ Face.FaceCuspidal identityPlaneSplitting.conjAct n trivialCharacter
      Face.badPlaneFlag Face.badPlaneSemidirectEquiv ↔
      leviMixedEquiv identityPlaneSplitting.conjAct
        (Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
          Face.badPlaneSemidirectEquiv) y ∈
        cuspidalFamily
          (fun e : {e : Edges // endpoint .plane e = Face.badPlaneFlag} =>
            Face.faceCusp identityPlaneSplitting.conjAct Face.badPlaneFlag
              Face.badPlaneSemidirectEquiv e.1)
          (splitRadicalH1Representation (SemidirectProduct.inr_splitting identityPlaneSplitting.conjAct)
            (Rep.of (Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
              Face.badPlaneSemidirectEquiv))) := by
    rw [← hmap]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y', hy', h⟩
      have := (leviMixedEquiv identityPlaneSplitting.conjAct
        (Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
          Face.badPlaneSemidirectEquiv)).injective h
      rw [← this]
      exact hy'
  refine h1.trans ?_
  refine (Iff.of_eq (congrArg (fun S => _ ∈ S) (badPlane_faceCusp_family_eq _))).trans ?_
  exact (semidirectH1Equiv_symm_mem_cuspidalFamily identityPlaneSplitting
    (identityPlaneCoefficientRep n) cuspGL _).symm

/-- **Mathlib's `H²` of `Λ₀ = ℤ² ⋊ GL₂(ℤ)` is the face library's `H²` of the stabilizer of the identity
plane** (trivial character), through the semidirect product model, `h2Equiv` and `faceH2Equiv`. -/
def badPlaneH2Equiv (n : ℕ) : groupCohomology.H2 (identityPlaneCoefficientRep n) ≃ₗ[ℂ]
    GeneralEisenstein.Homogeneous.H2 (fixedPointLevel rationalLevel Face.badPlaneFlag)
      (rationalCoefficientComponent n trivialCharacter) :=
  ((LinearEquiv.ofBijective (semidirectH2Map identityPlaneSplitting (identityPlaneCoefficientRep n))
    (semidirectH2Map_bijective _ _)).trans
    (h2Equiv (Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
      Face.badPlaneSemidirectEquiv)).symm).trans
    (Face.faceH2Equiv identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
      Face.badPlaneSemidirectEquiv).symm

/-- **Locally inner classes at the identity plane are the classes with cuspidal edge.** For odd
`n > 0` and a class `z ∈ H²(Λ₀, E_n)` of Mathlib's group cohomology, its image in the face library's
`H²` of the stabilizer of the identity plane is locally inner (vanishes on the stabilizer of every
complete flag over the plane) iff `z` has Hochschild--Serre edge in the literal mixed cuspidal group
`badPlaneCuspidal n`, i.e. iff `z ∈ badPlaneCuspidalInH2 n`. -/
theorem badPlaneH2Equiv_mem_locallyInner_iff (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (z : groupCohomology.H2 (identityPlaneCoefficientRep n)) :
    badPlaneH2Equiv n z ∈ locallyInnerClasses n trivialCharacter .plane Face.badPlaneFlag ↔
      z ∈ badPlaneCuspidalInH2 n hn hodd := by
  have hz : twoCohomologyRestriction identityPlaneExtension.inl (identityPlaneCoefficientRep n) z = 0 :=
    identityPlaneH2_restriction_zero n hn hodd z
  have hab : h2Equiv (Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter
      Face.badPlaneFlag Face.badPlaneSemidirectEquiv)
      (Face.faceH2Equiv identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
        Face.badPlaneSemidirectEquiv (badPlaneH2Equiv n z)) =
      semidirectH2Map identityPlaneSplitting (identityPlaneCoefficientRep n) z := by
    refine (congrArg (h2Equiv (Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter
      Face.badPlaneFlag Face.badPlaneSemidirectEquiv))
      (LinearEquiv.apply_symm_apply (Face.faceH2Equiv identityPlaneSplitting.conjAct n
        trivialCharacter Face.badPlaneFlag Face.badPlaneSemidirectEquiv)
        ((h2Equiv (Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter
          Face.badPlaneFlag Face.badPlaneSemidirectEquiv)).symm
          (semidirectH2Map identityPlaneSplitting (identityPlaneCoefficientRep n) z)))).trans ?_
    exact LinearEquiv.apply_symm_apply _ _
  refine (locallyInner_iff_edge_mem_cuspidalFamily identityPlaneSplitting.conjAct n trivialCharacter
    Face.badPlaneFlag Face.badPlaneSemidirectEquiv (fun r e he => Face.badPlane_radical_fixes r e he)
    Face.badPlaneLeviEmbedding Face.badPlaneLeviEmbedding_injective (badPlaneH2Equiv n z)).trans ?_
  let ρB := Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
    Face.badPlaneSemidirectEquiv
  let xB := Face.faceH2Equiv identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
    Face.badPlaneSemidirectEquiv (badPlaneH2Equiv n z)
  have hrB : xB ∈ (radicalRestrictionH2 identityPlaneSplitting.conjAct ρB).ker := by
    apply (h2Equiv (ρB.comp SemidirectProduct.inl)).injective
    rw [← h2Equiv_radicalRestriction, hab, LinearEquiv.map_zero (h2Equiv (ρB.comp SemidirectProduct.inl))]
    exact (semidirectH2Map_restriction_eq_zero_iff identityPlaneSplitting
      (identityPlaneCoefficientRep n) z).mpr hz
  have hker : (⟨h2Equiv ρB xB, h2Equiv_mem_ker identityPlaneSplitting.conjAct ρB ⟨xB, hrB⟩⟩ :
      (twoCohomologyRestriction (SemidirectProduct.toGroupExtension identityPlaneSplitting.conjAct).inl
        (Rep.of ρB)).ker) =
      ⟨semidirectH2Map identityPlaneSplitting (identityPlaneCoefficientRep n) z,
        (semidirectH2Map_restriction_eq_zero_iff identityPlaneSplitting
          (identityPlaneCoefficientRep n) z).mpr hz⟩ := Subtype.ext hab
  have hedge := semidirect_edge identityPlaneSplitting (identityPlaneCoefficientRep n) ⟨z, hz⟩
  have hfam := badPlane_faceCusp_family_eq
    (splitRadicalH1Representation (SemidirectProduct.inr_splitting identityPlaneSplitting.conjAct)
      (semidirectRep identityPlaneSplitting (identityPlaneCoefficientRep n)))
  have hiff : splitCohomologyEdge (SemidirectProduct.inr_splitting identityPlaneSplitting.conjAct)
      (Rep.of ρB) ⟨h2Equiv ρB xB, h2Equiv_mem_ker identityPlaneSplitting.conjAct ρB ⟨xB, hrB⟩⟩ ∈
      cuspidalFamily
        (fun e : {e : Edges // endpoint .plane e = Face.badPlaneFlag} =>
          Face.faceCusp identityPlaneSplitting.conjAct Face.badPlaneFlag
            Face.badPlaneSemidirectEquiv e.1)
        (splitRadicalH1Representation (SemidirectProduct.inr_splitting identityPlaneSplitting.conjAct)
          (Rep.of ρB)) ↔
      z ∈ badPlaneCuspidalInH2 n hn hodd := by
    refine (Iff.of_eq (congrArg (fun k => splitCohomologyEdge
      (SemidirectProduct.inr_splitting identityPlaneSplitting.conjAct) (Rep.of ρB) k ∈
        cuspidalFamily
          (fun e : {e : Edges // endpoint .plane e = Face.badPlaneFlag} =>
            Face.faceCusp identityPlaneSplitting.conjAct Face.badPlaneFlag
              Face.badPlaneSemidirectEquiv e.1)
          (splitRadicalH1Representation
            (SemidirectProduct.inr_splitting identityPlaneSplitting.conjAct) (Rep.of ρB))) hker)).trans ?_
    refine (Iff.of_eq (congrArg (fun S => _ ∈ S) hfam)).trans ?_
    refine (Iff.of_eq (congrArg (fun w => w ∈ _) hedge)).trans ?_
    exact semidirectH1Equiv_mem_cuspidalFamily identityPlaneSplitting
      (identityPlaneCoefficientRep n) cuspGL _
  exact ⟨fun ⟨_, h⟩ => hiff.mp h, fun h => ⟨hrB, hiff.mpr h⟩⟩

/-- **Locally inner classes at the identity plane, every degree.** For every `n` (no parity
hypothesis) a class `z ∈ H²(Λ₀, E_n)` has locally inner image in the face library iff its radical
restriction vanishes and its Hochschild--Serre edge lies in `badPlaneCuspidal n`.  The radical
condition is part of `𝒞_P(E) ↪ H²`: a locally inner class has zero radical
restriction because the radical fixes every complete flag over the plane, so no vanishing statement
is needed for even `n`. -/
theorem badPlaneH2Equiv_mem_locallyInner_iff_general (n : ℕ)
    (z : groupCohomology.H2 (identityPlaneCoefficientRep n)) :
    badPlaneH2Equiv n z ∈ locallyInnerClasses n trivialCharacter .plane Face.badPlaneFlag ↔
      ∃ hz : twoCohomologyRestriction identityPlaneExtension.inl
          (identityPlaneCoefficientRep n) z = 0,
        splitCohomologyEdge identityPlaneSplitting (identityPlaneCoefficientRep n) ⟨z, hz⟩ ∈
          badPlaneCuspidal n := by
  let ρB := Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
    Face.badPlaneSemidirectEquiv
  let xB := Face.faceH2Equiv identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
    Face.badPlaneSemidirectEquiv (badPlaneH2Equiv n z)
  have hab : h2Equiv ρB xB =
      semidirectH2Map identityPlaneSplitting (identityPlaneCoefficientRep n) z := by
    refine (congrArg (h2Equiv ρB)
      (LinearEquiv.apply_symm_apply (Face.faceH2Equiv identityPlaneSplitting.conjAct n
        trivialCharacter Face.badPlaneFlag Face.badPlaneSemidirectEquiv)
        ((h2Equiv ρB).symm
          (semidirectH2Map identityPlaneSplitting (identityPlaneCoefficientRep n) z)))).trans ?_
    exact LinearEquiv.apply_symm_apply _ _
  have hrB_iff : xB ∈ (radicalRestrictionH2 identityPlaneSplitting.conjAct ρB).ker ↔
      twoCohomologyRestriction identityPlaneExtension.inl (identityPlaneCoefficientRep n) z = 0 := by
    have h1 := h2Equiv_radicalRestriction identityPlaneSplitting.conjAct ρB xB
    refine (LinearMap.mem_ker.trans ((h2Equiv (ρB.comp SemidirectProduct.inl)).map_eq_zero_iff.symm.trans
      (Iff.of_eq (congrArg (fun w => w = 0) h1.symm)))).trans ?_
    refine (Iff.of_eq (congrArg (fun w => twoCohomologyRestriction
      (SemidirectProduct.toGroupExtension identityPlaneSplitting.conjAct).inl
        (semidirectRep identityPlaneSplitting (identityPlaneCoefficientRep n)) w = 0) hab)).trans ?_
    exact semidirectH2Map_restriction_eq_zero_iff identityPlaneSplitting
      (identityPlaneCoefficientRep n) z
  have key : ∀ (hz : twoCohomologyRestriction identityPlaneExtension.inl
        (identityPlaneCoefficientRep n) z = 0)
      (hr : xB ∈ (radicalRestrictionH2 identityPlaneSplitting.conjAct ρB).ker),
      splitCohomologyEdge (SemidirectProduct.inr_splitting identityPlaneSplitting.conjAct)
        (Rep.of ρB) ⟨h2Equiv ρB xB, h2Equiv_mem_ker identityPlaneSplitting.conjAct ρB ⟨xB, hr⟩⟩ ∈
      cuspidalFamily
        (fun e : {e : Edges // endpoint .plane e = Face.badPlaneFlag} =>
          Face.faceCusp identityPlaneSplitting.conjAct Face.badPlaneFlag
            Face.badPlaneSemidirectEquiv e.1)
        (splitRadicalH1Representation (SemidirectProduct.inr_splitting identityPlaneSplitting.conjAct)
          (Rep.of ρB)) ↔
      splitCohomologyEdge identityPlaneSplitting (identityPlaneCoefficientRep n) ⟨z, hz⟩ ∈
        badPlaneCuspidal n := by
    intro hz hr
    have hker : (⟨h2Equiv ρB xB, h2Equiv_mem_ker identityPlaneSplitting.conjAct ρB ⟨xB, hr⟩⟩ :
        (twoCohomologyRestriction
          (SemidirectProduct.toGroupExtension identityPlaneSplitting.conjAct).inl (Rep.of ρB)).ker) =
        ⟨semidirectH2Map identityPlaneSplitting (identityPlaneCoefficientRep n) z,
          (semidirectH2Map_restriction_eq_zero_iff identityPlaneSplitting
            (identityPlaneCoefficientRep n) z).mpr hz⟩ := Subtype.ext hab
    have hedge := semidirect_edge identityPlaneSplitting (identityPlaneCoefficientRep n) ⟨z, hz⟩
    have hfam := badPlane_faceCusp_family_eq
      (splitRadicalH1Representation (SemidirectProduct.inr_splitting identityPlaneSplitting.conjAct)
        (semidirectRep identityPlaneSplitting (identityPlaneCoefficientRep n)))
    refine (Iff.of_eq (congrArg (fun k => splitCohomologyEdge
      (SemidirectProduct.inr_splitting identityPlaneSplitting.conjAct) (Rep.of ρB) k ∈
        cuspidalFamily
          (fun e : {e : Edges // endpoint .plane e = Face.badPlaneFlag} =>
            Face.faceCusp identityPlaneSplitting.conjAct Face.badPlaneFlag
              Face.badPlaneSemidirectEquiv e.1)
          (splitRadicalH1Representation
            (SemidirectProduct.inr_splitting identityPlaneSplitting.conjAct) (Rep.of ρB))) hker)).trans ?_
    refine (Iff.of_eq (congrArg (fun S => _ ∈ S) hfam)).trans ?_
    refine (Iff.of_eq (congrArg (fun w => w ∈ _) hedge)).trans ?_
    exact semidirectH1Equiv_mem_cuspidalFamily identityPlaneSplitting
      (identityPlaneCoefficientRep n) cuspGL _
  refine (locallyInner_iff_edge_mem_cuspidalFamily identityPlaneSplitting.conjAct n trivialCharacter
    Face.badPlaneFlag Face.badPlaneSemidirectEquiv (fun r e he => Face.badPlane_radical_fixes r e he)
    Face.badPlaneLeviEmbedding Face.badPlaneLeviEmbedding_injective (badPlaneH2Equiv n z)).trans ?_
  constructor
  · rintro ⟨hr, hmem⟩
    have hz := hrB_iff.mp hr
    exact ⟨hz, (key hz hr).mp hmem⟩
  · rintro ⟨hz, hm⟩
    have hr := hrB_iff.mpr hz
    exact ⟨hr, (key hz hr).mpr hm⟩

end TernaryPeriodPolynomials.Argument.SeedC3S4c
