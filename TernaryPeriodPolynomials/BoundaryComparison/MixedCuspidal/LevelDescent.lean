module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.BadPlaneLevelDescent
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.OtherFaceBridge
public import TernaryPeriodPolynomials.BoundaryComparison.MixedCuspidal.C3

@[expose] public section


/-!
# Lemma C.3: all four reference faces, every degree, and descent to `Γ(N)`

Paper: Lemma C.3 (`ar:lem:seed`).

* **Even degrees.**  `bad_plane_locally_inner_iff_general`: for every `n` (no parity hypothesis), a
  class of `H²(Λ₀, E_n)` is locally inner (in the face library) iff its radical restriction vanishes
  and its Hochschild--Serre edge lies in the literal mixed cuspidal group.  The radical condition is
  part of the definition of `𝒞_R(E) ↪ H²`; locally inner classes satisfy it because the
  radical fixes every complete flag over the face, so no vanishing statement is needed for even `n`.
* **The other reference faces.**  `bad_line_face_cuspidal_iff`, `good_plane_face_cuspidal_iff`,
  `good_line_face_cuspidal_iff`: `FaceCuspidal` is `cuspidalFamily` of `ℤˣ × binaryCuspLevel F`
  (bad line, good plane; Levi `ℤˣ × Γ₁'(3)`) resp. of the cusp stabilizers `cuspGL F` of `GL₂(ℤ)`
  (good line).
* **Descent** (the abstract version is `SeedC3S4c.edge_mem_cuspidalFamily_descent`).  At the identity
  plane: `bad_plane_level_descent`, `bad_plane_locally_inner_level_descent`,
  `bad_plane_locally_inner_iff_seed_span`: the level group's locally inner classes restrict into the
  mixed cuspidal group of the plane group `Γ(N) ∩ P(ℤ)`, and a class is locally inner iff that
  restriction lies in the span of the holomorphic and antiholomorphic seeds (unconditional).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalLevelDescent

open CategoryTheory
open GeneralEisenstein Matrix
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

/-- **Locally inner classes at the identity plane, every degree.** -/
theorem bad_plane_locally_inner_iff_general (n : ℕ)
    (z : groupCohomology.H2 (identityPlaneCoefficientRep n)) :
    SeedC3S4c.badPlaneH2Equiv n z ∈ locallyInnerClasses n trivialCharacter .plane
        FacePairingFull.Face.badPlaneFlag ↔
      ∃ hz : twoCohomologyRestriction identityPlaneExtension.inl
          (identityPlaneCoefficientRep n) z = 0,
        splitCohomologyEdge identityPlaneSplitting (identityPlaneCoefficientRep n) ⟨z, hz⟩ ∈
          SeedC3S4c.badPlaneCuspidal n :=
  SeedC3S4c.badPlaneH2Equiv_mem_locallyInner_iff_general n z

/-- **Standard bad line:** `FaceCuspidal` is the literal mixed cuspidal group for the cusp subgroups
`ℤˣ × binaryCuspLevel F`. -/
theorem bad_line_face_cuspidal_iff (n : ℕ) (character : RankOneCharacter)
    (y : CrossedH1 (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (FacePairingFull.Face.faceRep integralBadLineSplitting.conjAct n character standardBadLine
        standardBadLineSemidirectEquiv))) :
    y ∈ FacePairingFull.Face.FaceCuspidal integralBadLineSplitting.conjAct n character
        standardBadLine standardBadLineSemidirectEquiv ↔
      SeedC3S4c.leviMixedEquiv integralBadLineSplitting.conjAct
        (FacePairingFull.Face.faceRep integralBadLineSplitting.conjAct n character standardBadLine
          standardBadLineSemidirectEquiv) y ∈ SeedC3S4c.cuspidalFamily FacePairingFull.leviCusp
        (splitRadicalH1Representation
          (SemidirectProduct.inr_splitting integralBadLineSplitting.conjAct)
          (Rep.of (FacePairingFull.Face.faceRep integralBadLineSplitting.conjAct n character
            standardBadLine standardBadLineSemidirectEquiv))) :=
  SeedC3S4c.badLine_faceCuspidal_iff n character y

/-- **Good plane:** the same cusp subgroups `ℤˣ × binaryCuspLevel F`. -/
theorem good_plane_face_cuspidal_iff (n : ℕ) (character : RankOneCharacter)
    (y : CrossedH1 (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (FacePairingFull.Face.faceRep integralBadLineSplitting.conjAct n character
        FacePairingFull.Face.goodPlaneFlag FacePairingFull.Face.goodPlaneSemidirectEquiv))) :
    y ∈ FacePairingFull.Face.FaceCuspidal integralBadLineSplitting.conjAct n character
        FacePairingFull.Face.goodPlaneFlag FacePairingFull.Face.goodPlaneSemidirectEquiv ↔
      SeedC3S4c.leviMixedEquiv integralBadLineSplitting.conjAct
        (FacePairingFull.Face.faceRep integralBadLineSplitting.conjAct n character
          FacePairingFull.Face.goodPlaneFlag FacePairingFull.Face.goodPlaneSemidirectEquiv) y ∈
        SeedC3S4c.cuspidalFamily FacePairingFull.leviCusp
        (splitRadicalH1Representation
          (SemidirectProduct.inr_splitting integralBadLineSplitting.conjAct)
          (Rep.of (FacePairingFull.Face.faceRep integralBadLineSplitting.conjAct n character
            FacePairingFull.Face.goodPlaneFlag FacePairingFull.Face.goodPlaneSemidirectEquiv))) :=
  SeedC3S4c.goodPlane_faceCuspidal_iff n character y

/-- **Good line:** the cusp stabilizers `cuspGL F` of the Levi `GL₂(ℤ)`. -/
theorem good_line_face_cuspidal_iff (n : ℕ) (character : RankOneCharacter)
    (y : CrossedH1 (leviCrossedH1Representation goodLineSplitting.conjAct
      (FacePairingFull.Face.faceRep goodLineSplitting.conjAct n character
        FacePairingFull.Face.goodLineFlag FacePairingFull.Face.goodLineSemidirectEquivFixed))) :
    y ∈ FacePairingFull.Face.FaceCuspidal goodLineSplitting.conjAct n character
        FacePairingFull.Face.goodLineFlag FacePairingFull.Face.goodLineSemidirectEquivFixed ↔
      SeedC3S4c.leviMixedEquiv goodLineSplitting.conjAct
        (FacePairingFull.Face.faceRep goodLineSplitting.conjAct n character
          FacePairingFull.Face.goodLineFlag FacePairingFull.Face.goodLineSemidirectEquivFixed) y ∈
        SeedC3S4c.cuspidalFamily SeedC3S4c.cuspGL
        (splitRadicalH1Representation
          (SemidirectProduct.inr_splitting goodLineSplitting.conjAct)
          (Rep.of (FacePairingFull.Face.faceRep goodLineSplitting.conjAct n character
            FacePairingFull.Face.goodLineFlag FacePairingFull.Face.goodLineSemidirectEquivFixed))) :=
  SeedC3S4c.goodLine_faceCuspidal_iff n character y

/-- **Level descent of the mixed cuspidal condition at the identity plane.** -/
theorem bad_plane_level_descent (N n : ℕ) [NeZero N]
    (z : groupCohomology.H2 (identityPlaneCoefficientRep n))
    (hz : twoCohomologyRestriction identityPlaneExtension.inl (identityPlaneCoefficientRep n) z = 0) :
    splitCohomologyEdge identityPlaneSplitting (identityPlaneCoefficientRep n) ⟨z, hz⟩ ∈
        SeedC3S4c.badPlaneCuspidal n ↔
      SeedC3S4c.EdgeNat.h2Map (SeedC3S4c.gammaNToStab N) (identityPlaneCoefficientRep n)
        (SeedC3S4c.gammaNRep N n) LinearMap.id (SeedC3S4c.coeff_hT N n) z ∈
        SeedC3S4c.gammaNCuspidalInH2 N n :=
  SeedC3S4c.badPlane_level_descent N n z hz

/-- **Locally inner classes of the level group at the identity plane restrict into the mixed
cuspidal group of the plane group of `Γ(N)`, and conversely.** -/
theorem bad_plane_locally_inner_level_descent (N n : ℕ) [NeZero N]
    (z : groupCohomology.H2 (identityPlaneCoefficientRep n))
    (hz : twoCohomologyRestriction identityPlaneExtension.inl (identityPlaneCoefficientRep n) z = 0) :
    SeedC3S4c.badPlaneH2Equiv n z ∈ locallyInnerClasses n trivialCharacter .plane
        FacePairingFull.Face.badPlaneFlag ↔
      SeedC3S4c.EdgeNat.h2Map (SeedC3S4c.gammaNToStab N) (identityPlaneCoefficientRep n)
        (SeedC3S4c.gammaNRep N n) LinearMap.id (SeedC3S4c.coeff_hT N n) z ∈
        SeedC3S4c.gammaNCuspidalInH2 N n :=
  SeedC3S4c.badPlane_locallyInner_level_descent N n z hz

/-- **Locally inner classes at the identity plane are the classes whose restriction to the plane group
of `Γ(N)` lies in the span of the seeds** (unconditional; zero radical restriction, automatic for odd
`n`). -/
theorem bad_plane_locally_inner_iff_seed_span (N n : ℕ) [NeZero N]
    (z : groupCohomology.H2 (identityPlaneCoefficientRep n))
    (hz : twoCohomologyRestriction identityPlaneExtension.inl (identityPlaneCoefficientRep n) z = 0) :
    SeedC3S4c.badPlaneH2Equiv n z ∈ locallyInnerClasses n trivialCharacter .plane
        FacePairingFull.Face.badPlaneFlag ↔
      SeedC3S4c.EdgeNat.h2Map (SeedC3S4c.gammaNToStab N) (identityPlaneCoefficientRep n)
        (SeedC3S4c.gammaNRep N n) LinearMap.id (SeedC3S4c.coeff_hT N n) z ∈
        SeedC3S4c.gammaNSeedSpan N n := by
  rw [MixedCuspidalC3.seed_span_eq_mixedCuspidal_H2_gammaN]
  exact SeedC3S4c.badPlane_locallyInner_level_descent N n z hz

end TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalLevelDescent
