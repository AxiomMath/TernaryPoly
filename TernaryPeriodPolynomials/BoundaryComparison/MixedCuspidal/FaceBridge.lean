module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.BadPlaneFaceBridge

@[expose] public section


/-!
# Lemma C.3: the face library's mixed cuspidal group is the literal one

Paper: Lemma C.3 (`ar:lem:seed`).

The library has two models of `𝒞_R(E) ⊂ H¹(L_R, H¹(N_R, E))`: Mathlib's `groupCohomology` on a
`GroupExtension` (`cuspidalFamily`, `splitCohomologyEdge`; used by the seed statements) and the
crossed-homomorphism model on a `SemidirectProduct` of the face library (`FaceCuspidal`,
`locallyInnerClasses`).  For an arbitrary semidirect product `Radical ⋊ Levi` with a representation
`ρ`:

* `crossed_model_cuspidal_iff`, `face_cuspidal_is_literal`: the crossed model's cuspidal condition is
  `cuspidalFamily` under the isomorphism `leviMixedEquiv`;
* `crossed_mixed_class_is_edge`: the face library's mixed class `radicalKernelMixedMap` is the
  Hochschild--Serre edge `splitCohomologyEdge`;
* `locally_inner_iff_cuspidal_edge`: a face class is locally inner iff its edge is cuspidal;
* `semidirect_model_cuspidal_iff`: passing from a split extension to its semidirect product model
  preserves the cuspidal group;

and at the identity plane of the paper's level group (`Λ₀ = ℤ² ⋊ GL₂(ℤ)`, trivial character):

* `bad_plane_face_cuspidal_iff`: `FaceCuspidal` is the literal group `badPlaneCuspidal` (the Levi parts
  of the stabilizers of the complete flags over the plane are exactly the cusp stabilizers `cuspGL F`);
* `bad_plane_locally_inner_iff`: for odd `n > 0`, `locallyInnerClasses` of the face library is the
  image of `badPlaneCuspidalInH2`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalFaceBridge

open CategoryTheory
open GeneralEisenstein Matrix
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

section Generic

variable {Radical Levi V : Type} [Group Radical] [Group Levi] [AddCommGroup V] [Module ℂ V]
  (action : Levi →* MulAut Radical)
  (ρ : Representation ℂ (SemidirectProduct Radical Levi action) V)

/-- A class of the crossed model `H¹(Levi, H¹(Radical, E))` restricts to zero on every member of a
family of cusp subgroups iff its coordinate in Mathlib's `H¹` lies in `cuspidalFamily`. -/
theorem crossed_model_cuspidal_iff {ι : Type} (B : ι → Subgroup Levi)
    (x : CrossedH1 (leviCrossedH1Representation action ρ)) :
    SeedC3S4c.leviMixedEquiv action ρ x ∈ SeedC3S4c.cuspidalFamily B
        (splitRadicalH1Representation (SemidirectProduct.inr_splitting action) (Rep.of ρ)) ↔
      x ∈ ⨅ i, LinearMap.ker
        (crossedPullbackH1 (B i).subtype (leviCrossedH1Representation action ρ)) :=
  SeedC3S4c.leviMixedEquiv_mem_cuspidalFamily action ρ B x

/-- The face library's mixed class is the Hochschild--Serre edge of the split extension. -/
theorem crossed_mixed_class_is_edge (x : (radicalRestrictionH2 action ρ).ker) :
    SeedC3S4c.leviMixedEquiv action ρ (radicalKernelMixedMap action ρ x) =
      splitCohomologyEdge (SemidirectProduct.inr_splitting action) (Rep.of ρ)
        ⟨SeedC3S4c.h2Equiv ρ x.1, SeedC3S4c.h2Equiv_mem_ker action ρ x⟩ :=
  SeedC3S4c.leviMixedEquiv_radicalKernelMixedMap action ρ x

end Generic

section Face

variable {Radical Levi : Type} [Group Radical] [Group Levi] (action : Levi →* MulAut Radical)
  (degree : ℕ) (character : RankOneCharacter) {side : Side} (F : Flags side)
  (ι : SemidirectProduct Radical Levi action ≃* fixedPointLevel rationalLevel F)

/-- **`FaceCuspidal` is the literal mixed cuspidal group.** -/
theorem face_cuspidal_is_literal :
    Submodule.map (SeedC3S4c.leviMixedEquiv action
        (FacePairingFull.Face.faceRep action degree character F ι)).toLinearMap
      (FacePairingFull.Face.FaceCuspidal action degree character F ι) =
      SeedC3S4c.cuspidalFamily
        (fun e : {e : Edges // endpoint side e = F} =>
          FacePairingFull.Face.faceCusp action F ι e.1)
        (splitRadicalH1Representation (SemidirectProduct.inr_splitting action)
          (Rep.of (FacePairingFull.Face.faceRep action degree character F ι))) :=
  SeedC3S4c.faceCuspidal_map_eq action degree character F ι

/-- **Locally inner classes are the classes with cuspidal Hochschild--Serre edge.** -/
theorem locally_inner_iff_cuspidal_edge
    (hfix : ∀ radical : Radical, ∀ e : Edges, endpoint side e = F →
      (ι (SemidirectProduct.inl radical)).val • e = e)
    (ψ : Levi →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (injective : Function.Injective ψ)
    (coordinate : Homogeneous.H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character)) :
    coordinate ∈ locallyInnerClasses degree character side F ↔
      ∃ hr : FacePairingFull.Face.faceH2Equiv action degree character F ι coordinate ∈
          (radicalRestrictionH2 action
            (FacePairingFull.Face.faceRep action degree character F ι)).ker,
        splitCohomologyEdge (SemidirectProduct.inr_splitting action)
            (Rep.of (FacePairingFull.Face.faceRep action degree character F ι))
            ⟨SeedC3S4c.h2Equiv (FacePairingFull.Face.faceRep action degree character F ι)
              (FacePairingFull.Face.faceH2Equiv action degree character F ι coordinate),
              SeedC3S4c.h2Equiv_mem_ker action _
                ⟨FacePairingFull.Face.faceH2Equiv action degree character F ι coordinate, hr⟩⟩ ∈
          SeedC3S4c.cuspidalFamily
            (fun e : {e : Edges // endpoint side e = F} =>
              FacePairingFull.Face.faceCusp action F ι e.1)
            (splitRadicalH1Representation (SemidirectProduct.inr_splitting action)
              (Rep.of (FacePairingFull.Face.faceRep action degree character F ι))) :=
  SeedC3S4c.locallyInner_iff_edge_mem_cuspidalFamily action degree character F ι hfix ψ injective
    coordinate

end Face

section Semidirect

variable {N E L : Type} [Group N] [Group E] [Group L] {ext : GroupExtension N E L}
  (s : ext.Splitting) (ρ : Rep ℂ E)

/-- The cuspidal group is the same on a split extension and on its semidirect product model. -/
theorem semidirect_model_cuspidal_iff {ι : Type} (B : ι → Subgroup L)
    (x : groupCohomology.H1 (splitRadicalH1Representation s ρ)) :
    SeedC3S4c.semidirectH1Equiv s ρ x ∈ SeedC3S4c.cuspidalFamily B
        (splitRadicalH1Representation (SemidirectProduct.inr_splitting s.conjAct)
          (SeedC3S4c.semidirectRep s ρ)) ↔
      x ∈ SeedC3S4c.cuspidalFamily B (splitRadicalH1Representation s ρ) :=
  SeedC3S4c.semidirectH1Equiv_mem_cuspidalFamily s ρ B x

end Semidirect

section BadPlane

/-- **At the identity plane `FaceCuspidal` is the literal mixed cuspidal group** `badPlaneCuspidal`
(`n`-th symmetric power, trivial character, Levi `GL₂(ℤ)`). -/
theorem bad_plane_face_cuspidal_iff (n : ℕ)
    (y : CrossedH1 (leviCrossedH1Representation identityPlaneSplitting.conjAct
      (FacePairingFull.Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter
        FacePairingFull.Face.badPlaneFlag FacePairingFull.Face.badPlaneSemidirectEquiv))) :
    y ∈ FacePairingFull.Face.FaceCuspidal identityPlaneSplitting.conjAct n trivialCharacter
        FacePairingFull.Face.badPlaneFlag FacePairingFull.Face.badPlaneSemidirectEquiv ↔
      (SeedC3S4c.semidirectH1Equiv identityPlaneSplitting (identityPlaneCoefficientRep n)).symm
        (SeedC3S4c.leviMixedEquiv identityPlaneSplitting.conjAct
          (FacePairingFull.Face.faceRep identityPlaneSplitting.conjAct n trivialCharacter
            FacePairingFull.Face.badPlaneFlag FacePairingFull.Face.badPlaneSemidirectEquiv) y) ∈
        SeedC3S4c.badPlaneCuspidal n :=
  SeedC3S4c.badPlane_faceCuspidal_iff n y

/-- **At the identity plane the locally inner classes are the classes with edge in the literal mixed
cuspidal group** (odd `n > 0`): `badPlaneH2Equiv` identifies Mathlib's `H²(Λ₀, E_n)` with the face
library's `H²` of the stabilizer of the identity plane, and carries `badPlaneCuspidalInH2` onto
`locallyInnerClasses`. -/
theorem bad_plane_locally_inner_iff (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (z : groupCohomology.H2 (identityPlaneCoefficientRep n)) :
    SeedC3S4c.badPlaneH2Equiv n z ∈ locallyInnerClasses n trivialCharacter .plane
        FacePairingFull.Face.badPlaneFlag ↔
      z ∈ SeedC3S4c.badPlaneCuspidalInH2 n hn hodd :=
  SeedC3S4c.badPlaneH2Equiv_mem_locallyInner_iff n hn hodd z

end BadPlane

end TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalFaceBridge
