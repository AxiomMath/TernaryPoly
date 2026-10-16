module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaceTransfer
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.BadPlaneLevelDescentFull
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ReferencePlanes
public import TernaryPeriodPolynomials.BoundaryComparison.MixedCuspidal.C3

@[expose] public section


/-!
# Lemma C.3: level descent and transfer at every plane cusp

Paper: Lemma C.3 (`ar:lem:seed`).

Let `Γ` be the paper's level group, `N ≥ 3` with `3 ∣ N`, `h ∈ SL₃(ℤ)` an integral change of basis,
`F = h⁻¹⟨e₁, e₂⟩` the corresponding rational plane, `Γ_F` its stabilizer in `Γ`, and
`H²(Γ(N) ∩ h⁻¹Ph, E_n)` Mathlib's cohomology of the plane group of `Γ(N)`.  All statements are
unconditional (Eichler--Shimura spanning for `Γ(N)` is proved) and hold for every plane cusp, the good
plane and the bad plane included, with no presentation of `Γ_F` as a semidirect product.

* `locally_inner_iff_restriction_in_seed_span`: a class of the face library's `H²(Γ_F, E)` is locally
  inner iff its restriction to `Γ_F ∩ Γ(N)`, read in Mathlib's `H²` of the plane group, lies in the span of
  the holomorphic and antiholomorphic seeds;
* `locally_inner_iff_transfer_of_seed_span`: **iff it is the transfer (corestriction, `planeTransfer`)
  of an element of the seed span**: the level group's `𝒞_P(E)` is spanned by the transfers of the `Γ(N)`
  seeds;
* `mem_map_locally_inner_iff_seed_span_invariant`: `𝒞(Γ) = 𝒞(Γ(N))^{invariants}`;
* `locally_inner_level_descent`, `locally_inner_eq_transfer` (any flag, in the homogeneous model): the
  presentation-free statements for every face of every type (planes and lines);
* `bad_plane_level_descent_full`: the identity-plane descent with no hypothesis on the radical.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalTransfer

open GeneralEisenstein Matrix
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

section Planes

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (h : SL(3, ℤ)) (n : ℕ)
  (character : RankOneCharacter)

/-- **Locally inner classes at the plane cusp `h⁻¹Ph` restrict into the span of the `Γ(N)` seeds, and
conversely.** -/
theorem locally_inner_iff_restriction_in_seed_span
    (x : Homogeneous.H2 (fixedPointLevel rationalLevel (SeedC3S4c.planeFlagAt h))
      (rationalCoefficientComponent n character)) :
    x ∈ locallyInnerClasses n character .plane (SeedC3S4c.planeFlagAt h) ↔
      SeedC3S4c.planeH2Equiv N h3 h n character hN
        (SeedC3S4c.resPrincipal N (SeedC3S4c.planeFlagAt h)
          (rationalCoefficientComponent n character) x) ∈ SeedC3S4c.faceSeedSpan N h n := by
  rw [MixedCuspidalC3.seed_span_eq_mixedCuspidal_H2_cusp]
  exact SeedC3S4c.locallyInnerClasses_planeFlag_iff N h3 h n character hN x

/-- **The level group's `𝒞_P(E)` at the plane `h⁻¹⟨e₁,e₂⟩` is spanned by the transfers of the seeds
of `Γ(N)`.** -/
theorem locally_inner_iff_transfer_of_seed_span
    (x : Homogeneous.H2 (fixedPointLevel rationalLevel (SeedC3S4c.planeFlagAt h))
      (rationalCoefficientComponent n character)) :
    x ∈ locallyInnerClasses n character .plane (SeedC3S4c.planeFlagAt h) ↔
      ∃ y ∈ SeedC3S4c.faceSeedSpan N h n,
        SeedC3S4c.planeTransfer N h3 hN h n character y = x := by
  rw [MixedCuspidalC3.seed_span_eq_mixedCuspidal_H2_cusp]
  exact SeedC3S4c.locallyInnerClasses_planeFlag_eq_transfer N h3 hN h n character x

/-- **`𝒞(Γ) = 𝒞(Γ(N))^{invariants}`** at the plane cusp `h⁻¹Ph`. -/
theorem mem_map_locally_inner_iff_seed_span_invariant
    (y : groupCohomology.H2 (SeedC3S4c.faceRep N h n)) :
    y ∈ Submodule.map
        ((SeedC3S4c.planeH2Equiv N h3 h n character hN).toLinearMap ∘ₗ
          SeedC3S4c.resPrincipal N (SeedC3S4c.planeFlagAt h)
            (rationalCoefficientComponent n character))
        (locallyInnerClasses n character .plane (SeedC3S4c.planeFlagAt h)) ↔
      y ∈ SeedC3S4c.faceSeedSpan N h n ∧
        (SeedC3S4c.planeH2Equiv N h3 h n character hN).symm y ∈
          LevelTransfer.invariantsH2 (rationalCoefficientComponent n character)
            (SeedC3S4c.fixedPointLevel_hnorm (SeedC3S4c.levelPrincipal N)
              (SeedC3S4c.levelPrincipal_norm N) (SeedC3S4c.planeFlagAt h)) := by
  rw [MixedCuspidalC3.seed_span_eq_mixedCuspidal_H2_cusp]
  exact SeedC3S4c.mem_map_locallyInnerClasses_planeFlag_iff N h3 h n character hN y

end Planes

section AnyFlag

variable (N : ℕ) [NeZero N] {side : Side} (flag : Flags side) (degree : ℕ)
  (character : RankOneCharacter)

/-- **Presentation-free level descent at every flag.** -/
theorem locally_inner_level_descent
    (x : Homogeneous.H2 (fixedPointLevel rationalLevel flag)
      (rationalCoefficientComponent degree character)) :
    x ∈ locallyInnerClasses degree character side flag ↔
      SeedC3S4c.resPrincipal N flag (rationalCoefficientComponent degree character) x ∈
        SeedC3S4c.locallyInnerAt (rationalCoefficientComponent degree character)
          (SeedC3S4c.levelPrincipal N) flag :=
  SeedC3S4c.locallyInnerClasses_level_descent N degree character flag x

/-- **`𝒞(Γ_F) = tr(𝒞(Γ_F ∩ Γ(N)))` at every flag.** -/
theorem locally_inner_eq_transfer :
    locallyInnerClasses degree character side flag =
      Submodule.map (SeedC3S4c.trLevel (rationalCoefficientComponent degree character)
          (SeedC3S4c.levelPrincipal N) (SeedC3S4c.levelPrincipal_le N)
          (SeedC3S4c.levelPrincipal_norm N) flag)
        (SeedC3S4c.locallyInnerAt (rationalCoefficientComponent degree character)
          (SeedC3S4c.levelPrincipal N) flag) :=
  (SeedC3S4c.map_trH2_locallyInnerAt (rationalCoefficientComponent degree character)
    (SeedC3S4c.levelPrincipal N) (SeedC3S4c.levelPrincipal_le N)
    (SeedC3S4c.levelPrincipal_norm N) flag).symm

end AnyFlag

/-- **Identity-plane level descent with no hypothesis on the radical restriction**, every `n`. -/
theorem bad_plane_level_descent_full (N n : ℕ) [NeZero N]
    (z : groupCohomology.H2 (TernaryPeriodPolynomials.SphericalDetection.Helpers.identityPlaneCoefficientRep n)) :
    SeedC3S4c.badPlaneH2Equiv n z ∈ locallyInnerClasses n trivialCharacter .plane
        FacePairingFull.Face.badPlaneFlag ↔
      SeedC3S4c.EdgeNat.h2Map (SeedC3S4c.gammaNToStab N)
        (TernaryPeriodPolynomials.SphericalDetection.Helpers.identityPlaneCoefficientRep n) (SeedC3S4c.gammaNRep N n)
        LinearMap.id (SeedC3S4c.coeff_hT N n) z ∈ SeedC3S4c.gammaNCuspidalInH2 N n :=
  SeedC3S4c.badPlane_locallyInner_level_descent_full N n z

section Reference

/-- The standard plane `⟨e₁, e₂⟩` is `planeFlagAt 1`. -/
theorem plane_flag_at_one : SeedC3S4c.planeFlagAt 1 = FacePairingFull.Face.badPlaneFlag :=
  SeedC3S4c.planeFlagAt_one

/-- The good plane `⟨e₃, e₂⟩` is `planeFlagAt wGood`. -/
theorem plane_flag_at_w_good :
    SeedC3S4c.planeFlagAt SeedC3S4c.wGood = FacePairingFull.Face.goodPlaneFlag :=
  SeedC3S4c.planeFlagAt_wGood

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ) (character : RankOneCharacter)

/-- **The level group's `𝒞_P(E)` at the bad plane is spanned by the transfers of the `Γ(N)` seeds.** -/
theorem bad_plane_locally_inner_iff_transfer_of_seed_span
    (x : Homogeneous.H2 (fixedPointLevel rationalLevel (SeedC3S4c.planeFlagAt 1))
      (rationalCoefficientComponent n character)) :
    x ∈ locallyInnerClasses n character .plane (SeedC3S4c.planeFlagAt 1) ↔
      ∃ y ∈ SeedC3S4c.faceSeedSpan N 1 n,
        SeedC3S4c.planeTransfer N h3 hN 1 n character y = x :=
  locally_inner_iff_transfer_of_seed_span N h3 hN 1 n character x

/-- **The same at the good plane.** -/
theorem good_plane_locally_inner_iff_transfer_of_seed_span
    (x : Homogeneous.H2 (fixedPointLevel rationalLevel (SeedC3S4c.planeFlagAt SeedC3S4c.wGood))
      (rationalCoefficientComponent n character)) :
    x ∈ locallyInnerClasses n character .plane (SeedC3S4c.planeFlagAt SeedC3S4c.wGood) ↔
      ∃ y ∈ SeedC3S4c.faceSeedSpan N SeedC3S4c.wGood n,
        SeedC3S4c.planeTransfer N h3 hN SeedC3S4c.wGood n character y = x :=
  locally_inner_iff_transfer_of_seed_span N h3 hN SeedC3S4c.wGood n character x

end Reference

end TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalTransfer
