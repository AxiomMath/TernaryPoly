module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelDescent.LineData
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FrameLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeUniq

@[expose] public section


/-!
# The concrete data of the restriction of a plane face from level `N` to level `M`

Formalized by Claude Sonnet 5.5.

For `N ∣ M`, `M = N k`: the inclusion `Γ_{h⁻¹Ph}(M) ⊆ Γ_{h⁻¹Ph}(N)`, the scaling `r ↦ r^k` of the radical lattices (`radElt M r = radElt N (r^k)`), and the compatibilities with the extension data of `faceExt`, `faceSplitting`;
`planeFace_restrict_pairing`: the instance of the `facePairingCan_restrict`.
-/

open scoped MatrixGroups
noncomputable section

namespace TernaryPeriodPolynomials.Argument.LevelDescent

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.CuspidalInduction

section PlaneData

variable {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (h : SL(3, ℤ)) (n : ℕ)

/-- The inclusion of the plane group of level `M` into that of level `N`. -/
def planeIota : gammaNPAt M h →* gammaNPAt N h := Subgroup.inclusion (gammaNPAt_mono hNM h)

theorem plane_hinl (k : ℕ) (hk : M = N * k) (r : RadicalLattice) :
    planeIota hNM h ((faceExt M h).inl r) = (faceExt N h).inl (radScale k r) := by
  apply Subtype.ext
  change h⁻¹ * radElt M r * h = h⁻¹ * radElt N (radScale k r) * h
  congr 2
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [radElt, radScale, hk]; try ring)

theorem plane_hsplit (l : Gamma M) :
    planeIota hNM h ((faceSplitting M h) l) = (faceSplitting N h) (Subgroup.inclusion (Gamma_le_of_dvd hNM) l) :=
  Subtype.ext rfl

/-- The identity comparison of the coefficient modules (`faceRep M h n` is `faceRep N h n` restricted along `planeIota`). -/
def planeT : faceRep N h n →ₗ[ℂ] faceRep M h n := LinearMap.id

/-- The identity comparison of the contragredient coefficient modules. -/
def planeT' : dualRepG (faceRep N h n) →ₗ[ℂ] dualRepG (faceRep M h n) := LinearMap.id

omit [NeZero N] [NeZero M] in
theorem plane_hT (e : gammaNPAt M h) (v : faceRep N h n) :
    planeT (N := N) (M := M) h n ((faceRep N h n).ρ (planeIota hNM h e) v) = (faceRep M h n).ρ e (planeT (N := N) (M := M) h n v) := rfl

omit [NeZero N] [NeZero M] in
theorem plane_hT' (e : gammaNPAt M h) (v : dualRepG (faceRep N h n)) :
    planeT' (N := N) (M := M) h n ((dualRepG (faceRep N h n)).ρ (planeIota hNM h e) v) =
      (dualRepG (faceRep M h n)).ρ e (planeT' (N := N) (M := M) h n v) := rfl

omit [NeZero N] [NeZero M] in
theorem plane_hSe (a : faceRep N h n) (b : dualRepG (faceRep N h n)) :
    planeT' (N := N) (M := M) h n b (planeT (N := N) (M := M) h n a) = b a := rfl

variable [hN : Fact (3 ≤ N)] (hM3 : 3 ≤ M) [Fintype (Gamma N ⧸ CuspidalInduction.subM N M)]

/-- **Restriction of the canonical pairing of a plane face to the subface of level `M`** (instance of S1's `facePairingCan_restrict`). -/
theorem planeFace_restrict_pairing (k : ℕ) (hk : M = N * k) (hk0 : k ≠ 0)
    (x : SeedC3S4c.cuspidalSubspace (Gamma N) (splitRadicalH1Representation (faceSplitting N h) (faceRep N h n)))
    (y : SeedC3S4c.cuspidalSubspace (Gamma N) (splitRadicalH1Representation (faceSplitting N h) (dualRepG (faceRep N h n)))) :
    facePairingCan hM3 (faceSplitting M h) (planeFaceRadicalInput_det M h) (faceRep M h n)
        (RadicalInduction.mapCusp hM3 (Gamma_le_of_dvd hNM)
          (levTr (Gamma_le_of_dvd hNM) (faceSplitting N h) (faceSplitting M h) (planeIota hNM h) (radScale k)
            (plane_hinl hNM h k hk) (plane_hsplit hNM h) (faceRep N h n) (faceRep M h n) (planeT h n) (plane_hT hNM h n)) x)
        (RadicalInduction.mapCusp hM3 (Gamma_le_of_dvd hNM)
          (levTr (Gamma_le_of_dvd hNM) (faceSplitting N h) (faceSplitting M h) (planeIota hNM h) (radScale k)
            (plane_hinl hNM h k hk) (plane_hsplit hNM h) (dualRepG (faceRep N h n)) (dualRepG (faceRep M h n))
            (planeT' h n) (plane_hT' hNM h n)) y) =
      ((k : ℤ) * k : ℤ) * (Fintype.card (Gamma N ⧸ CuspidalInduction.subM N M) : ℂ) *
        facePairingCan hN.out (faceSplitting N h) (planeFaceRadicalInput_det N h) (faceRep N h n) x y := by
  have hD : radDet (radScale k) ≠ 0 := by
    rw [radDet_radScale]; exact mul_ne_zero (by exact_mod_cast hk0) (by exact_mod_cast hk0)
  have := facePairingCan_restrict (Gamma_le_of_dvd hNM) (faceSplitting N h) (faceSplitting M h) (planeIota hNM h) (radScale k)
    (plane_hinl hNM h k hk) (plane_hsplit hNM h) (faceRep N h n) (faceRep M h n) (planeT h n) (plane_hT hNM h n) hM3
    (planeT' h n) (plane_hT' hNM h n) (plane_hSe h n) (planeFaceRadicalInput_det N h) (planeFaceRadicalInput_det M h) hD x y
  rw [this, radDet_radScale]

end PlaneData

end TernaryPeriodPolynomials.Argument.LevelDescent
