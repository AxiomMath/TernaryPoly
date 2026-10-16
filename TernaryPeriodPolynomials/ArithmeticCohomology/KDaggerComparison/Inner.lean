module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Faces

@[expose] public section


/-!
# `K†` comparison, CMP-4 (forward): `InnerBoundary` gives zero flag restrictions and mixed cuspidal faces

`zeroFlags_litAll_of_inner`: a global `K†`-cocycle whose plane coordinate is `InnerBoundary` has a literal class with zero flag restrictions.
`phiPlane_mem_range`, `phiLine_mem_range`: the `Γ(N)` boundary of an `InnerBoundary` stratum class lies in the image of `𝒞_P(E)`, `𝒞_Q(E)`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

section Inner

theorem planeLocallyInner_litClass_of_inner
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hin : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1) :
    PlaneLocallyInner N h3 hN n
      (litClass N h3 hN n (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) := by
  intro F
  rw [classPrincipal_litClass]
  have h1 := (innerBoundary_iff_locallyInner _).mp hin F
  have h2 := (locallyInnerClasses_level_descent N n trivialCharacter F _).mp h1
  have h4 : resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
      (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F
        (globalCoordinates n trivialCharacter c).1) =
      resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_self (levelPrincipal N) F)
        (resH2 (rationalCoefficientComponent n trivialCharacter) (levelPrincipal_le N)
          (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) :=
    resPrincipal_fixedPointH2_stratum N n c F
  rw [h4] at h2
  exact h2

/-- **CMP-4 (forward).** A global cocycle whose plane coordinate is `InnerBoundary` has a literal `Γ(N)` class with zero flag
restrictions. -/
theorem zeroFlags_litAll_of_inner
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hin : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1) :
    ZeroFlags N n (litAll N h3 hN n (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) := by
  refine zeroFlags_of_plane_mixed N n hN _ fun h => ?_
  have h5 := (planeLocallyInner_iff_cusps N n h3 hN _).mp (planeLocallyInner_litClass_of_inner N h3 hN n c hin) h
  show resAtC N h n (litClass N h3 hN n _) ∈ faceCuspidalInH2 N h n
  rwa [faceCuspidalInH2_eq_locallyInner]

/-- The `Γ(N)` plane vector of an `InnerBoundary` plane stratum class lies in the image of `𝒞_P(E)`. -/
theorem phiPlane_mem_range (ξ : StratumH2 n trivialCharacter .plane)
    (hξ : InnerBoundary n trivialCharacter .plane ξ) :
    phiPlane N h3 hN n ξ ∈ LinearMap.range (planeCuspSumEmbedding N n) := by
  rw [mem_range_planeCuspSumEmbedding]
  intro i
  rw [phiPlane_apply]
  exact (locallyInnerClasses_planeFlag_iff N h3 (planeFaceRepr i) n trivialCharacter hN _).mp
    ((innerBoundary_iff_locallyInner ξ).mp hξ _)

/-- The same for lines. -/
theorem phiLine_mem_range (ξ : StratumH2 n trivialCharacter .line)
    (hξ : InnerBoundary n trivialCharacter .line ξ) :
    phiLine N h3 hN n ξ ∈ LinearMap.range (lineCuspSumEmbedding N n) := by
  rw [mem_range_lineCuspSumEmbedding]
  intro i
  rw [phiLine_apply]
  exact (locallyInnerClasses_lineFlag_iff N h3 i.rep n trivialCharacter hN _).mp
    ((innerBoundary_iff_locallyInner ξ).mp hξ _)

end Inner
end TernaryPeriodPolynomials.Argument.KDaggerComparison
