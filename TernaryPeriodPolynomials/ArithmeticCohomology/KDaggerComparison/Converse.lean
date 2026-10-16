module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Inner
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Faces

@[expose] public section


/-!
# `K†` comparison, CMP-4 (converse): zero flag restrictions give `InnerBoundary`

`innerBoundary_of_zeroFlags`: if the literal class of a global `K†`-cocycle has zero flag restrictions, both stratum coordinates are `InnerBoundary`.
`zeroFlags_litAll_of_inner_line`, `zeroFlags_litAll_iff`: the three conditions (zero flags, plane `InnerBoundary`, line `InnerBoundary`) are equivalent.

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

section Converse

include h3 hN in
/-- A global `K†`-cocycle whose literal class has zero flag restrictions has `InnerBoundary` coordinates on both sides
(**CMP-4, converse**): restriction to the stabilizer of a complete flag vanishes on `Γ ∩ Γ(N)`, hence on `K†` (level descent). -/
theorem innerBoundary_of_zeroFlags (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hz : ZeroFlags N n (litAll N h3 hN n (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c))) :
    InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 ∧
      InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 := by
  have hpli : PlaneLocallyInner N h3 hN n
      (litClass N h3 hN n (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) := by
    refine (planeLocallyInner_iff_cusps N n h3 hN _).mpr fun h => ?_
    have hm := ((zeroFlags_iff_mixed N n hN _).mp hz).2 h
    have hm' : resAtC N h n (litClass N h3 hN n
        (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) ∈ faceCuspidalInH2 N h n := by
      have := LinearMap.congr_fun (rPlane_eq_resAtC N n h)
        (litClass N h3 hN n (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c))
      exact this ▸ hm
    rwa [faceCuspidalInH2_eq_locallyInner] at hm'
  have he : ∀ e : Edges, resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_level e)
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0 := by
    intro e
    refine res_level_injective (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N)
      (levelPrincipal_le N) (levelPrincipal_norm N) e ?_
    have h1 := classPrincipal_edge_vanishing N h3 hN n _ hpli e
    rw [classPrincipal_litClass] at h1
    rw [map_zero, resH2_comp]
    rw [resH2_comp] at h1
    exact h1
  exact ⟨innerBoundary_of_edgeVanishing n trivialCharacter .plane c he,
    innerBoundary_of_edgeVanishing n trivialCharacter .line c he⟩

include h3 hN in
/-- The same from the line coordinate alone. -/
theorem zeroFlags_litAll_of_inner_line (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hin : InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2) :
    ZeroFlags N n (litAll N h3 hN n (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) := by
  refine zeroFlags_of_line_mixed N n hN _ fun h => ?_
  have h1 : phiLineAt N h3 hN n h (globalCoordinates n trivialCharacter c).2 ∈ lineFaceCuspidalInH2 N h n :=
    (locallyInnerClasses_lineFlag_iff N h3 h n trivialCharacter hN
      (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (lineFlagAt h)
        (globalCoordinates n trivialCharacter c).2)).mp
      ((innerBoundary_iff_locallyInner _).mp hin (lineFlagAt h))
  have h2 := phiLineAt_stratum N h3 hN n c h
  exact h2 ▸ h1

include h3 hN in
/-- **CMP-4.** For a global `K†`-cocycle, zero flag restrictions of its literal class, `InnerBoundary` of the plane coordinate and
`InnerBoundary` of the line coordinate are equivalent. -/
theorem zeroFlags_litAll_iff (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    ZeroFlags N n (litAll N h3 hN n (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) ↔
      InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 ∧
        InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 :=
  ⟨innerBoundary_of_zeroFlags N h3 hN n c, fun h => zeroFlags_litAll_of_inner N h3 hN n c h.1⟩

end Converse
end TernaryPeriodPolynomials.Argument.KDaggerComparison
