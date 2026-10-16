module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Lit

@[expose] public section


/-!
# `K†` comparison, CMP-2 and CMP-3: the face dictionary and its naturality

`phiPlaneAt h`, `phiLineAt h`: the Shapiro coordinate of a `K†` stratum class at the plane (line) `h⁻¹⟨e₁,e₂⟩` (`h⁻¹ℚe₁`), restricted to
`Γ ∩ Γ(N)` and read in Mathlib's `H²` of the face group of `Γ(N)`.  `phiPlane`, `phiLine`: the vectors over the faces of `Γ(N)` (chosen representatives).
`phiPlane_globalCoordinates`, `phiLine_globalCoordinates`: for a global `K†`-cocycle `c`, they send its stratum coordinates to the
plane / line boundary `planeBoundary`, `lineBoundary` of the literal class `litAll [c]`.

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

section Faces

open scoped Classical

/-- **The plane coordinate of a `K†` stratum class at the plane `h⁻¹⟨e₁, e₂⟩`, read in `Γ(N)`'s plane group** (CMP-2). -/
def phiPlaneAt (h : SL(3, ℤ)) : StratumH2 n trivialCharacter .plane →ₗ[ℂ] groupCohomology.H2 (faceRep N h n) :=
  (planeH2Equiv N h3 h n trivialCharacter hN).toLinearMap ∘ₗ
    (resPrincipal N (planeFlagAt h) (rationalCoefficientComponent n trivialCharacter) ∘ₗ
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (planeFlagAt h))

/-- … line version. -/
def phiLineAt (h : SL(3, ℤ)) : StratumH2 n trivialCharacter .line →ₗ[ℂ] groupCohomology.H2 (lineFaceRep N h n) :=
  (lineH2Equiv N h3 h n trivialCharacter hN).toLinearMap ∘ₗ
    (resPrincipal N (lineFlagAt h) (rationalCoefficientComponent n trivialCharacter) ∘ₗ
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (lineFlagAt h))

/-- **The plane boundary of `Γ(N)` carried by a `K†` plane stratum class** (the faces of `Γ(N)` at the chosen representatives). -/
def phiPlane : StratumH2 n trivialCharacter .plane →ₗ[ℂ] PlaneFaceH2 N n :=
  ∑ i : PlaneFaces N, (DirectSum.lof ℂ (PlaneFaces N)
    (fun i => groupCohomology.H2 (faceRep N (planeFaceRepr i) n)) i).comp
      (phiPlaneAt N h3 hN n (planeFaceRepr i))

/-- … line version. -/
def phiLine : StratumH2 n trivialCharacter .line →ₗ[ℂ] LineFaceH2 N n :=
  ∑ i : LineFaces N, (DirectSum.lof ℂ (LineFaces N)
    (fun i => groupCohomology.H2 (lineFaceRep N i.rep n)) i).comp
      (phiLineAt N h3 hN n i.rep)

theorem phiPlane_apply (ξ : StratumH2 n trivialCharacter .plane) (i : PlaneFaces N) :
    phiPlane N h3 hN n ξ i = phiPlaneAt N h3 hN n (planeFaceRepr i) ξ := by
  simp only [phiPlane, LinearMap.sum_apply, LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [DFinsupp.finsetSum_apply]
  simp [DirectSum.of_apply]

theorem phiLine_apply (ξ : StratumH2 n trivialCharacter .line) (i : LineFaces N) :
    phiLine N h3 hN n ξ i = phiLineAt N h3 hN n i.rep ξ := by
  simp only [phiLine, LinearMap.sum_apply, LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [DFinsupp.finsetSum_apply]
  simp [DirectSum.of_apply]

end Faces


section Naturality

variable (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))

omit [NeZero N] in
/-- The Shapiro coordinate at `F`, restricted to `Γ ∩ Γ(N)`, of the stratum class of a global cocycle is the restriction of
the global class. -/
theorem resPrincipal_fixedPointH2_stratum {side : Side} (F : Flags side) :
    resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
      (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
          (restrictionCocycle n trivialCharacter side c))) =
      resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_self (levelPrincipal N) F)
        (resH2 (rationalCoefficientComponent n trivialCharacter) (levelPrincipal_le N)
          (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) := by
  have h1 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
        (restrictionCocycle n trivialCharacter side c)) =
      resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_level F)
        (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) := rfl
  rw [h1]
  unfold resPrincipal
  rw [resH2_comp, resH2_comp]

omit [NeZero N] in
theorem phiPlaneAt_stratum (h : SL(3, ℤ)) :
    phiPlaneAt N h3 hN n h
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
        (restrictionCocycle n trivialCharacter .plane c)) =
      rPlane N n h (litAll N h3 hN n (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) := by
  refine Eq.trans ?_ (congrArg (fun f => f (litAll N h3 hN n
    (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c))) (rPlane_eq_resAtC N n h)).symm
  refine Eq.trans ?_ (planeH2Equiv_res_classPrincipal N h n h3 hN _)
  rw [classPrincipal_litAll]
  exact congrArg (planeH2Equiv N h3 h n trivialCharacter hN) (resPrincipal_fixedPointH2_stratum N n c _)

omit [NeZero N] in
theorem phiLineAt_stratum (h : SL(3, ℤ)) :
    phiLineAt N h3 hN n h
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
        (restrictionCocycle n trivialCharacter .line c)) =
      rLine N n h (litAll N h3 hN n (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) := by
  refine Eq.trans ?_ (lineH2Equiv_res_classPrincipal N h3 hN n h _)
  rw [classPrincipal_litAll]
  exact congrArg (lineH2Equiv N h3 h n trivialCharacter hN) (resPrincipal_fixedPointH2_stratum N n c _)

/-- **CMP-3 (plane).** -/
theorem phiPlane_globalCoordinates :
    phiPlane N h3 hN n (globalCoordinates n trivialCharacter c).1 =
      planeBoundary N n (litAll N h3 hN n (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) := by
  ext1 i
  rw [phiPlane_apply, planeBoundary_apply]
  exact phiPlaneAt_stratum N h3 hN n c _

/-- **CMP-3 (line).** -/
theorem phiLine_globalCoordinates :
    phiLine N h3 hN n (globalCoordinates n trivialCharacter c).2 =
      lineBoundary N n (litAll N h3 hN n (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) := by
  ext1 i
  rw [phiLine_apply, lineBoundary_apply]
  exact phiLineAt_stratum N h3 hN n c _

end Naturality
end TernaryPeriodPolynomials.Argument.KDaggerComparison
