module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Faces
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Cosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Orbits

@[expose] public section


/-!
# `K†` comparison (injectivity): the face dictionary loses nothing

`eq_zero_of_phiPlane_eq_zero`, `eq_zero_of_phiLine_eq_zero`: a `K†` stratum class whose `Γ(N)` plane (line) boundary at the chosen
representatives vanishes is zero.  Uses the Shapiro injectivity `eq_zero_iff_fixedPointH2`, level descent `res_level_injective`, and the transport
along the `Γ(N)`-orbit of the representative (`stabilizerTransportH2_fixedPointH2`).  `lineFlagAt_surjective`: every rational line is `h⁻¹ℚe₁`.

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

section Injective

omit [NeZero N] in
include h3 in
theorem fixedPointH2_eq_zero_of_orbit {side : Side} (ξ : StratumH2 n trivialCharacter side)
    (F₁ F₂ : Flags side) (γ : SL(3, ℤ)) (hγ : γ ∈ gammaN N) (hF : F₂ = Matrix.SpecialLinearGroup.mapGL ℚ γ • F₁)
    (h : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F₁ ξ = 0) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F₂ ξ = 0 := by
  have hmem : Matrix.SpecialLinearGroup.mapGL ℚ γ ∈ rationalLevel :=
    levelPrincipal_le N (mapGL_mem_levelPrincipal N h3 hγ)
  have := stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
    ⟨Matrix.SpecialLinearGroup.mapGL ℚ γ, hmem⟩ F₁ F₂ hF.symm ξ
  rw [← this, h, map_zero]

theorem fixedPointH2_eq_zero_of_res {side : Side} (ξ : StratumH2 n trivialCharacter side) (F : Flags side)
    (h : resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
      (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F ξ) = 0) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F ξ = 0 :=
  res_level_injective (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N)
    (levelPrincipal_le N) (levelPrincipal_norm N) F (h.trans (map_zero _).symm)

/-- **Injectivity of the plane dictionary (CMP-2).** A plane stratum class whose `Γ(N)` plane boundary vanishes is zero. -/
theorem eq_zero_of_phiPlane_eq_zero (ξ : StratumH2 n trivialCharacter .plane)
    (h0 : phiPlane N h3 hN n ξ = 0) : ξ = 0 := by
  refine (eq_zero_iff_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) ξ).mpr ?_
  intro F
  obtain ⟨h, rfl⟩ := planeFlagAt_surjective F
  set i : PlaneFaces N := Quotient.mk (planeFaceSetoid N) h with hi
  obtain ⟨γ, hγ, hF⟩ := (planeFlagAt_orbit_iff N h (planeFaceRepr i)).mpr
    ((planeFaceSetoid N).iseqv.symm (Quotient.mk_out (s := planeFaceSetoid N) h))
  have h1 : phiPlaneAt N h3 hN n (planeFaceRepr i) ξ = 0 := by
    have := congrArg (fun v => v i) h0
    simpa [phiPlane_apply] using this
  have h2 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (planeFlagAt (planeFaceRepr i)) ξ = 0 := by
    refine fixedPointH2_eq_zero_of_res N n ξ _ ?_
    exact (planeH2Equiv N h3 (planeFaceRepr i) n trivialCharacter hN).map_eq_zero_iff.mp h1
  refine fixedPointH2_eq_zero_of_orbit N h3 n ξ (planeFlagAt (planeFaceRepr i)) (planeFlagAt h) γ⁻¹
    ((gammaN N).inv_mem hγ) ?_ h2
  rw [hF, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

theorem stdLine_eq_standardLine : TernaryPeriodPolynomials.Argument.GammaNStokes.stdLine =
    TernaryPoly.SymmetricSpaceBoundaryFaces.standardLine := by
  apply Subtype.ext
  ext v
  change v ∈ Submodule.span ℚ {TernaryPeriodPolynomials.Argument.GammaNStokes.e0} ↔
    v ∈ TernaryPoly.RelativeStabilizerCoordinates.L0
  rw [TernaryPoly.RelativeStabilizerCoordinates.mem_L0, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp [TernaryPeriodPolynomials.Argument.GammaNStokes.e0]
  · rintro ⟨h1, h2⟩
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [TernaryPeriodPolynomials.Argument.GammaNStokes.e0, h1, h2]

/-- Every rational line is `h⁻¹ℚe₁` for an integral change of basis `h ∈ SL₃(ℤ)`, as a line flag. -/
theorem lineFlagAt_surjective (F : Flags .line) : ∃ h : SL(3, ℤ), lineFlagAt h = F := by
  obtain ⟨h, hh⟩ := TernaryPeriodPolynomials.Argument.GammaNStokes.exists_lineOf
    (TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.flagLine F)
  refine ⟨h, TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.flagLine_injective ?_⟩
  change TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.flagLine
    (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)) = _
  rw [TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.flagLine_mk]
  have e : TernaryPoly.SymmetricSpaceBoundaryFaces.lineLabel (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) =
      TernaryPeriodPolynomials.Argument.GammaNStokes.lineOf h := by
    unfold TernaryPoly.SymmetricSpaceBoundaryFaces.lineLabel TernaryPeriodPolynomials.Argument.GammaNStokes.lineOf
    rw [stdLine_eq_standardLine]
  rw [e]
  exact hh

omit [NeZero N] in
theorem lineFlagAt_rep (h : SL(3, ℤ)) :
    ∃ γ ∈ gammaN N, lineFlagAt (LineFaces.mk (N := N) h).rep =
      Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹ • lineFlagAt h := by
  obtain ⟨q, hq, γ, hγ, e⟩ := LineFaces.rel_rep (N := N) h
  refine ⟨γ, hγ, ?_⟩
  rw [e]
  change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ (q * h * γ)⁻¹) : Flags .line) =
    (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) : Flags .line)
  apply QuotientGroup.eq.mpr
  have hq' : Matrix.SpecialLinearGroup.mapGL ℚ q ∈ parabolic .line := by
    refine ⟨?_, ?_⟩
    · change (((q : Matrix (Fin 3) (Fin 3) ℤ) 1 0 : ℤ) : ℚ) = 0
      rw [hq.1]; simp
    · change (((q : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℤ) : ℚ) = 0
      rw [hq.2]; simp
  have : (Matrix.SpecialLinearGroup.mapGL ℚ (q * h * γ)⁻¹)⁻¹ *
      (Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) =
      Matrix.SpecialLinearGroup.mapGL ℚ q := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  rw [this]
  exact hq'

/-- **Injectivity of the line dictionary (CMP-2).** -/
theorem eq_zero_of_phiLine_eq_zero (ξ : StratumH2 n trivialCharacter .line)
    (h0 : phiLine N h3 hN n ξ = 0) : ξ = 0 := by
  refine (eq_zero_iff_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) ξ).mpr ?_
  intro F
  obtain ⟨h, rfl⟩ := lineFlagAt_surjective F
  set i : LineFaces N := LineFaces.mk h with hi
  obtain ⟨γ, hγ, hF⟩ := lineFlagAt_rep N h
  have h1 : phiLineAt N h3 hN n i.rep ξ = 0 := by
    have := congrArg (fun v => v i) h0
    simpa [phiLine_apply] using this
  have h2 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (lineFlagAt i.rep) ξ = 0 := by
    refine fixedPointH2_eq_zero_of_res N n ξ _ ?_
    exact (lineH2Equiv N h3 i.rep n trivialCharacter hN).map_eq_zero_iff.mp h1
  refine fixedPointH2_eq_zero_of_orbit N h3 n ξ (lineFlagAt i.rep) (lineFlagAt h) γ hγ ?_ h2
  rw [hF, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

end Injective
end TernaryPeriodPolynomials.Argument.KDaggerComparison
