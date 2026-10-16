module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.SeedPassageCochain

@[expose] public section


/-!
# CMP-8 (3a, 3b): the bad-face coordinate of the entry section in terms of the seed classes of `g5_levelOne_cusp`

`phiPlaneAt_bad_face`: for the entry datum (`M`, Eichler input `I`, spherical datum `S` with the same weight and vector) and a face `h` whose plane is bad,
the coordinate `phiPlaneAt h` of the class of `badPlaneWeight · cOmega` is `K_h` times the `(conjP, faceMor)`-transport of
`[seed H_h] + ε_* [seed H'_h]`, `H_h = F(1 · b_F(g_h))`, `H'_h = F(J · b_F(g_h))`, `g_h = faceArg h`, `K_h = (-1)^n (n+1)/2 · c_F(g_h)`.
This is `phiPlaneAt_weighted_eq` (the cochain identity) composed with the `g5_levelOne_cusp`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.FormSeedBridge TernaryPeriodPolynomials.Argument.FormSeriesModel
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section
namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

theorem faceArg_eq (h : SL(3, ℤ)) :
    faceArg h = rationalGroup (integralRational (Matrix.SpecialLinearGroup.toGL h)) := by
  have e : (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ = integralRational (Matrix.SpecialLinearGroup.toGL h) := by
    rw [map_inv, inv_inv]
    apply Units.ext
    ext i j
    simp [integralRational, Matrix.SpecialLinearGroup.mapGL, Matrix.GeneralLinearGroup.map_apply]
  unfold faceArg
  rw [e]

/-- **The bad-face coordinate of the entry section in terms of the seed classes** (`g5_levelOne_cusp` at the face `h`). -/
theorem phiPlaneAt_bad_face (M : CohomologicalCuspData n) (I : EichlerInput M.cusp n)
    (S : SphericalEntryData M.inducingData) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (hPP : IsSourceCocycle M.inducingData .plane (fun y g => badPlaneWeight g • cOmega n M.inducingData S.F y g))
    (h : SL(3, ℤ)) (hbad : ¬ GoodFlag .plane (planeFlagAt h)) :
    ∃ (Gm Gm' : ℕ → ℂ → ℂ) (s : SeedHyp N n (S.F (1 * bF (faceArg h))) Gm)
      (s' : SeedHyp N n (S.F (atInfinity UpperHalfPlane.J * bF (faceArg h))) Gm'),
      phiPlaneAt N h3 hN n h (SourceSpace.sourceClass M.inducingData .plane
        ⟨fun y g => badPlaneWeight g • cOmega n M.inducingData S.F y g, hPP⟩) =
      (((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * cF M.inducingData (faceArg h)) •
        (groupCohomology.map (conjP N h).toMonoidHom (faceMor N n h) 2).hom
          (complexifyG N n ((gammaNPlaneData N).seedClass (S.F (1 * bF (faceArg h))) n Gm s.hh s.hG s.hmod) +
            (groupCohomology.map (epsHom N) (epsRep N n) 2).hom
              (complexifyG N n ((gammaNPlaneData N).seedClass (S.F (atInfinity UpperHalfPlane.J * bF (faceArg h))) n Gm'
                s'.hh s'.hG s'.hmod))) := by
  have hF : S.F = cuspScalarWeightedRealization M.inducingData.cusp I.halfWeight I.vector := by
    rw [hw, hv]; rfl
  obtain ⟨Gm, Gm', s, s', hc1, hc2⟩ := g5_levelOne_cusp N n h3 M.inducingData I S.F hF h (faceArg h)
    (realGroup_faceArg h) (by rw [faceArg_eq]; exact bF_rational_integral _)
  refine ⟨Gm, Gm', s, s', ?_⟩
  rw [phiPlaneAt_weighted_eq N h3 hN n M S.F hPP h hbad _ _ hc1, hc2]
  rfl

end TernaryPeriodPolynomials.Argument.KDaggerComparison
