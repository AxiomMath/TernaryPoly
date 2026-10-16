module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.SeedPassageBase
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.OtherCusps
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.PerDatumMS
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.GoodWeights
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Bridge

@[expose] public section


/-!
# CMP-8 (3a, 3b): the Shapiro coordinate of the bad-plane weighted plane integral cochain at a bad face

`faceArg h`: the adelic argument `rationalGroup (mapGL ℚ h⁻¹)⁻¹` at which the evaluated cocycle is read at the flag `planeFlagAt h`
(`realGroup_faceArg`: its real component is `mapGL ℝ h`).  `phiPlaneAt_weighted`: at a bad face the coordinate of the class of
`badPlaneWeight · cOmega` is the class of the cocycle `(a, b) ↦ cOmega(1, a, ab)(faceArg h)`.  `phiPlaneAt_weighted_eq`: given the coefficient
identity of `FormSeedBridge.g5_levelOne_cusp` with a cocycle `C` and a scalar `K`, it is `K` times the class of the conjugate cocycle `cuspCocycle h C`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspOrbits

noncomputable section
namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

/-- The adelic argument of the face `planeFlagAt h`: `rationalGroup (mapGL ℚ h⁻¹)⁻¹`. -/
def faceArg (h : SL(3, ℤ)) : AdelicGL := rationalGroup (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹

theorem realGroup_faceArg (h : SL(3, ℤ)) : realGroup (faceArg h) = Matrix.SpecialLinearGroup.mapGL ℝ h := by
  have e : realGroup (rationalGroup (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)) =
      Matrix.SpecialLinearGroup.mapGL ℝ h⁻¹ := by
    apply Units.ext
    ext i j
    simp [realGroup_rational, Matrix.SpecialLinearGroup.mapGL]
  unfold faceArg
  rw [map_inv, map_inv, e, map_inv, inv_inv]

omit [NeZero N] in
/-- **The Shapiro coordinate of the bad-plane weighted plane integral cochain at a bad face.** -/
theorem phiPlaneAt_weighted (M : CohomologicalCuspData n) (F : BinaryAdelicGL → ℂ → ℂ)
    (hPP : IsSourceCocycle M.inducingData .plane (fun y g => badPlaneWeight g • cOmega n M.inducingData F y g))
    (h : SL(3, ℤ)) (hbad : ¬ GoodFlag .plane (planeFlagAt h)) :
    ∃ c : groupCohomology.cocycles₂ (faceRep N h n),
      (∀ a b : gammaNPAt N h, (c : gammaNPAt N h × gammaNPAt N h → HomogeneousPoly n) (a, b) =
        cOmega n M.inducingData F (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          (![1, Matrix.SpecialLinearGroup.mapGL ℚ a.1, Matrix.SpecialLinearGroup.mapGL ℚ (a.1 * b.1)] i))
          (faceArg h)) ∧
      phiPlaneAt N h3 hN n h (SourceSpace.sourceClass M.inducingData .plane
        ⟨fun y g => badPlaneWeight g • cOmega n M.inducingData F y g, hPP⟩) = groupCohomology.H2π (faceRep N h n) c := by
  obtain ⟨c, hc, hcl⟩ := phiPlaneAt_classOf N h3 hN n h
    (SourceSpace.evaluatedSource M.inducingData .plane ⟨fun y g => badPlaneWeight g • cOmega n M.inducingData F y g, hPP⟩)
  refine ⟨c, fun a b => ?_, hcl⟩
  rw [hc]
  have hq := SourceSpace.evaluatedSource_realizes M.inducingData .plane
    ⟨fun y g => badPlaneWeight g • cOmega n M.inducingData F y g, hPP⟩
    ![1, Matrix.SpecialLinearGroup.mapGL ℚ a.1, Matrix.SpecialLinearGroup.mapGL ℚ (a.1 * b.1)]
    (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)
  have hw : badPlaneWeight (faceArg h) = 1 := by
    have := badPlaneWeight_rational (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)
    unfold goodWeight at this
    have hb' : ¬ GoodFlag .plane (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) : Flags .plane) := hbad
    rw [ite_eq_right hb'] at this
    simpa [faceArg] using this
  refine hq.trans ?_
  change badPlaneWeight (faceArg h) • _ = _
  rw [hw, one_smul]
  rfl

open TernaryPeriodPolynomials.Argument.FormSeedBridge TernaryPeriodPolynomials.Argument.LevelTransfer TernaryPeriodPolynomials.Argument.FormSeriesModel TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3 in
omit [NeZero N] in
/-- **The Shapiro coordinate of the weighted plane cochain is `K` times the class of the conjugate cocycle** (given the coefficient
identity of `g5_levelOne_cusp`). -/
theorem phiPlaneAt_weighted_eq (M : CohomologicalCuspData n) (F : BinaryAdelicGL → ℂ → ℂ)
    (hPP : IsSourceCocycle M.inducingData .plane (fun y g => badPlaneWeight g • cOmega n M.inducingData F y g))
    (h : SL(3, ℤ)) (hbad : ¬ GoodFlag .plane (planeFlagAt h))
    (C : cocycles (realLevel (gammaNP N)) (GeneralEisenstein.realCoefficient n)) (K : ℂ)
    (hC : ∀ (y : Fin 3 → RealGL3) (κ : Fin 3 →₀ ℕ), cOmegaCoeff n M.inducingData F y (faceArg h) κ =
      K * ((GeneralEisenstein.realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ h)⁻¹
        (C.val.val (fun i => Matrix.SpecialLinearGroup.mapGL ℝ h * y i)) : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ).coeff κ) :
    phiPlaneAt N h3 hN n h (SourceSpace.sourceClass M.inducingData .plane
        ⟨fun y g => badPlaneWeight g • cOmega n M.inducingData F y g, hPP⟩) =
      K • (groupCohomology.map (realLevelHom (gammaNPAt N h)) (repMorAt n (gammaNPAt N h)) 2).hom
        (bridge (GeneralEisenstein.realCoefficient n) (realLevel (gammaNPAt N h))
          (Submodule.Quotient.mk (cuspCocycle N n h C))) := by
  obtain ⟨c, hc, hcl⟩ := phiPlaneAt_weighted N h3 hN n M F hPP h hbad
  rw [hcl, bridge_mk, groupCohomology.H2π_comp_map_apply, ← map_smul]
  congr 1
  apply Subtype.ext
  funext ab
  obtain ⟨a, b⟩ := ab
  refine (hc a b).trans ?_
  change _ = K • (bridgeCocycle (GeneralEisenstein.realCoefficient n) (realLevel (gammaNPAt N h))
      (cuspCocycle N n h C) : _ × _ → HomogeneousPoly n) (realLevelHom _ a, realLevelHom _ b)
  rw [bridgeCocycle_apply, cuspCocycle_apply]
  have hm : ∀ p : SL(3, ℤ), Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ p) =
      Matrix.SpecialLinearGroup.mapGL ℝ p := fun p => by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply, Matrix.SpecialLinearGroup.mapGL]
  have hy : (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (![1, Matrix.SpecialLinearGroup.mapGL ℚ a.1, Matrix.SpecialLinearGroup.mapGL ℚ (a.1 * b.1)] i)) =
      ![1, ((realLevelHom (gammaNPAt N h) a : realLevel (gammaNPAt N h)) : RealGL3),
        ((realLevelHom (gammaNPAt N h) a * realLevelHom (gammaNPAt N h) b : realLevel (gammaNPAt N h)) : RealGL3)] := by
    funext i
    fin_cases i
    · simp
    · exact hm a.1
    · change _ = Matrix.SpecialLinearGroup.mapGL ℝ a.1 * Matrix.SpecialLinearGroup.mapGL ℝ b.1
      rw [← map_mul]
      exact hm (a.1 * b.1)
  rw [hy]
  apply Subtype.ext
  apply MvPolynomial.ext
  intro κ
  change ((ofCoeffs n _ : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ).coeff κ = _
  rw [coeff_ofCoeffs]
  rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  split_ifs with hd
  · exact hC _ κ
  · have hhom := (MvPolynomial.mem_homogeneousSubmodule n _).mp
      ((GeneralEisenstein.realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ h)⁻¹
        (C.val.val (fun i => Matrix.SpecialLinearGroup.mapGL ℝ h *
          ![1, ((realLevelHom (gammaNPAt N h) a : realLevel (gammaNPAt N h)) : RealGL3),
            ((realLevelHom (gammaNPAt N h) a * realLevelHom (gammaNPAt N h) b : realLevel (gammaNPAt N h)) : RealGL3)] i))).2)
    rw [hhom.coeff_eq_zero (by simpa using hd), mul_zero]

end TernaryPeriodPolynomials.Argument.KDaggerComparison
