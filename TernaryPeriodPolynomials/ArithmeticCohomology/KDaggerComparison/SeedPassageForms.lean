module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.SeedPassageClasses
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.SeedPassageScalar

@[expose] public section


/-!
# CMP-8 (3a, 3b): the bad-face coordinate of the entry section is the pair of classical seed classes at the face

`levelN N f`: the restriction of a level-one cusp form to `Γ₂(N)`.  `phiPlaneAt_bad_face_forms`: for the entry datum, with `f0` the classical level-one form of the Eichler vector
and `f1` the same form of weight `n + 3`, the coordinate `phiPlaneAt h` of the bad-plane weighted plane integral cochain at a face `h` whose plane is bad is
`K_h • [seed of f] + K_h (-1)^{n+1} • [antiholomorphic seed of f*]` at the face `h`, `K_h = (-1)^n (n+1)/2 · c_F(g_h)` (the `faceSeedKerClass`, `faceSeedConjKerClass` of the restrictions
of `f1` and `fStar f1` to `Γ₂(N)`).  The ingredients: `phiPlaneAt_bad_face` (the cochain identity composed with the `g5_levelOne_cusp`), `scalarF_one_eq_form`, `scalarF_J_eq_form`
(the scalar functions are the classical form), `seedClass_congr`, the `eps_seedClass`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open UpperHalfPlane ModularForm

noncomputable section
namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

/-- **Restriction of a cusp form to a smaller group.** -/
def restrictCuspForm {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (hle : Γ' ≤ Γ) (f : CuspForm Γ k) : CuspForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := f.slash_action_eq' γ (hle hγ)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono hle)

theorem restrictCuspForm_apply {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (hle : Γ' ≤ Γ) (f : CuspForm Γ k) (τ : ℍ) :
    restrictCuspForm hle f τ = f τ := rfl

theorem leviGroup_le_lvl1 (N : ℕ) : leviGroup N ≤ Lvl1 := Subgroup.map_le_range _ _

/-- The level-`Γ₂(N)` cusp form of a level-one cusp form. -/
def levelN (N : ℕ) {k : ℤ} (f : CuspForm Lvl1 k) : CuspForm (leviGroup N) k := restrictCuspForm (leviGroup_le_lvl1 N) f

section Face

open TernaryPeriodPolynomials.Argument.FormSeedBridge TernaryPeriodPolynomials.Argument.FormClassK
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry TernaryPeriodPolynomials.SourceConstruction
  TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction TernaryPeriodPolynomials.SphericalDetection.Helpers
  TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

/-- **The bad-face coordinate of the entry section is `K_h` times the seed classes of the classical form `f` and of `f*` at the face** (`g5_levelOne_cusp`,
the scalar functions `F(1·b_F)`, `F(J·b_F)` identified with `f` by `scalarF_one_eq_form`, `scalarF_J_eq_form`, and `eps_seedClass`). -/
theorem phiPlaneAt_bad_face_forms (M : CohomologicalCuspData n) (I : EichlerInput M.cusp n)
    (S : SphericalEntryData M.inducingData) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (hPP : IsSourceCocycle M.inducingData .plane (fun y g => badPlaneWeight g • cOmega n M.inducingData S.F y g))
    (f0 : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑f0 : ℍ → ℂ) = cuspScalarWeightedLinear M.cusp I.halfWeight 1 I.vector)
    (f1 : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (hf1 : (f1 : ℍ → ℂ) = f0)
    (h : SL(3, ℤ)) (hbad : ¬ GoodFlag .plane (planeFlagAt h)) :
    phiPlaneAt N h3 hN n h (SourceSpace.sourceClass M.inducingData .plane
        ⟨fun y g => badPlaneWeight g • cOmega n M.inducingData S.F y g, hPP⟩) =
      (((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * cF M.inducingData (faceArg h)) •
          ((faceSeedKerClass N h n (levelN N f1)).1 : groupCohomology.H2 (faceRep N h n)) +
        ((((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * cF M.inducingData (faceArg h)) * ((-1 : ℂ) ^ (n + 1))) •
          ((faceSeedConjKerClass N h n (levelN N (fStar f1))).1 : groupCohomology.H2 (faceRep N h n)) := by
  obtain ⟨Gm, Gm', s, s', hmain⟩ := phiPlaneAt_bad_face N h3 hN n M I S hw hv hPP h hbad
  obtain ⟨B, hB⟩ : ∃ B : Matrix.GeneralLinearGroup (Fin 2) IntegralAdeles,
      bF (faceArg h) = atFinite (Matrix.GeneralLinearGroup.map integralEmbedding B) := by
    rw [faceArg_eq]; exact bF_rational_integral _
  have hF : S.F = cuspScalarWeightedRealization M.inducingData.cusp I.halfWeight I.vector := by
    rw [hw, hv]; rfl
  have hcH : ∀ (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (z : ℂ) (hz : 0 < z.im),
      cuspH (leviGroup N) n (levelN N f) z = f ⟨z, hz⟩ := fun f z hz => by
    change f (ofComplex z) = _
    rw [ofComplex_apply_of_im_pos hz]
  have e1 : (gammaNPlaneData N).seedClass (S.F (1 * bF (faceArg h))) n Gm s.hh s.hG s.hmod =
      cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := levelN N f1) :=
    seedClass_congr (gammaNPlaneData N) n _ (cuspH (leviGroup N) n (levelN N f1)) Gm _ s.hh
      (cuspH_holo (leviGroup N) n (levelN N f1)) s.hG (momentPrim_hasDerivAt (leviGroup N) n (levelN N f1))
      s.hmod (cuspH_mod (gammaNPlaneData N) (gammaNPlaneData_lam_mem N))
      (fun z hz => by
        rw [hcH f1 z hz, hF, hB]
        exact (scalarF_one_eq_form I f0 hform B ⟨z, hz⟩).trans (congrFun hf1 ⟨z, hz⟩).symm)
  have e2 := eps_seedClass N n (S.F (atInfinity UpperHalfPlane.J * bF (faceArg h)))
    (cuspH (leviGroup N) n (levelN N (fStar f1))) Gm' _ s'.hh s'.hG s'.hmod
    (cuspH_holo (leviGroup N) n (levelN N (fStar f1))) (momentPrim_hasDerivAt (leviGroup N) n (levelN N (fStar f1)))
    (cuspH_mod (gammaNPlaneData N) (gammaNPlaneData_lam_mem N))
    (fun z hz => by
      have hz' : 0 < (-(starRingEnd ℂ z)).im := by simpa using hz
      have e3 := scalarF_J_eq_form I f0 hform B (ofComplex (-(starRingEnd ℂ z)))
      rw [ofComplex_apply_of_im_pos hz'] at e3
      rw [hcH (fStar f1) z hz, fStar_apply, hF, hB, ofComplex_apply_of_im_pos hz']
      refine congrArg (starRingEnd ℂ) ?_
      exact (congrFun hf1 ⟨-(starRingEnd ℂ z), hz'⟩).trans e3.symm)
  rw [hmain, e1, e2, map_add, map_smul, faceSeedKerClass_val, faceSeedConjKerClass_val, smul_add, smul_smul]
  rfl

end Face

end TernaryPeriodPolynomials.Argument.KDaggerComparison
