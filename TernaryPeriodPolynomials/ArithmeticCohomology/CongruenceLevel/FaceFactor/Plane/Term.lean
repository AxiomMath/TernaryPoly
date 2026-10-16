module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Plane.Eval
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.ExtendWGen
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CuspTotal

@[expose] public section


/-!
# The flag term of a cusp, planes: `λ_{F_c}[Θ^P_c] = 6 (r e(X_c, C'σ_c) - μ σ_c)`

Formalized by Claude Sonnet 5.5.

`planeLam_term`: for the plane flag `pflag h w` the flag cocycle `Θ^P = cup21 z (-w') + γ` (`w'` a primitive of the normal-form `z'` on the flag group, `γ` a primitive of `z ∪ z'`) has
`λ[Θ^P] = -6 ⟨Θ^P, Sh₁σ⟩ = 6 (r e_C(Φ c + v, C'σ_c) - μ σ_c)`: `planeLam_eq_slant`, `chainEval_nuSh_planeTheta`, `mu_cup21_alt` and `local_cusp_plane`.  This is the line term with the opposite sign.
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD TernaryPeriodPolynomials.Argument.FlagH3
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open scoped Classical

section Term

/-- **The plane flag term at a cusp.** -/
theorem planeLam_term (hN : 3 ≤ 6) (h : SL(3, ℤ)) (w : Prim2) (σ : Gamma 6) (hσ : σ.1 = posPar w.1)
    (c : RationalLine2) (hσc : gammaEquiv hN σ = cuspSigma c)
    (hψσ : ∃ ψ : Gamma 6 → ℚ, (∀ a b, ψ (a * b) = ψ a + ψ b) ∧ ψ σ ≠ 0)
    (W : Rep ℂ ↥(gammaNPAt 6 h)) [FiniteDimensional ℂ W] [Module ℚ W] [Module ℚ (dualRepG W)]
    (ρ' : Representation ℚ ↥(gammaNPAt 6 h) (dualRepG W)) (hρ' : ∀ g x, ρ' g x = (dualRepG W).ρ g x)
    (eQ : W →ₗ[ℚ] dualRepG W →ₗ[ℚ] ℚ) (r : ℂ →ₗ[ℚ] ℚ) (he : ∀ x y, eQ x y = r (Module.Dual.eval ℂ W x y))
    (z : relativeTwoCocycles (faceExt 6 h).inl W) (z' : relativeTwoCocycles (faceExt 6 h).inl (dualRepG W))
    (hmix : ∀ (r : RadicalLattice) (l : Gamma 6), z.val ((faceExt 6 h).inl r, faceSplitting 6 h l) = 0)
    (hmix' : ∀ (r : RadicalLattice) (l : Gamma 6), z'.val ((faceExt 6 h).inl r, faceSplitting 6 h l) = 0)
    (γ : ↥(gammaNPAt 6 h) → ↥(gammaNPAt 6 h) → ↥(gammaNPAt 6 h) → ℚ)
    (hγ : ∀ a b c : RadicalLattice, γ ((faceExt 6 h).inl a) ((faceExt 6 h).inl b) ((faceExt 6 h).inl c) = 0)
    (w' : ↥(MulAction.stabilizer Γ6 (pflag h w)) → dualRepG W)
    (hw' : ∀ b₁ b₂, (dualRepG W).ρ ((planeLift h w σ hσ).ι b₁) (w' b₂) - w' (b₁ * b₂) + w' b₁ =
      z'.val ((planeLift h w σ hσ).ι b₁, (planeLift h w σ hσ).ι b₂))
    (hΘ : dThree ((planeLift h w σ hσ).planeFlagTheta ρ' eQ (fun a b => z.val (a, b)) w' γ) = 0)
    (Φ : Tw (transRep hN (splitRadicalH1Representation (faceSplitting 6 h) W)).ρ)
    (v : splitRadicalH1Representation (faceSplitting 6 h) W)
    (hCΦ : ∀ g : Gamma 6, (splitCocycleEdge (faceSplitting 6 h) W z).1 g =
      fTw (transRep hN (splitRadicalH1Representation (faceSplitting 6 h) W)) Φ.1 (gammaEquiv hN g) +
        (v - (splitRadicalH1Representation (faceSplitting 6 h) W).ρ g v)) :
    flagLam (pflag h w) (clsRes (MulAction.stabilizer Γ6 (pflag h w)) _ hΘ) =
      6 * (r ((leviCoupling hN (faceSplitting 6 h) (planeFaceRadicalInput_det 6 h) W).e (Φ.1 c + v)
          ((splitCocycleEdge (faceSplitting 6 h) (dualRepG W) z').1 σ)) -
        (pmE (faceSplitting 6 h)).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) σ) := by
  have hdet := planeFaceRadicalInput_det 6 h
  have hl := relativeTwoCocycle_radical_left (faceSplitting 6 h) W z hmix
  have hz0 : ∀ (a : Additive RadicalLattice) (g : ↥(gammaNPAt 6 h)),
      (fun a b => z.val (a, b)) ((pmE (faceSplitting 6 h)).nl a) g = 0 := fun a g => by
    show z.val ((pmE (faceSplitting 6 h)).nl a, g) = 0
    rw [pm_nl]; exact hl _ _
  have hGe1 : (pmE (faceSplitting 6 h)).Ge1 γ := fun a b c => by
    rw [pm_nl, pm_nl, pm_nl]; exact hγ _ _ _
  have hz := fun a b c => (planeLift h w σ hσ).planeFlagTheta_nl ρ' eQ (fun a b => z.val (a, b)) w' γ hz0 hGe1 a b c
  rw [planeLam_eq_slant h w σ hσ hdet hψσ _ hΘ hz,
    (planeLift h w σ hσ).chainEval_nuSh_planeTheta ρ' eQ (fun a b => z.val (a, b)) w' γ]
  have hR1 := (planeLift h w σ hσ).extendG_hR1 (faceSplitting 6 h) (dualRepG W) z' w' hw'
  have hR2 := (planeLift h w σ hσ).extendG_hR2 (faceSplitting 6 h) (dualRepG W) z' w' hw' hmix'
  have hR3 := (planeLift h w σ hσ).extendG_hR3 (faceSplitting 6 h) (dualRepG W) z' w' hw'
  have hloc := local_cusp_plane (faceSplitting 6 h) W hN hdet z z' hmix' σ ((planeLift h w σ hσ).extendG (faceSplitting 6 h) (dualRepG W) w')
    hR1 hR2 hR3 Φ v hCΦ c hσc
  have hmu := mu_cup21_alt (faceSplitting 6 h) ρ' hρ' eQ (Module.Dual.eval ℂ W) r he z hmix
    (flagRadCocycle (dualRepG W) ((planeLift h w σ hσ).extendG (faceSplitting 6 h) (dualRepG W) w') hR1)
    ((planeLift h w σ hσ).extendG (faceSplitting 6 h) (dualRepG W) w') (fun u => rfl) σ
  have hext : (fun g => w' (Function.invFun (planeLift h w σ hσ).ι g)) =
      (planeLift h w σ hσ).extendG (faceSplitting 6 h) (dualRepG W) w' := rfl
  rw [hext, hmu, hloc]
  ring

end Term

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
