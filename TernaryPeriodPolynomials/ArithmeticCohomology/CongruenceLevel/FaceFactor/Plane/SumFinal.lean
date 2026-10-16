module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Plane.Term
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.TwoCusps

@[expose] public section


/-!
# The plane sum: `∑_c λ_{F_c}[Θ^P_c] = 3 · r (facePairingCan)`

Formalized by Claude Sonnet 5.5.

`planeSum_final`: the plane flag terms `planeLam_term` summed over the cusp representatives with the global term `cusp_total`: `κ_P = 3 = -κ_L`.
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

section Sum

/-- **The plane sum.**  `∑_c λ_{F_c}[Θ^P_c] = 6 ∑_c (r e(X_c, C'σ_c) - μ σ_c) = 3 r (can)`. -/
theorem planeSum_final (hN : 3 ≤ 6) (h : SL(3, ℤ))
    (W : Rep ℂ ↥(gammaNPAt 6 h)) [FiniteDimensional ℂ W] [Module ℚ W] [Module ℚ (dualRepG W)]
    (ρ' : Representation ℚ ↥(gammaNPAt 6 h) (dualRepG W)) (hρ' : ∀ g x, ρ' g x = (dualRepG W).ρ g x)
    (eQ : W →ₗ[ℚ] dualRepG W →ₗ[ℚ] ℚ) (r : ℂ →ₗ[ℚ] ℚ) (he : ∀ x y, eQ x y = r (Module.Dual.eval ℂ W x y))
    (z : relativeTwoCocycles (faceExt 6 h).inl W) (z' : relativeTwoCocycles (faceExt 6 h).inl (dualRepG W))
    (hU : ∀ a b : Gamma 6, z.val (faceSplitting 6 h a, faceSplitting 6 h b) = 0)
    (hmix : ∀ (r : RadicalLattice) (l : Gamma 6), z.val ((faceExt 6 h).inl r, faceSplitting 6 h l) = 0)
    (hmix' : ∀ (r : RadicalLattice) (l : Gamma 6), z'.val ((faceExt 6 h).inl r, faceSplitting 6 h l) = 0)
    (γ : ↥(gammaNPAt 6 h) → ↥(gammaNPAt 6 h) → ↥(gammaNPAt 6 h) → ℚ)
    (hγ : ∀ a b c : RadicalLattice, γ ((faceExt 6 h).inl a) ((faceExt 6 h).inl b) ((faceExt 6 h).inl c) = 0)
    (hd : dd3T γ = cup22 ρ' eQ (fun a b => z.val (a, b)) (fun a b => z'.val (a, b)))
    (hC : groupCohomology.H1π _ (splitCocycleEdge (faceSplitting 6 h) W z) ∈
      cuspidalSubspace (Gamma 6) (splitRadicalH1Representation (faceSplitting 6 h) W))
    (hC' : groupCohomology.H1π _ (splitCocycleEdge (faceSplitting 6 h) (dualRepG W) z') ∈
      cuspidalSubspace (Gamma 6) (splitRadicalH1Representation (faceSplitting 6 h) (dualRepG W)))
    (Φ : Tw (transRep hN (splitRadicalH1Representation (faceSplitting 6 h) W)).ρ)
    (Φ' : Tw (transRep hN (splitRadicalH1Representation (faceSplitting 6 h) (dualRepG W))).ρ)
    (v : splitRadicalH1Representation (faceSplitting 6 h) W)
    (v' : splitRadicalH1Representation (faceSplitting 6 h) (dualRepG W))
    (h0 : Φ.1 cusp1 = 0)
    (hCΦ : ∀ g : Gamma 6, (splitCocycleEdge (faceSplitting 6 h) W z).1 g =
      fTw (transRep hN (splitRadicalH1Representation (faceSplitting 6 h) W)) Φ.1 (gammaEquiv hN g) +
        (v - (splitRadicalH1Representation (faceSplitting 6 h) W).ρ g v))
    (hCΦ' : ∀ g : Gamma 6, (splitCocycleEdge (faceSplitting 6 h) (dualRepG W) z').1 g =
      fTw (transRep hN (splitRadicalH1Representation (faceSplitting 6 h) (dualRepG W))) Φ'.1 (gammaEquiv hN g) +
        (v' - (splitRadicalH1Representation (faceSplitting 6 h) (dualRepG W)).ρ g v'))
    (w' : ∀ c : ↥(cuspReps hN).R, ↥(MulAction.stabilizer Γ6 (pflag h (wOf (c : RationalLine2)))) → dualRepG W)
    (hw' : ∀ (c : ↥(cuspReps hN).R) b₁ b₂, (dualRepG W).ρ
      ((planeLift h (wOf (c : RationalLine2)) ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2))) (sigmaCusp_val hN c)).ι b₁)
        (w' c b₂) - w' c (b₁ * b₂) + w' c b₁ =
      z'.val ((planeLift h (wOf (c : RationalLine2)) ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2))) (sigmaCusp_val hN c)).ι b₁,
        (planeLift h (wOf (c : RationalLine2)) ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2))) (sigmaCusp_val hN c)).ι b₂))
    (hΘ : ∀ c : ↥(cuspReps hN).R, dThree ((planeLift h (wOf (c : RationalLine2)) ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2)))
      (sigmaCusp_val hN c)).planeFlagTheta ρ' eQ (fun a b => z.val (a, b)) (w' c) γ) = 0) :
    ∑ c : ↥(cuspReps hN).R, flagLam (pflag h (wOf (c : RationalLine2)))
        (clsRes (MulAction.stabilizer Γ6 (pflag h (wOf (c : RationalLine2)))) _ (hΘ c)) =
      3 * r (facePairingCan hN (faceSplitting 6 h) (planeFaceRadicalInput_det 6 h) W
        ⟨groupCohomology.H1π _ (splitCocycleEdge (faceSplitting 6 h) W z), hC⟩
        ⟨groupCohomology.H1π _ (splitCocycleEdge (faceSplitting 6 h) (dualRepG W) z'), hC'⟩) := by
  have hterm : ∀ c : ↥(cuspReps hN).R, flagLam (pflag h (wOf (c : RationalLine2)))
        (clsRes (MulAction.stabilizer Γ6 (pflag h (wOf (c : RationalLine2)))) _ (hΘ c)) =
      6 * (r ((leviCoupling hN (faceSplitting 6 h) (planeFaceRadicalInput_det 6 h) W).e (Φ.1 c + v)
          ((splitCocycleEdge (faceSplitting 6 h) (dualRepG W) z').1 ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2))))) -
        (pmE (faceSplitting 6 h)).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2)
          ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2)))) := fun c => by
    refine planeLam_term hN h (wOf (c : RationalLine2)) _ (sigmaCusp_val hN c) (c : RationalLine2)
      (by rw [MulEquiv.apply_symm_apply]) ?_ W ρ' hρ' eQ r he z z' hmix hmix' γ hγ (w' c) (hw' c) (hΘ c) Φ v hCΦ
    obtain ⟨φ, hφ, h1⟩ := exists_hom_ne_zero hN c
    refine ⟨fun x => φ (gammaEquiv hN x), fun a b => by simp only [map_mul]; exact hφ _ _, ?_⟩
    show φ (gammaEquiv hN ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2)))) ≠ 0
    rw [MulEquiv.apply_symm_apply, h1]; exact one_ne_zero
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.mul_sum]
  have htot := cusp_total hN (faceSplitting 6 h) (planeFaceRadicalInput_det 6 h) W ρ' hρ' eQ r he z z' hU hmix hmix' γ hγ hd
    hC hC' Φ Φ' v v' h0 hCΦ hCΦ'
  rw [Finset.sum_coe_sort (cuspReps hN).R (fun c => r ((leviCoupling hN (faceSplitting 6 h) (planeFaceRadicalInput_det 6 h) W).e (Φ.1 c + v)
          ((splitCocycleEdge (faceSplitting 6 h) (dualRepG W) z').1 ((gammaEquiv hN).symm (cuspSigma c)))) -
        (pmE (faceSplitting 6 h)).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) ((gammaEquiv hN).symm (cuspSigma c)))]
  rw [htot]
  ring

end Sum

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
