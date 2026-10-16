module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CuspTotal
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.LineTerm
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Lift
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.LocalCusp
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.TwoCusps

@[expose] public section


/-!
# The line sum: `∑_c λ_{F_c}[Θ_c] = -3 · r (facePairingCan)`

Formalized by Claude Sonnet 5.5.

`lineSum_final`: the flag terms `flagLam_term` summed over the cusp representatives, together with the global term `cusp_total` and the cusp formula `edge_pairing_cusp_sum`.
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

/-- **The line sum.**  Summing the flag terms over the cusp representatives gives `-3 · r (facePairingCan)`: `∑_c λ_{F_c}[Θ_c] = -6 ∑_c (r e(X_c, C'σ_c) - μ σ_c) = -3 r (can)`. -/
theorem lineSum_final (hN : 3 ≤ 6) (h : SL(3, ℤ))
    (W : Rep ℂ ↥(gammaNQAt 6 h)) [FiniteDimensional ℂ W] [Module ℚ W] [Module ℚ (dualRepG W)]
    (ρ' : Representation ℚ ↥(gammaNQAt 6 h) (dualRepG W)) (hρ' : ∀ g x, ρ' g x = (dualRepG W).ρ g x)
    (eQ : W →ₗ[ℚ] dualRepG W →ₗ[ℚ] ℚ) (r : ℂ →ₗ[ℚ] ℚ) (he : ∀ x y, eQ x y = r (Module.Dual.eval ℂ W x y))
    (z : relativeTwoCocycles (lineFaceExt 6 h).inl W) (z' : relativeTwoCocycles (lineFaceExt 6 h).inl (dualRepG W))
    (hU : ∀ a b : Gamma 6, z.val (lineFaceSplitting 6 h a, lineFaceSplitting 6 h b) = 0)
    (hmix : ∀ (r : RadicalLattice) (l : Gamma 6), z.val ((lineFaceExt 6 h).inl r, lineFaceSplitting 6 h l) = 0)
    (hmix' : ∀ (r : RadicalLattice) (l : Gamma 6), z'.val ((lineFaceExt 6 h).inl r, lineFaceSplitting 6 h l) = 0)
    (γ : ↥(gammaNQAt 6 h) → ↥(gammaNQAt 6 h) → ↥(gammaNQAt 6 h) → ℚ)
    (hγ : ∀ a b c : RadicalLattice, γ ((lineFaceExt 6 h).inl a) ((lineFaceExt 6 h).inl b) ((lineFaceExt 6 h).inl c) = 0)
    (hd : dd3T γ = cup22 ρ' eQ (fun a b => z.val (a, b)) (fun a b => z'.val (a, b)))
    (hC : groupCohomology.H1π _ (splitCocycleEdge (lineFaceSplitting 6 h) W z) ∈
      cuspidalSubspace (Gamma 6) (splitRadicalH1Representation (lineFaceSplitting 6 h) W))
    (hC' : groupCohomology.H1π _ (splitCocycleEdge (lineFaceSplitting 6 h) (dualRepG W) z') ∈
      cuspidalSubspace (Gamma 6) (splitRadicalH1Representation (lineFaceSplitting 6 h) (dualRepG W)))
    (Φ : Tw (transRep hN (splitRadicalH1Representation (lineFaceSplitting 6 h) W)).ρ)
    (Φ' : Tw (transRep hN (splitRadicalH1Representation (lineFaceSplitting 6 h) (dualRepG W))).ρ)
    (v : splitRadicalH1Representation (lineFaceSplitting 6 h) W)
    (v' : splitRadicalH1Representation (lineFaceSplitting 6 h) (dualRepG W))
    (h0 : Φ.1 cusp1 = 0)
    (hCΦ : ∀ g : Gamma 6, (splitCocycleEdge (lineFaceSplitting 6 h) W z).1 g =
      fTw (transRep hN (splitRadicalH1Representation (lineFaceSplitting 6 h) W)) Φ.1 (gammaEquiv hN g) +
        (v - (splitRadicalH1Representation (lineFaceSplitting 6 h) W).ρ g v))
    (hCΦ' : ∀ g : Gamma 6, (splitCocycleEdge (lineFaceSplitting 6 h) (dualRepG W) z').1 g =
      fTw (transRep hN (splitRadicalH1Representation (lineFaceSplitting 6 h) (dualRepG W))) Φ'.1 (gammaEquiv hN g) +
        (v' - (splitRadicalH1Representation (lineFaceSplitting 6 h) (dualRepG W)).ρ g v'))
    (wB : ∀ c : ↥(cuspReps hN).R, ↥(MulAction.stabilizer Γ6 (flagAt h (cuspPrim (c : RationalLine2)))) → W)
    (hwB : ∀ (c : ↥(cuspReps hN).R) b₁ b₂, W.ρ (flagIota h (cuspPrim (c : RationalLine2)) b₁) (wB c b₂) - wB c (b₁ * b₂) + wB c b₁ =
      z.val (flagIota h (cuspPrim (c : RationalLine2)) b₁, flagIota h (cuspPrim (c : RationalLine2)) b₂))
    (hΘ : ∀ c : ↥(cuspReps hN).R, dThree ((flagLift h (cuspPrim (c : RationalLine2))
      ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2))) (sigma_fix (c : RationalLine2))).flagTheta ρ' eQ (wB c)
      (fun a b => z'.val (a, b)) γ) = 0) :
    ∑ c : ↥(cuspReps hN).R, flagLam (flagAt h (cuspPrim (c : RationalLine2)))
        (clsRes (MulAction.stabilizer Γ6 (flagAt h (cuspPrim (c : RationalLine2)))) _ (hΘ c)) =
      -3 * r (facePairingCan hN (lineFaceSplitting 6 h) (lineFaceRadicalInput_det 6 h) W
        ⟨groupCohomology.H1π _ (splitCocycleEdge (lineFaceSplitting 6 h) W z), hC⟩
        ⟨groupCohomology.H1π _ (splitCocycleEdge (lineFaceSplitting 6 h) (dualRepG W) z'), hC'⟩) := by
  have hterm : ∀ c : ↥(cuspReps hN).R, flagLam (flagAt h (cuspPrim (c : RationalLine2)))
        (clsRes (MulAction.stabilizer Γ6 (flagAt h (cuspPrim (c : RationalLine2)))) _ (hΘ c)) =
      -6 * (r ((leviCoupling hN (lineFaceSplitting 6 h) (lineFaceRadicalInput_det 6 h) W).e (Φ.1 c + v)
          ((splitCocycleEdge (lineFaceSplitting 6 h) (dualRepG W) z').1 ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2))))) -
        (pmE (lineFaceSplitting 6 h)).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2)
          ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2)))) := fun c => by
    refine flagLam_term hN h (cuspPrim (c : RationalLine2)) _ (sigma_fix (c : RationalLine2))
      (gammaEquiv_symm_cuspSigma (c : RationalLine2)) (c : RationalLine2) (by rw [MulEquiv.apply_symm_apply]) ?_ W ρ' hρ'
      eQ r he z z' hmix hmix' γ hγ (wB c) (hwB c) (hΘ c) Φ v hCΦ Φ' v' hCΦ'
    obtain ⟨φ, hφ, h1⟩ := exists_hom_ne_zero hN c
    refine ⟨fun x => φ (gammaEquiv hN x), fun a b => by simp only [map_mul]; exact hφ _ _, ?_⟩
    show φ (gammaEquiv hN ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2)))) ≠ 0
    rw [MulEquiv.apply_symm_apply, h1]; exact one_ne_zero
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.mul_sum]
  have htot := cusp_total hN (lineFaceSplitting 6 h) (lineFaceRadicalInput_det 6 h) W ρ' hρ' eQ r he z z' hU hmix hmix' γ hγ hd
    hC hC' Φ Φ' v v' h0 hCΦ hCΦ'
  rw [Finset.sum_coe_sort (cuspReps hN).R (fun c => r ((leviCoupling hN (lineFaceSplitting 6 h) (lineFaceRadicalInput_det 6 h) W).e (Φ.1 c + v)
          ((splitCocycleEdge (lineFaceSplitting 6 h) (dualRepG W) z').1 ((gammaEquiv hN).symm (cuspSigma c)))) -
        (pmE (lineFaceSplitting 6 h)).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) ((gammaEquiv hN).symm (cuspSigma c)))]
  rw [htot]
  ring

end Sum

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
