module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Plane.SumFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.EdgeToCusp

@[expose] public section


/-!
# From normal-form data to the canonical pairing of two mixed classes (planes)

Formalized by Claude Sonnet 5.5.

`planeSum_can`: `planeSum_final` for normal-form relative cocycles `z`, `z'` representing two mixed classes `x`, `y` of the plane group `gammaNPAt 6 h`; the result is `3 · r (facePairingCan (planeMixedEdgeAt x) (planeMixedEdgeAt y))`.
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD TernaryPeriodPolynomials.Argument.FlagH3
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open scoped Classical

/-- **The plane sum for normal-form representatives of two mixed classes**: `∑_c λ_{F_c}[Θ^P_c] = 3 r (can)`. -/
theorem planeSum_can (hN : 3 ≤ 6) (h : SL(3, ℤ))
    (W : Rep ℂ ↥(gammaNPAt 6 h)) [FiniteDimensional ℂ W] [Module ℚ W] [Module ℚ (dualRepG W)]
    (ρ' : Representation ℚ ↥(gammaNPAt 6 h) (dualRepG W)) (hρ' : ∀ g x, ρ' g x = (dualRepG W).ρ g x)
    (eQ : W →ₗ[ℚ] dualRepG W →ₗ[ℚ] ℚ) (r : ℂ →ₗ[ℚ] ℚ) (he : ∀ x y, eQ x y = r (Module.Dual.eval ℂ W x y))
    (x : planeMixedAt 6 h W) (y : planeMixedAt 6 h (dualRepG W))
    (z : relativeTwoCocycles (faceExt 6 h).inl W) (z' : relativeTwoCocycles (faceExt 6 h).inl (dualRepG W))
    (hzx : relativeTwoCocycleClass (faceExt 6 h).inl W z = ⟨x.1, res_radical_of_planeMixedAt x⟩)
    (hzy : relativeTwoCocycleClass (faceExt 6 h).inl (dualRepG W) z' = ⟨y.1, res_radical_of_planeMixedAt y⟩)
    (hU : ∀ a b : Gamma 6, z.val (faceSplitting 6 h a, faceSplitting 6 h b) = 0)
    (hmix : ∀ (r : RadicalLattice) (l : Gamma 6), z.val ((faceExt 6 h).inl r, faceSplitting 6 h l) = 0)
    (hmix' : ∀ (r : RadicalLattice) (l : Gamma 6), z'.val ((faceExt 6 h).inl r, faceSplitting 6 h l) = 0)
    (γ : ↥(gammaNPAt 6 h) → ↥(gammaNPAt 6 h) → ↥(gammaNPAt 6 h) → ℚ)
    (hγ : ∀ a b c : RadicalLattice, γ ((faceExt 6 h).inl a) ((faceExt 6 h).inl b) ((faceExt 6 h).inl c) = 0)
    (hd : dd3T γ = cup22 ρ' eQ (fun a b => z.val (a, b)) (fun a b => z'.val (a, b)))
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
        (planeMixedEdgeAt 6 h W x) (planeMixedEdgeAt 6 h (dualRepG W) y)) := by
  have e1 := planeEdge_class_eq 6 h x z hzx
  have e2 := planeEdge_class_eq 6 h y z' hzy
  have hC : groupCohomology.H1π _ (splitCocycleEdge (faceSplitting 6 h) W z) ∈
      cuspidalSubspace (Gamma 6) (splitRadicalH1Representation (faceSplitting 6 h) W) := by
    rw [← e1]; exact (planeMixedEdgeAt 6 h W x).2
  have hC' : groupCohomology.H1π _ (splitCocycleEdge (faceSplitting 6 h) (dualRepG W) z') ∈
      cuspidalSubspace (Gamma 6) (splitRadicalH1Representation (faceSplitting 6 h) (dualRepG W)) := by
    rw [← e2]; exact (planeMixedEdgeAt 6 h (dualRepG W) y).2
  obtain ⟨Φ, v, h0, hCΦ⟩ := exists_cusp_function hN _ (splitCocycleEdge (faceSplitting 6 h) W z) hC
  obtain ⟨Φ', v', -, hCΦ'⟩ := exists_cusp_function hN _ (splitCocycleEdge (faceSplitting 6 h) (dualRepG W) z') hC'
  have := planeSum_final hN h W ρ' hρ' eQ r he z z' hU hmix hmix' γ hγ hd hC hC' Φ Φ' v v' h0
    (fun g => hCΦ g) (fun g => hCΦ' g) w' hw' hΘ
  rw [this]
  have f1 : (⟨groupCohomology.H1π _ (splitCocycleEdge (faceSplitting 6 h) W z), hC⟩ :
      cuspidalSubspace (Gamma 6) (splitRadicalH1Representation (faceSplitting 6 h) W)) = planeMixedEdgeAt 6 h W x :=
    Subtype.ext e1.symm
  have f2 : (⟨groupCohomology.H1π _ (splitCocycleEdge (faceSplitting 6 h) (dualRepG W) z'), hC'⟩ :
      cuspidalSubspace (Gamma 6) (splitRadicalH1Representation (faceSplitting 6 h) (dualRepG W))) =
        planeMixedEdgeAt 6 h (dualRepG W) y := Subtype.ext e2.symm
  rw [f1, f2]

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
