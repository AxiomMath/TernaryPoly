module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.LineSumFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.EdgeToCusp

@[expose] public section


/-!
# From normal-form data to the canonical pairing of two mixed classes (lines)

Formalized by Claude Sonnet 5.5.

`lineSum_can`: `lineSum_final` for normal-form relative cocycles `z`, `z'` *representing* two mixed classes `x`, `y` of the line group `gammaNQAt 6 h`: the cuspidality of the edges and the cusp functions
`(Φ, v)`, `(Φ', v')` are supplied by `lineEdge_class_eq` and `exists_cusp_function`, and the result is `-3 · r (facePairingCan (mixedEdgeAt x) (mixedEdgeAt y))`.
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

/-- **The line sum for normal-form representatives of two mixed classes**: `∑_c λ_{F_c}[Θ_c] = -3 r (can)`. -/
theorem lineSum_can (hN : 3 ≤ 6) (h : SL(3, ℤ))
    (W : Rep ℂ ↥(gammaNQAt 6 h)) [FiniteDimensional ℂ W] [Module ℚ W] [Module ℚ (dualRepG W)]
    (ρ' : Representation ℚ ↥(gammaNQAt 6 h) (dualRepG W)) (hρ' : ∀ g x, ρ' g x = (dualRepG W).ρ g x)
    (eQ : W →ₗ[ℚ] dualRepG W →ₗ[ℚ] ℚ) (r : ℂ →ₗ[ℚ] ℚ) (he : ∀ x y, eQ x y = r (Module.Dual.eval ℂ W x y))
    (x : lineMixedAt 6 h W) (y : lineMixedAt 6 h (dualRepG W))
    (z : relativeTwoCocycles (lineFaceExt 6 h).inl W) (z' : relativeTwoCocycles (lineFaceExt 6 h).inl (dualRepG W))
    (hzx : relativeTwoCocycleClass (lineFaceExt 6 h).inl W z = ⟨x.1, res_radical_of_lineMixedAt x⟩)
    (hzy : relativeTwoCocycleClass (lineFaceExt 6 h).inl (dualRepG W) z' = ⟨y.1, res_radical_of_lineMixedAt y⟩)
    (hU : ∀ a b : Gamma 6, z.val (lineFaceSplitting 6 h a, lineFaceSplitting 6 h b) = 0)
    (hmix : ∀ (r : RadicalLattice) (l : Gamma 6), z.val ((lineFaceExt 6 h).inl r, lineFaceSplitting 6 h l) = 0)
    (hmix' : ∀ (r : RadicalLattice) (l : Gamma 6), z'.val ((lineFaceExt 6 h).inl r, lineFaceSplitting 6 h l) = 0)
    (γ : ↥(gammaNQAt 6 h) → ↥(gammaNQAt 6 h) → ↥(gammaNQAt 6 h) → ℚ)
    (hγ : ∀ a b c : RadicalLattice, γ ((lineFaceExt 6 h).inl a) ((lineFaceExt 6 h).inl b) ((lineFaceExt 6 h).inl c) = 0)
    (hd : dd3T γ = cup22 ρ' eQ (fun a b => z.val (a, b)) (fun a b => z'.val (a, b)))
    (wB : ∀ c : ↥(cuspReps hN).R, ↥(MulAction.stabilizer Γ6 (flagAt h (cuspPrim (c : RationalLine2)))) → W)
    (hwB : ∀ (c : ↥(cuspReps hN).R) b₁ b₂, W.ρ (flagIota h (cuspPrim (c : RationalLine2)) b₁) (wB c b₂) - wB c (b₁ * b₂) + wB c b₁ =
      z.val (flagIota h (cuspPrim (c : RationalLine2)) b₁, flagIota h (cuspPrim (c : RationalLine2)) b₂))
    (hΘ : ∀ c : ↥(cuspReps hN).R, dThree ((flagLift h (cuspPrim (c : RationalLine2))
      ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2))) (sigma_fix (c : RationalLine2))).flagTheta ρ' eQ (wB c)
      (fun a b => z'.val (a, b)) γ) = 0) :
    ∑ c : ↥(cuspReps hN).R, flagLam (flagAt h (cuspPrim (c : RationalLine2)))
        (clsRes (MulAction.stabilizer Γ6 (flagAt h (cuspPrim (c : RationalLine2)))) _ (hΘ c)) =
      -3 * r (facePairingCan hN (lineFaceSplitting 6 h) (lineFaceRadicalInput_det 6 h) W
        (mixedEdgeAt 6 h W x) (mixedEdgeAt 6 h (dualRepG W) y)) := by
  have e1 := lineEdge_class_eq 6 h x z hzx
  have e2 := lineEdge_class_eq 6 h y z' hzy
  have hC : groupCohomology.H1π _ (splitCocycleEdge (lineFaceSplitting 6 h) W z) ∈
      cuspidalSubspace (Gamma 6) (splitRadicalH1Representation (lineFaceSplitting 6 h) W) := by
    rw [← e1]; exact (mixedEdgeAt 6 h W x).2
  have hC' : groupCohomology.H1π _ (splitCocycleEdge (lineFaceSplitting 6 h) (dualRepG W) z') ∈
      cuspidalSubspace (Gamma 6) (splitRadicalH1Representation (lineFaceSplitting 6 h) (dualRepG W)) := by
    rw [← e2]; exact (mixedEdgeAt 6 h (dualRepG W) y).2
  obtain ⟨Φ, v, h0, hCΦ⟩ := exists_cusp_function hN _ (splitCocycleEdge (lineFaceSplitting 6 h) W z) hC
  obtain ⟨Φ', v', -, hCΦ'⟩ := exists_cusp_function hN _ (splitCocycleEdge (lineFaceSplitting 6 h) (dualRepG W) z') hC'
  have := lineSum_final hN h W ρ' hρ' eQ r he z z' hU hmix hmix' γ hγ hd hC hC' Φ Φ' v v' h0
    (fun g => hCΦ g) (fun g => hCΦ' g) wB hwB hΘ
  rw [this]
  have f1 : (⟨groupCohomology.H1π _ (splitCocycleEdge (lineFaceSplitting 6 h) W z), hC⟩ :
      cuspidalSubspace (Gamma 6) (splitRadicalH1Representation (lineFaceSplitting 6 h) W)) = mixedEdgeAt 6 h W x :=
    Subtype.ext e1.symm
  have f2 : (⟨groupCohomology.H1π _ (splitCocycleEdge (lineFaceSplitting 6 h) (dualRepG W) z'), hC'⟩ :
      cuspidalSubspace (Gamma 6) (splitRadicalH1Representation (lineFaceSplitting 6 h) (dualRepG W))) =
        mixedEdgeAt 6 h (dualRepG W) y := Subtype.ext e2.symm
  rw [f1, f2]

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
