module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineEdgeParabolic
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.PsiLReconciliation
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentGoodLine

@[expose] public section


/-!
# `bridgeX` is parabolic for an `InnerBoundary` line class, Hecke-free (M4, good line, step 2)

`ParabolicDualityIdentGoodLine.bridgeX_mem_parabolicCocycles` makes `bridgeX` a parabolic cocycle
via `LocalUniqueness.phiL` and a Hecke pair character `c` with a spectral-gap bound at `T₂`
(`phiL_mem_parabolicH1`). This file gives a Hecke-free alternative when the underlying class comes
from an `InnerBoundary` witness.

`phiL` is *defined* as `edgeK ∘ₗ (psiL n).restrict _` (`LocalUniqueness.lean`), so
`ParabolicDualityIdentGoodLine.projectH1_bridgeX_eq_neg_edgeK` already identifies `[bridgeX]` as
minus the `edgeK`-image of `classOf Λ₁ (ρn n) (cocycleAtGoodLine n trivialCharacter z)` with *no*
Hecke/`c` dependence at all. Via `classOf_cocycleAtGoodLine` and `PsiLReconciliation.psiL_cuspRes_eq`
this class is *literally* `fixedPointH2 rationalLevel (ρn n) (mk rationalGoodLine) coordinate` —
exactly the term `GoodLineEdgeParabolic.goodLine_edge_parabolic_of_innerBoundary` (M1a) already shows
is parabolic. Composing the two gives `bridgeX`'s parabolicity directly, bypassing `phiL`/`ML n`/the
Hecke eigenvalue bound entirely.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GoodBuildingPaths.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.LineCoordinates
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Spectral.GoodLineLocalOp
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (lineCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant (bridgeX phiTwist_trivial)

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M4, good line, step 2 (value form).** The Hochschild–Serre edge image of `bridgeX` for an
`InnerBoundary` line class is *literally* minus the `edgeK`-edge of the `InnerBoundary` witness —
no Hecke-eigenvalue hypothesis, and no mere membership: the exact value transports. This is the
sharp form needed to compute `parabolicPairing` against `[bridgeX]` later (M4 step 4). -/
theorem projectH1_bridgeX_eq_neg_edgeK_of_innerBoundary {n : ℕ} (hn : 0 < n)
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate)
    (z : MaximalCycles n trivialCharacter .line)
    (hz : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z =
      coordinate)
    {Λe : Subgroup RationalGL3} {η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : GoodLineFiber n trivialCharacter Λe (lineCocycle z) η ω ωU θU) :
    projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF) =
      -edgeK n hn ⟨fixedPointH2 rationalLevel (ρn n)
          (QuotientGroup.mk rationalGoodLine : Flags .line) coordinate,
        fixedPointH2_mem_KL_of_innerBoundary inner⟩ := by
  have hKL := fixedPointH2_mem_KL_of_innerBoundary inner
  have hζC : ∀ x, lineCocycle z x = (cocycleAtGoodLine n trivialCharacter z).val.val x :=
    zeta_eq_cocycleAtGoodLine n trivialCharacter z (fun _ => rfl)
  have hval : classOf Λ₁ (ρn n) (cocycleAtGoodLine n trivialCharacter z) =
      fixedPointH2 rationalLevel (ρn n) (QuotientGroup.mk rationalGoodLine : Flags .line)
        coordinate := by
    rw [classOf_cocycleAtGoodLine, hz, psiL_cuspRes_eq]
  have hsub : (⟨classOf Λ₁ (ρn n) (cocycleAtGoodLine n trivialCharacter z),
      zetaClass_mem_KL hF (cocycleAtGoodLine n trivialCharacter z) hζC⟩ : KL n) =
      ⟨fixedPointH2 rationalLevel (ρn n) (QuotientGroup.mk rationalGoodLine : Flags .line)
        coordinate, hKL⟩ :=
    Subtype.ext hval
  have e := congrArg (edgeK n hn) hsub
  rw [projectH1_bridgeX_eq_neg_edgeK hn hF (cocycleAtGoodLine n trivialCharacter z) hζC, e]

/-- **M4, good line, step 2.** `bridgeX` is a parabolic cocycle for an `InnerBoundary` line class,
with *no* Hecke-eigenvalue hypothesis: the underlying class is identified directly with the
already-parabolic `edgeK`-edge of the `InnerBoundary` witness. -/
theorem bridgeX_mem_parabolicCocycles_of_innerBoundary {n : ℕ} (hn : 0 < n)
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate)
    (z : MaximalCycles n trivialCharacter .line)
    (hz : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z =
      coordinate)
    {Λe : Subgroup RationalGL3} {η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : GoodLineFiber n trivialCharacter Λe (lineCocycle z) η ω ωU θU) :
    bridgeX hn 0 (phiTwist_trivial n) hF ∈ parabolicCocycles (arithmeticBinaryRep (n + 1) 0) :=
  mem_parabolicCocycles_of_eq_neg (arithmeticBinaryRep (n + 1) 0)
    (goodLine_edge_parabolic_of_innerBoundary hn inner)
    (projectH1_bridgeX_eq_neg_edgeK_of_innerBoundary hn inner z hz hF)

end TernaryPeriodPolynomials.Argument.FacePairing
