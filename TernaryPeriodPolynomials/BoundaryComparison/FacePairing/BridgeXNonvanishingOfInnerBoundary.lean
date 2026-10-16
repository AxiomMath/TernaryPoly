module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineFiberOfInnerBoundary

@[expose] public section


/-!
# `bridgeX`'s class is nonzero for an `InnerBoundary` line class with nonzero good-flag residue
(M4, good line, nonvanishing transfer; Hecke-free)

`ParabolicDualityIdentGoodLine.projectH1_bridgeX_eq_neg_phiL` identifies `[bridgeX]` with
`-phiL (cuspRes ...)`, but packages the needed membership `cuspRes ... ∈ ML n` behind a Hecke
joint-eigenclass hypothesis `(c, hc, hy : ... ∈ localJoint ...)`. Reading its proof shows the Hecke
data is used *only* to produce that one membership fact (via `LocalUniqueness.localJoint_le_ML`);
every other step (`projectH1_bridgeX_eq_neg_edgeK`, `zetaClass_mem_KL`, `classOf_cocycleAtGoodLine`)
is already unconditional. `GoodLineFiberOfInnerBoundary.exists_goodLineFiber_of_innerBoundary`
already derives that same membership *without* Hecke, directly from `InnerBoundary`, via
`KLMembership.fixedPointH2_mem_KL_of_innerBoundary` + `PsiLReconciliation.psiL_cuspRes_eq`. This
file reruns `projectH1_bridgeX_eq_neg_phiL`'s proof with that Hecke-free membership substituted, then
chains the result with `LocalUniqueness.phiL_injective` (also Hecke-free) to get: for an
`InnerBoundary` line class, `[bridgeX]` is nonzero whenever the good-flag cusp-residue is nonzero.
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
open TernaryPeriodPolynomials.Spectral.LocalUniqueness
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (e₂ L₁)
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipGood
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Trivial
open TernaryPeriodPolynomials.BoundaryDuality.Kostant (bridgeX phiTwist_trivial)

namespace TernaryPeriodPolynomials.Argument.FacePairing


variable {n : ℕ} {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **Step 0 (Hecke-free).** An `InnerBoundary` line class's good-flag cusp-residue lies in `ML n`
— no Hecke hypothesis needed. -/
theorem cuspRes_mem_ML_of_innerBoundary {b : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line b) :
    cuspRes n trivialCharacter .line true b ∈ ML n := by
  rw [Submodule.mem_comap, psiL_cuspRes_eq]
  exact fixedPointH2_mem_KL_of_innerBoundary inner

/-- **Hecke-free line-side bridge/`phiL` identity.** Same conclusion as
`ParabolicDualityIdentGoodLine.projectH1_bridgeX_eq_neg_phiL`, but with that theorem's Hecke
hypotheses `(c, hc, hy : cuspRes ... ∈ localJoint ...)` replaced by a directly-supplied membership
`hML : cuspRes ... ∈ ML n` (e.g. from `cuspRes_mem_ML_of_innerBoundary` above) — mirrors the
original's proof verbatim, substituting `hML` for its one Hecke-dependent step
(`localJoint_le_ML c hc hy`). -/
theorem projectH1_bridgeX_eq_neg_phiL_of_mem_ML (hn : 0 < n)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line))
    (hML : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc) ∈
      ML n)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (hζ : ∀ x, ζ x = cc.val.val x L₁) :
    projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF) =
      -phiL n hn ⟨cuspRes n trivialCharacter .line true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc),
        hML⟩ := by
  have hζC := zeta_eq_cocycleAtGoodLine n trivialCharacter cc hζ
  have key := projectH1_bridgeX_eq_neg_edgeK hn hF (cocycleAtGoodLine n trivialCharacter cc) hζC
  have hmem : psiL n (cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc)) ∈
      KL n := (Submodule.mem_comap (f := psiL n) (p := KL n)).mp hML
  have hsub : (⟨classOf Λ₁ (ρn n) (cocycleAtGoodLine n trivialCharacter cc),
      zetaClass_mem_KL hF (cocycleAtGoodLine n trivialCharacter cc) hζC⟩ : KL n) =
      ⟨psiL n (cuspRes n trivialCharacter .line true
          (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc)),
        hmem⟩ :=
    Subtype.ext (classOf_cocycleAtGoodLine n cc)
  have e1 : edgeK n hn ⟨classOf Λ₁ (ρn n) (cocycleAtGoodLine n trivialCharacter cc),
      zetaClass_mem_KL hF (cocycleAtGoodLine n trivialCharacter cc) hζC⟩ =
      edgeK n hn ⟨psiL n (cuspRes n trivialCharacter .line true
          (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc)),
        hmem⟩ :=
    congrArg (edgeK n hn) hsub
  have e2 : edgeK n hn ⟨psiL n (cuspRes n trivialCharacter .line true
          (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc)),
        hmem⟩ =
      phiL n hn ⟨cuspRes n trivialCharacter .line true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc),
        hML⟩ :=
    rfl
  exact key.trans (congrArg Neg.neg (e1.trans e2))

/-- **M4, good line, nonvanishing transfer (Hecke-free).** For an arbitrary good-flag cusp-residue
membership `hML : cuspRes ... ∈ ML n`, the class of `bridgeX` is nonzero whenever that cusp-residue
is nonzero. Chains `projectH1_bridgeX_eq_neg_phiL_of_mem_ML` with the already Hecke-free
`LocalUniqueness.phiL_injective`. -/
theorem projectH1_bridgeX_ne_zero_of_mem_ML (hn : 0 < n)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line))
    (hML : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc) ∈
      ML n)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (hζ : ∀ x, ζ x = cc.val.val x L₁)
    (hne : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc) ≠ 0) :
    projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF) ≠ 0 := by
  rw [projectH1_bridgeX_eq_neg_phiL_of_mem_ML hn cc hML hF hζ, neg_ne_zero]
  intro h0
  exact hne (congrArg Subtype.val (phiL_injective hn (h0.trans (map_zero (phiL n hn)).symm)))

/-- **M4, good line, nonvanishing transfer, `InnerBoundary` form (Hecke-free).** Same as
`projectH1_bridgeX_ne_zero_of_mem_ML`, taking the line class's `InnerBoundary` witness directly
instead of the `ML n`-membership it supplies via `cuspRes_mem_ML_of_innerBoundary`. -/
theorem projectH1_bridgeX_ne_zero_of_innerBoundary (hn : 0 < n)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line))
    (inner : InnerBoundary n trivialCharacter .line
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc))
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (hζ : ∀ x, ζ x = cc.val.val x L₁)
    (hne : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc) ≠ 0) :
    projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF) ≠ 0 :=
  projectH1_bridgeX_ne_zero_of_mem_ML hn cc (cuspRes_mem_ML_of_innerBoundary inner) hF hζ hne

end TernaryPeriodPolynomials.Argument.FacePairing
