module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.LineValueGoodLineInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.BridgeXPrimeInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.BridgeXNonvanishingOfInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineEdgeParabolic
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineFiberOfInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.InnerPlaneEdgeParabolicProof
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.GoodFlagTransport
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Shapiro
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.OddBad

@[expose] public section


/-!
# Value formula at the good line for arbitrary inner classes: odd `n`

For odd `n > 0` and inner classes `b` (line), `ξ` (plane),
`lineValue 1 z w y = (n+1)! · ⟨goodLineParabolic b, badPlaneParabolic ξ⟩_{GL₂(ℤ)}` for all
representatives (`lineValue_one_odd`), where `goodLineParabolic b = phiL (cuspRes true b)` and
`badPlaneParabolic ξ = edgeH2 (cuspRes false ξ)` are parabolic classes of `H¹(GL₂(ℤ), Sym^{n+1})`,
`H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`.  The plane class is first replaced by one vanishing at the good plane
cusp with the same bad-plane coordinate (`exists_decoupled_plane`, Shapiro realization), for which
the library bridge theorem `LineValueGoodLineInnerBoundary.lineValue_goodLine_eq_of_innerBoundary` applies;
`lineValue 1` depends only on the bad-plane coordinate (`lineValue_one_congr_plane`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag cuspFlag_good_iff)
open TernaryPeriodPolynomials.Spectral.LocalUniqueness (phiL ML)
open TernaryPeriodPolynomials.Spectral.GoodLineHecke (edgeK)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (rationalGoodLine)
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Duality (dualInvolution)
open TernaryPeriodPolynomials.BoundaryDuality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₁)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.Argument.FacePairing
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

variable {n : ℕ}

/-- An inner plane class can be modified, without changing its bad-plane cusp coordinate, to one
vanishing at the good plane cusp. -/
theorem exists_decoupled_plane (ξ : innerClasses n .plane) :
    ∃ ξ' : innerClasses n .plane, cuspRes n trivialCharacter .plane true ξ'.val = 0 ∧
      cuspRes n trivialCharacter .plane false ξ'.val = cuspRes n trivialCharacter .plane false ξ.val := by
  have hg : GoodFlag .plane (cuspFlag .plane true) := (cuspFlag_good_iff .plane true).mpr rfl
  have hb : ¬ GoodFlag .plane (cuspFlag .plane false) := fun h => by
    have := (cuspFlag_good_iff .plane false).mp h
    exact absurd this (by decide)
  obtain ⟨ξ', h'⟩ := Face.innerToLocal_surjective n (cuspFlag .plane true) (cuspFlag .plane false) hg hb
    (0, (Face.innerToLocal n (cuspFlag .plane true) (cuspFlag .plane false) hg hb ξ).2)
  refine ⟨ξ', congrArg Subtype.val (congrArg Prod.fst h'), congrArg Subtype.val (congrArg Prod.snd h')⟩

/-- The good-flag Shapiro coordinate of an inner line class, in `ML`. -/
def innerLineToML : innerClasses n .line →ₗ[ℂ] ML n :=
  ((cuspRes n trivialCharacter .line true).comp (innerClasses n .line).subtype).codRestrict _
    fun b => cuspRes_mem_ML_of_innerBoundary (n := n) b.property

theorem phiL_innerLineToML_mem (hn : 0 < n) (b : innerClasses n .line) :
    phiL n hn (innerLineToML b) ∈ parabolicH1 (arithmeticBinaryRep (n + 1) 0) := by
  have hbin : InnerBoundary n trivialCharacter .line b.val := b.property
  have h := goodLine_edge_parabolic_of_innerBoundary hn hbin
  have e : phiL n hn (innerLineToML b) = edgeK n hn ⟨fixedPointH2 rationalLevel (ρn n)
      (QuotientGroup.mk rationalGoodLine : Flags .line) b.val,
        fixedPointH2_mem_KL_of_innerBoundary hbin⟩ :=
    congrArg (edgeK n hn) (Subtype.ext (psiL_cuspRes_eq n b.val))
  rw [e]
  exact h

/-- The good-line literal dictionary (level one): `b ↦ phiL(cuspRes true b)`, a parabolic class of
`H¹(GL₂(ℤ), Sym^{n+1})`. -/
def goodLineParabolic (hn : 0 < n) :
    innerClasses n .line →ₗ[ℂ] parabolicH1 (arithmeticBinaryRep (n + 1) 0) :=
  ((phiL n hn).comp innerLineToML).codRestrict _ (phiL_innerLineToML_mem hn)

theorem edgeH2_cuspRes_false_mem (hn : 0 < n) (hodd : Odd n) (ξ : innerClasses n .plane) :
    IdentityPlaneHecke.edgeH2 n hn hodd (cuspRes n trivialCharacter .plane false ξ.val) ∈
      parabolicH1 (arithmeticBinaryRep (n + 1) (-1)) := by
  obtain ⟨ξ', h0, hf⟩ := exists_decoupled_plane ξ
  rw [← hf]
  exact CuspidalSpan.innerPlaneEdgeParabolic_proof hn hodd ξ'.val
    (GoodPlaneSpan.vanishesOnGood_of_cuspRes_good_eq_zero ξ'.val h0) ξ'.property

/-- The bad-plane (identity plane) literal dictionary (level one): `ξ ↦ edgeH2(cuspRes false ξ)`, a
parabolic class of `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`. -/
def badPlaneParabolic (hn : 0 < n) (hodd : Odd n) :
    innerClasses n .plane →ₗ[ℂ] parabolicH1 (arithmeticBinaryRep (n + 1) (-1)) :=
  ((IdentityPlaneHecke.edgeH2 n hn hodd).comp ((cuspRes n trivialCharacter .plane false).comp
    (innerClasses n .plane).subtype)).codRestrict _ (edgeH2_cuspRes_false_mem hn hodd)

theorem lineValue_one_congr_plane (z : MaximalCycles n trivialCharacter .line)
    (w : EdgeCochains n trivialCharacter 1) (hw : EdgePrimitive z w)
    (y y' : MaximalCycles n trivialCharacter .plane)
    (h : cuspRes n trivialCharacter .plane false
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) =
      cuspRes n trivialCharacter .plane false
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y')) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y =
      lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y' := by
  have hgood1' : CuspDualL2.good 1 = false := rfl
  have hF1 : ∃ γ : rationalLevel, γ.val • cuspFlag .plane false =
      (dualityData n trivialCharacter).dualFlag (traceDataL2.lineRep 1) := by
    rw [← hgood1']
    exact CuspDualL2.hdual_L2 n trivialCharacter 1
  refine CuspSeparation.lineValue_eq_of_fixedPointH2_eq traceDataL2 (dualityData n trivialCharacter)
    1 hw ?_
  have h0 := CuspSeparation.fixedPointH2_eq_zero_of_cuspRes hF1
    (a := classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y -
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y')
    (by rw [map_sub, h, sub_self])
  exact sub_eq_zero.mp ((map_sub _ _ _).symm.trans h0)

section Generic

variable {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

theorem projectH1_bridgeX_eq_goodLineParabolic (hn : 0 < n) (b : innerClasses n .line)
    (cc : MaximalCycles n trivialCharacter .line)
    (hcc : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc = b.val)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (hζ : ∀ x, ζ x = cc.val.val x L₁) :
    projectH1 (arithmeticBinaryRep (n + 1) 0)
        (Kostant.bridgeX hn 0 (Kostant.phiTwist_trivial n) hF) =
      -((goodLineParabolic hn b : parabolicH1 (arithmeticBinaryRep (n + 1) 0)) :
        groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0)) := by
  have hbin : InnerBoundary n trivialCharacter .line
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc) := by
    rw [hcc]; exact b.property
  rw [projectH1_bridgeX_eq_neg_phiL_of_mem_ML hn cc (cuspRes_mem_ML_of_innerBoundary hbin) hF hζ]
  refine congrArg Neg.neg (congrArg (phiL n hn) (Subtype.ext ?_))
  change cuspRes n trivialCharacter .line true _ = cuspRes n trivialCharacter .line true b.val
  rw [hcc]

theorem projectH1_bridgeX'_eq_badPlaneParabolic (hn : 0 < n) (hodd : Odd n)
    (ξ : innerClasses n .plane) (y : MaximalCycles n trivialCharacter .plane)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1),
      dualInvolution (x 2)] ((dualityData n trivialCharacter).dualFlag L₁)) :
    projectH1 (arithmeticBinaryRep (n + 1) (-1))
        (Kostant.bridgeX' (-1) (Kostant.psiTwist_trivial hodd) hF) =
      -((badPlaneParabolic hn hodd ξ : parabolicH1 (arithmeticBinaryRep (n + 1) (-1))) :
        groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))) := by
  rw [LocalPairingCaseL1Trivial.projectH1_bridgeX'_eq_neg_edge hn hodd hF y hη, hy]
  rfl

end Generic

theorem parabolicPairing_eq_of_neg {M M' : Rep.{0, 0, 0} ℂ GL2Z}
    {B : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ} (P : TwistedPairing M M' B) {X : parabolicH1 M}
    {Y : parabolicH1 M'} {a : groupCohomology.H1 M} {b : groupCohomology.H1 M'}
    (ha : a = -(X : groupCohomology.H1 M)) (hb : b = -(Y : groupCohomology.H1 M'))
    (hma : a ∈ parabolicH1 M) (hmb : b ∈ parabolicH1 M') :
    parabolicPairing P (⟨a, hma⟩ : parabolicH1 M) (⟨b, hmb⟩ : parabolicH1 M') =
      parabolicPairing P X Y := by
  have h1 : (⟨a, hma⟩ : parabolicH1 M) = -X := Subtype.ext ha
  have h2 : (⟨b, hmb⟩ : parabolicH1 M') = -Y := Subtype.ext hb
  rw [h1, h2]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

theorem lineValue_one_odd_aux (hn : 0 < n) (hodd : Odd n) (b : innerClasses n .line)
    (ξ : innerClasses n .plane) (hgood : cuspRes n trivialCharacter .plane true ξ.val = 0)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val)
    (hw : EdgePrimitive z w) (y : MaximalCycles n trivialCharacter .plane)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val)
    (flat : PlaneEdgeExact y) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y =
      ((n + 1).factorial : ℂ) *
        parabolicPairing (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd)
          (goodLineParabolic hn b) (badPlaneParabolic hn hodd ξ) := by
  have hbin : InnerBoundary n trivialCharacter .line b.val := b.property
  obtain ⟨z₂, w₂, hz₂, hw₂, ωU, θU, hωU, hdωU, hθU, hdθU, hF⟩ :=
    exists_goodLineFiber_of_innerBoundary hn hodd hbin y
  have hgood' : VanishesOnGood n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) := by
    rw [hy]; exact GoodPlaneSpan.vanishesOnGood_of_cuspRes_good_eq_zero ξ.val hgood
  have hinner_y : InnerBoundary n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) := by
    rw [hy]; exact ξ.property
  have hxpar := bridgeX_mem_parabolicCocycles_of_innerBoundary hn hbin z₂ hz₂ hF
  have hx'par := bridgeX'_mem_parabolicCocycles_of_innerBoundary hn hodd y hgood' hinner_y hF
    (fun _ => rfl)
  have h1 := lineValue_goodLine_eq_of_innerBoundary hn hodd hbin z₂ w₂ hz₂ hw₂ y ωU θU hωU hdωU
    hθU hdθU (hF := hF) (hxpar := hxpar) (hx'par := hx'par)
  have e1 := parabolicPairing_eq_of_neg (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd)
    (projectH1_bridgeX_eq_goodLineParabolic hn b z₂ hz₂ hF (fun _ => rfl))
    (projectH1_bridgeX'_eq_badPlaneParabolic hn hodd ξ y hy hF (fun _ => rfl))
    (Submodule.mem_map_of_mem hxpar) (Submodule.mem_map_of_mem hx'par)
  have h2 := LocalIndependence.lineValue_eq_of_line_fixedPointH2_eq traceDataL2
    (dualityData n trivialCharacter) 1 hw hw₂ flat
    (congrArg (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (traceDataL2.lineRep 1)) (hz.trans hz₂.symm))
  exact h2.trans (h1.trans (congrArg₂ (· * ·) (neg_neg _) e1))

theorem badPlaneParabolic_congr (hn : 0 < n) (hodd : Odd n) (ξ ξ' : innerClasses n .plane)
    (h : cuspRes n trivialCharacter .plane false ξ'.val =
      cuspRes n trivialCharacter .plane false ξ.val) :
    badPlaneParabolic hn hodd ξ' = badPlaneParabolic hn hodd ξ :=
  Subtype.ext (congrArg (IdentityPlaneHecke.edgeH2 n hn hodd) h)

theorem lineValue_one_odd (hn : 0 < n) (hodd : Odd n) (b : innerClasses n .line)
    (ξ : innerClasses n .plane) (z : MaximalCycles n trivialCharacter .line)
    (w : EdgeCochains n trivialCharacter 1)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val)
    (hw : EdgePrimitive z w) (y : MaximalCycles n trivialCharacter .plane)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y =
      ((n + 1).factorial : ℂ) *
        parabolicPairing (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd)
          (goodLineParabolic hn b) (badPlaneParabolic hn hodd ξ) :=
  (exists_decoupled_plane ξ).elim fun ξ' hξ' =>
    (exists_plane_rep ξ').elim fun y' hy'flat =>
      (lineValue_one_congr_plane z w hw y y' (by
        rw [hy, hy'flat.1]; exact hξ'.2.symm)).trans
        ((lineValue_one_odd_aux hn hodd b ξ' hξ'.1 z w hz hw y' hy'flat.1 hy'flat.2).trans
          (congrArg (fun t => ((n + 1).factorial : ℂ) * t)
            (congrArg (parabolicPairing (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd)
              (goodLineParabolic hn b)) (badPlaneParabolic_congr hn hodd ξ ξ' hξ'.2))))

end TernaryPeriodPolynomials.Argument.FacePairingFull.Literal
