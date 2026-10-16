module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.AssembleFromAnchor
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.LineFiberOfInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.XInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineValueFromPlaneBadRes
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.PlanePeriodsRealizedVanishesOnBadProof
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicAssembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenBridge
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.EvenBadLineAnchor
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Anchors.Basic

@[expose] public section


/-!
# Face-pairing anchor, EvenBad branch

Copy of `TernaryPeriodPolynomials.Argument.FacePairing.EvenBadLineAnchor`'s main theorem with the final
assembly step replaced: instead of concluding the non-exactness statement of
`face_pairing_perfect`, it returns the `FacePairingAnchor` (representatives with a nonzero
`lineValue` sum), which certifies the stronger non-vanishing of the trace pairing. The proof body
is verbatim the original one up to its last line.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower)
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (e₀ L₀ endpoint_line_e₀)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL0 (fiberHyp_line)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossed parabolicCrossedH1 parabolicCrossedH1_eq)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant (badX badX')
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even
  (badGoodPairingEven badGoodPairingEven_left_nondegenerate planeTransportH1 planeTransportH1_mem
    mkQ_badX'_eq_planeTransport mem_parabolicCrossed_of_class lineValue_of_classes)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.TwoGenerator (parabolicH1)
open TernaryPeriodPolynomials.LevelThree.BadLineLocal
open TernaryPeriodPolynomials.LevelThree.BadLineFinal (badLineEdge)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3 (goodPlaneEdge)
open TernaryPeriodPolynomials.Argument.CuspidalSpan
  (automorphicPlaneSpan_subset_innerBoundary)
open TernaryPeriodPolynomials.Argument.GoodPlaneSpan
  (goodPlaneEdgeParabolic goodPlanePeriodsRealized)
open TernaryPeriodPolynomials.Argument (automorphicPlaneSpan)


namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Anchors

open TernaryPeriodPolynomials.Argument.FacePairing
open TernaryPeriodPolynomials.Argument.FacePairingFull


/-- **Even `n`, bad-line branch of `face_pairing_perfect`, unconditional.** For an `InnerBoundary`
line class `b` with nonzero bad-flag cusp residue, the face-pairing conclusion holds for `b`. -/
theorem facePairingAnchor_even_badLine {n : ℕ} (hn : 0 < n) (heven : Even n)
    {b : StratumH2 n trivialCharacter .line} (inner : InnerBoundary n trivialCharacter .line b)
    (hcuspF : cuspRes n trivialCharacter .line false b ≠ 0) :
    FacePairingAnchor b := by
  -- Step 1: anchor the bad-line fiber at the zero plane class.
  have hobtain1 := exists_badLineFiber_of_innerBoundary hn inner (0 : MaximalCycles n trivialCharacter .plane)
  obtain ⟨z₀, w₀, hz₀, hw₀, ωU₀, θU₀, hωU₀, hdωU₀, hθU₀, hdθU₀, hF₀⟩ := hobtain1
  have inner₀ : InnerBoundary n trivialCharacter .line
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀) := by
    rw [hz₀]; exact inner
  have hne₀ : cuspRes n trivialCharacter .line false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀) ≠ 0 := by
    rw [hz₀]; exact hcuspF
  have hXne : (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX hn hF₀) ≠ 0 :=
    mkQ_badX_ne_zero hn hF₀ z₀ (fun _ => rfl) hne₀
  have hxpar₀ : badX hn hF₀ ∈ parabolicCrossed (binaryArithmeticRepresentation n) :=
    badX_mem_parabolicCrossed_of_innerBoundary hn inner z₀ hz₀ w₀ hw₀
      (0 : MaximalCycles n trivialCharacter .plane) ωU₀ θU₀ hωU₀ hdωU₀ hθU₀ hdθU₀
  let c₀ := (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX hn hF₀)
  have hc0mem : c₀ ∈ parabolicCrossedH1 (binaryArithmeticRepresentation n) :=
    Submodule.mem_map_of_mem hxpar₀
  have hc0ne : (⟨c₀, hc0mem⟩ : parabolicCrossedH1 (binaryArithmeticRepresentation n)) ≠ 0 :=
    fun h => hXne (congrArg Subtype.val h)
  -- Step 2: nondegeneracy of `badGoodPairingEven`, contrapositive.
  have hexists_cl' : ∃ cl' : parabolicCrossedH1 (levelRep (n + 1) (-1)),
      badGoodPairingEven heven
        (⟨c₀, hc0mem⟩ : parabolicCrossedH1 (binaryArithmeticRepresentation n)) cl' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc0ne (badGoodPairingEven_left_nondegenerate heven _ hcon)
  obtain ⟨cl', hcl'ne⟩ := hexists_cl'
  -- Step 3: realize `cl'` directly via the good-plane supply and the cutoff lemma.
  have hcl'mem : (cl' : CrossedH1 (levelRep (n + 1) (-1))) ∈
      parabolicH1 (levelRep (n + 1) (-1)) (upper 1) (lower 1) := by
    rw [← parabolicCrossedH1_eq (levelRep (n + 1) (-1))]
    exact cl'.2
  have hobtain2 := goodPlanePeriodsRealized n hn (cl' : CrossedH1 (levelRep (n + 1) (-1))) hcl'mem
  obtain ⟨ξ'₀, hξ'₀, hedge⟩ := hobtain2
  have hobtain3 := exists_cutoff_automorphicPlaneSpan (n := n) true hξ'₀
  obtain ⟨ξ', hξ', hkeep, hkill⟩ := hobtain3
  have hinner_plane : InnerBoundary n trivialCharacter .plane ξ' :=
    automorphicPlaneSpan_subset_innerBoundary hξ'
  obtain ⟨y_plane, hy_plane, u_plane, hu_plane⟩ := hinner_plane
  -- Step 4: re-anchor the bad-line fiber at y_plane.
  have hobtain4 := exists_badLineFiber_of_innerBoundary hn inner y_plane
  obtain ⟨z₂, w₂, hz₂, hw₂, ωU₂, θU₂, hωU₂, hdωU₂, hθU₂, hdθU₂, hF₂⟩ := hobtain4
  have inner₂ : InnerBoundary n trivialCharacter .line
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₂) := by
    rw [hz₂]; exact inner
  have hxpar₂ : badX hn hF₂ ∈ parabolicCrossed (binaryArithmeticRepresentation n) :=
    badX_mem_parabolicCrossed_of_innerBoundary hn inner z₂ hz₂ w₂ hw₂ y_plane ωU₂ θU₂
      hωU₂ hdωU₂ hθU₂ hdθU₂
  let c₂ := (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX hn hF₂)
  have hc2mem : c₂ ∈ parabolicCrossedH1 (binaryArithmeticRepresentation n) :=
    Submodule.mem_map_of_mem hxpar₂
  have hmkQ0 : c₀ = -badLineEdge n hn ⟨cuspRes n trivialCharacter .line false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀),
      cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary inner₀⟩ :=
    mkQ_badX_eq_neg_badLineEdge_cusp hn hF₀ z₀ (fun _ => rfl)
  have hmkQ2 : c₂ = -badLineEdge n hn ⟨cuspRes n trivialCharacter .line false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₂),
      cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary inner₂⟩ :=
    mkQ_badX_eq_neg_badLineEdge_cusp hn hF₂ z₂ (fun _ => rfl)
  have hval_eq : cuspRes n trivialCharacter .line false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀) =
      cuspRes n trivialCharacter .line false
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₂) := by
    rw [hz₀, hz₂]
  have hceq : c₀ = c₂ := by
    calc c₀ = -badLineEdge n hn ⟨cuspRes n trivialCharacter .line false
          (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀),
          cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary inner₀⟩ := hmkQ0
      _ = -badLineEdge n hn ⟨cuspRes n trivialCharacter .line false
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₂),
            cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary inner₂⟩ :=
        congrArg Neg.neg (congrArg (badLineEdge n hn) (Subtype.ext hval_eq))
      _ = c₂ := hmkQ2.symm
  have hXeq : (⟨c₀, hc0mem⟩ : parabolicCrossedH1 (binaryArithmeticRepresentation n)) =
      ⟨c₂, hc2mem⟩ := Subtype.ext hceq
  have hcl'2 : badGoodPairingEven heven
      (⟨c₂, hc2mem⟩ : parabolicCrossedH1 (binaryArithmeticRepresentation n)) cl' ≠ 0 :=
    hXeq ▸ hcl'ne
  -- Step 5: the plane-side bridge membership for hF₂, and the value equation for cl'.
  have hinner_plane' : InnerBoundary n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y_plane) := by
    rw [hy_plane]; exact ⟨y_plane, hy_plane, u_plane, hu_plane⟩
  have hx'par₂ : badX' heven hF₂ ∈ parabolicCrossed (binaryArithmeticRepresentation n) :=
    badX'_mem_parabolicCrossed_of_innerBoundary hn heven z₂ w₂ hw₂ y_plane ωU₂ θU₂
      hωU₂ hdωU₂ hθU₂ hdθU₂ hinner_plane'
  have hη'₂ := hη_flag
    (η := fun x => y_plane.val.val ![dualInvolution (x 0), dualInvolution (x 1),
      dualInvolution (x 2)] ((dualityData n trivialCharacter).dualFlag L₀))
    y_plane (fun _ => rfl)
  have hvaleq : goodPlaneEdge hn (cuspRes n trivialCharacter .plane true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y_plane)) =
      (cl' : CrossedH1 (levelRep (n + 1) (-1))) := by
    rw [hy_plane, hkeep, hedge]
  have hY : (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX' heven hF₂) =
      planeTransportH1 heven (cl' : CrossedH1 (levelRep (n + 1) (-1))) := by
    rw [mkQ_badX'_eq_planeTransport heven hn hF₂ y_plane hη'₂, hvaleq]
  have hval0 : lineValue traceDataL2 (dualityData n trivialCharacter) 0 z₂ w₂ y_plane =
      (((n + 1).factorial : ℂ) / 3) * badGoodPairingEven heven
        (⟨c₂, hc2mem⟩ : parabolicCrossedH1 (binaryArithmeticRepresentation n)) cl' :=
    lineValue_of_classes heven hn hF₂ z₂ w₂ y_plane hw₂ hωU₂ hdωU₂ hθU₂ hdθU₂
      ⟨c₂, hc2mem⟩ cl' hxpar₂ hx'par₂ rfl hY
  have hfact : (((n + 1).factorial : ℂ) / 3) ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))) (by norm_num)
  have hval0' : lineValue traceDataL2 (dualityData n trivialCharacter) 0 z₂ w₂ y_plane ≠ 0 := by
    rw [hval0]
    exact mul_ne_zero hfact hcl'2
  -- Step 6: the lineValue sum is nonzero, and assemble.
  have hval1 : lineValue traceDataL2 (dualityData n trivialCharacter) 1 z₂ w₂ y_plane = 0 :=
    lineValue_one_eq_zero_of_cuspRes_false n trivialCharacter z₂ w₂ hw₂ y_plane (by
      rw [hy_plane]; exact hkill)
  have hsum : ∑ v : Fin 2,
      lineValue traceDataL2 (dualityData n trivialCharacter) v z₂ w₂ y_plane ≠ 0 := by
    rw [Fin.sum_univ_two, hval1, add_zero]
    exact hval0'
  exact ⟨z₂, w₂, _, y_plane, hz₂, hw₂, hy_plane, ⟨u_plane, fun x e => hu_plane x e⟩, hsum⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Anchors
