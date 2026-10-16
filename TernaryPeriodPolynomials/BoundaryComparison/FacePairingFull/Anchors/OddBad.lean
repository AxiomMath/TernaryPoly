module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.AssembleFromAnchor
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.LineFiberOfInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.XInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.XPrimeInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineValueFromPlaneBadRes
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.PlaneInner
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge3
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenBridge
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.OddBadLineAnchor
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Anchors.Basic

@[expose] public section


/-!
# Face-pairing anchor, OddBad branch

Copy of `TernaryPeriodPolynomials.Argument.FacePairing.OddBadLineAnchor`'s main theorem with the final
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
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (e₀ L₀ endpoint_line_e₀)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL0
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (badX badXOdd' levelThreeBridgeBadOdd)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd
  (qcls_badXOdd'_eq thetaH1 mkQ_eq_qcls)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even
  (parabolicBinaryEquiv)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.BadLineLocal
open TernaryPeriodPolynomials.LevelThree.BadLineFinal (badLineEdge)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3 (goodPlaneEdge)
open TernaryPeriodPolynomials.Argument.CuspidalSpan
  (automorphicPlaneSpan_subset_innerBoundary)
open TernaryPeriodPolynomials.Argument (automorphicPlaneSpan)


namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Anchors

open TernaryPeriodPolynomials.Argument.FacePairing
open TernaryPeriodPolynomials.Argument.FacePairingFull


/-- **Odd `n`, bad-line branch of `face_pairing_perfect`, conditional on
`GoodPlanePeriodsRealizedVanishesOnBad`.** For an `InnerBoundary` line class `b` with nonzero
bad-flag cusp residue, the face-pairing conclusion holds for `b`. -/
theorem facePairingAnchor_odd_badLine {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    {b : StratumH2 n trivialCharacter .line} (inner : InnerBoundary n trivialCharacter .line b)
    (hcuspF : cuspRes n trivialCharacter .line false b ≠ 0)
    (hreal : GoodPlanePeriodsRealizedVanishesOnBad n hn hodd) :
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


  let c₀ :=
    (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX hn hF₀)
  have hc0mem : c₀ ∈ parabolicCrossedH1 (binaryArithmeticRepresentation n) :=
    Submodule.mem_map_of_mem hxpar₀
  let X₀ :=
    parabolicBinaryEquiv n ⟨c₀, hc0mem⟩
  have hc0ne : (⟨c₀, hc0mem⟩ : parabolicCrossedH1 (binaryArithmeticRepresentation n)) ≠ 0 :=
    fun h => hXne (congrArg Subtype.val h)
  have hX0ne' : X₀ ≠ 0 := by
    intro h
    exact hc0ne ((parabolicBinaryEquiv n).injective
      (h.trans (parabolicBinaryEquiv n).map_zero.symm))
  -- Step 2: nondegeneracy of the bad-line twisted pairing, contrapositive.
  have hexists_cl' : ∃ cl' : parabolicCrossedH1 (levelRep (n + 1) (-1)),
      parabolicPairing (twistedPairing_badLine_goodPlane hodd) X₀ cl' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hX0ne' (badLine_left_nondegenerate hodd X₀ hcon)
  obtain ⟨cl', hcl'ne⟩ := hexists_cl'
  -- Step 3: realize cl' via the new hypothesis.
  have hobtain2 := hreal cl'.1 cl'.2
  obtain ⟨ξ', hξ'mem, hξ'bad0, hξ'val⟩ := hobtain2
  have hinner_plane : InnerBoundary n trivialCharacter .plane ξ' :=
    automorphicPlaneSpan_subset_innerBoundary hξ'mem
  obtain ⟨y_plane, hy_plane, u_plane, hu_plane⟩ := hinner_plane
  -- Step 4: re-anchor the bad-line fiber at y_plane.
  have hobtain3 := exists_badLineFiber_of_innerBoundary hn inner y_plane
  obtain ⟨z₂, w₂, hz₂, hw₂, ωU₂, θU₂, hωU₂, hdωU₂, hθU₂, hdθU₂, hF₂⟩ := hobtain3
  have inner₂ : InnerBoundary n trivialCharacter .line
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₂) := by
    rw [hz₂]; exact inner
  have hxpar₂ : badX hn hF₂ ∈ parabolicCrossed (binaryArithmeticRepresentation n) :=
    badX_mem_parabolicCrossed_of_innerBoundary hn inner z₂ hz₂ w₂ hw₂ y_plane ωU₂ θU₂
      hωU₂ hdωU₂ hθU₂ hdθU₂
  let c₂ :=
    (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX hn hF₂)
  have hc2mem : c₂ ∈ parabolicCrossedH1 (binaryArithmeticRepresentation n) :=
    Submodule.mem_map_of_mem hxpar₂
  let X₂ :=
    parabolicBinaryEquiv n ⟨c₂, hc2mem⟩
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
  have hXeq : X₀ = X₂ := by
    exact congrArg (parabolicBinaryEquiv n) (Subtype.ext hceq)
  have hcl'2 : parabolicPairing (twistedPairing_badLine_goodPlane hodd) X₂ cl' ≠ 0 := hXeq ▸ hcl'ne
  -- Step 5: the plane-side bridge membership for hF₂, and its identification with cl'.
  have hinner_plane' : InnerBoundary n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y_plane) := by
    rw [hy_plane]; exact ⟨y_plane, hy_plane, u_plane, hu_plane⟩
  have hx'par₂ : badXOdd' hodd hF₂ ∈ parabolicCrossed (levelRep (n + 1) (-1)) :=
    badXOdd'_mem_parabolicCrossed_of_innerBoundary hn hodd z₂ w₂ hw₂ y_plane ωU₂ θU₂
      hωU₂ hdωU₂ hθU₂ hdθU₂ hinner_plane'
  let X'₂ : parabolicCrossedH1 (levelRep (n + 1) (-1)) :=
    ⟨_, Submodule.mem_map_of_mem hx'par₂⟩
  have hη'₂ := hη_flag
    (η := fun x => y_plane.val.val ![dualInvolution (x 0), dualInvolution (x 1),
      dualInvolution (x 2)] ((dualityData n trivialCharacter).dualFlag L₀))
    y_plane (fun _ => rfl)
  have hycls₂ := qcls_badXOdd'_eq hodd hn hF₂ y_plane hη'₂
  have hX'2val : (crossedBoundaries (levelRep (n + 1) (-1))).mkQ (badXOdd' hodd hF₂) = cl'.1 := by
    rw [mkQ_eq_qcls, hycls₂, hy_plane]
    exact hξ'val
  have hX'2eq : X'₂ = cl' := Subtype.ext hX'2val
  have hfinal : parabolicPairing (twistedPairing_badLine_goodPlane hodd) X₂ X'₂ ≠ 0 := by
    rw [hX'2eq]; exact hcl'2
  -- Step 6: the lineValue sum is nonzero, and assemble.
  have hfact : (-((n + 1).factorial : ℂ) / 3) ≠ 0 := by
    apply div_ne_zero _ (by norm_num)
    exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1)))
  have hval0 : lineValue traceDataL2 (dualityData n trivialCharacter) 0 z₂ w₂ y_plane ≠ 0 := by
    rw [lineValue_badLine_eq_of_innerBoundary hn hodd inner z₂ w₂ hz₂ hw₂ y_plane ωU₂ θU₂
      hωU₂ hdωU₂ hθU₂ hdθU₂ (hx'par := hx'par₂) (X := X₂) (X' := X'₂) (hxcls := rfl)
      (hx'cls := rfl)]
    exact mul_ne_zero hfact hfinal
  have hval1 : lineValue traceDataL2 (dualityData n trivialCharacter) 1 z₂ w₂ y_plane = 0 :=
    lineValue_one_eq_zero_of_cuspRes_false n trivialCharacter z₂ w₂ hw₂ y_plane (by
      rw [hy_plane]; exact hξ'bad0)
  have hsum : ∑ v : Fin 2,
      lineValue traceDataL2 (dualityData n trivialCharacter) v z₂ w₂ y_plane ≠ 0 := by
    rw [Fin.sum_univ_two, hval1, add_zero]
    exact hval0
  exact ⟨z₂, w₂, _, y_plane, hz₂, hw₂, hy_plane, ⟨u_plane, fun x e => hu_plane x e⟩, hsum⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Anchors
