module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.AssembleFromAnchor
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.LineFiberOfInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.XInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.XPrimeInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineValueFromPlaneBadRes
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.PlaneInner
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge3
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenBridge

@[expose] public section


/-!
# Face pairing, odd `n`, bad-line branch: assembly from an `InnerBoundary` line class with
nonzero bad-flag cusp residue, conditional on a new input

Bad-line analogue of `OddGoodLineAnchor.face_pairing_perfect_odd_goodLine`. The good-line branch
realizes its dual class `cl'` as an *actual* cuspidal-span witness via the real, already-proved
`CuspidalSpan.cuspFormRealized` / `CuspidalSpan.parabolicPeriodRealized_of_cuspFormRealized`
machinery. That machinery is anchored in real cusp-form periods landing in
`PlanePeriodParabolicRealized`, tied to the representation family `arithmeticBinaryRep (n+1) (-1)`
(`SphericalDetection.ArithmeticStabilizerEdge`) — a *different* named construction from this
branch's own `levelRep (n+1) (-1)` (`LevelThree.ParabolicBounds` /
`AxiomCodeBoundaryDuality`), with no confirmed bridge identifying the twist-`(-1)` instances of the
two families (only the twist-`0` pair, `binaryArithmeticRepresentation n` defeq `levelRep (n+1) 0`,
is identified anywhere in the library). So the good-line realization machinery cannot be reused
verbatim for the bad-line dual class `cl' : parabolicCrossedH1 (levelRep (n + 1) (-1))`.

This file instead takes the realization step as an explicit hypothesis
`GoodPlanePeriodsRealizedVanishesOnBad`: every class of `parabolicCrossedH1 (levelRep (n + 1)
(-1))` is the `thetaH1`-image of a good-flag cusp residue of an `automorphicPlaneSpan` witness
whose *bad*-flag cusp residue vanishes. (`thetaH1` — `LocalPairingCaseL0Odd.thetaH1`, declared in
`LocalPairingCaseL0OddPairing.lean` under the same namespace — is the injective transport
endomorphism identifying `qcls (levelRep (n+1)(-1)) (badXOdd' ...)` with the good-plane edge of a
bad-line fiber's plane-side witness; see `qcls_badXOdd'_eq`.) Given this input, the rest of the
derivation is Hecke-free and mirrors the good-line file step for step, with the roles of the two
`lineValue` summands and the two cusp flags exchanged throughout:

1. Anchor the bad-line fiber data at the zero plane class (`exists_badLineFiber_of_innerBoundary
   hn inner 0`) to get a witness `hF₀` for which `[badX hF₀]` is nonzero in `parabolicCrossedH1
   (levelRep (n+1) 0)` (`BadIdentLine.mkQ_badX_ne_zero`, driven by the hypothesis `hcuspF`).
2. By the nondegeneracy of the bad-line twisted pairing (`ParabolicDualityEdgeLevelThree
   .badLine_left_nondegenerate`, contrapositive), obtain a dual class `cl'` pairing nontrivially
   against `[badX hF₀]`.
3. Realize `cl'` via the new hypothesis `GoodPlanePeriodsRealizedVanishesOnBad`: a plane
   stratum class `ξ'` in `automorphicPlaneSpan n` (hence `InnerBoundary`, by
   `CuspidalSpan.automorphicPlaneSpan_subset_innerBoundary`) with zero bad-flag cusp residue and
   `thetaH1`-transported good-flag residue equal to `cl'`.
4. Re-anchor the bad-line fiber data at `ξ'`'s own `InnerBoundary` plane witness `y_plane` to get
   `hF₂`; show `[badX hF₀] = [badX hF₂]` since both represent the *same* line class `b`
   (`BadIdentLine.mkQ_badX_eq_neg_badLineEdge_cusp` depends only on the line class, not the
   particular fiber witness), transferring step 2's nonvanishing to `hF₂`.
5. Supply the plane-side bridge membership for `hF₂` via the Hecke-free
   `BadXPrimeInnerBoundary.badXOdd'_mem_parabolicCrossed_of_innerBoundary`, and identify
   `[badXOdd' hF₂]` with `cl'` via `qcls_badXOdd'_eq` and the hypothesis's own value equation.
6. Conclude the two-term `lineValue` sum at `(z₂, w₂, y_plane)` is nonzero
   (`LineValueBadLineInnerBoundary.lineValue_badLine_eq_of_innerBoundary` for the `v = 0` term,
   `GoodLineValueFromPlaneBadRes.lineValue_one_eq_zero_of_cuspRes_false` killing the `v = 1` term),
   and assemble via `AssembleFromAnchor.face_pairing_perfect_of_anchor`.
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

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **New input (bad-line branch).** Every class of `parabolicCrossedH1 (levelRep (n + 1)
(-1))` arises as the `thetaH1`-transported good-flag cusp residue of an `automorphicPlaneSpan`
witness whose bad-flag cusp residue vanishes. The good-line branch discharges its analogous input
via the real cuspidal-span realization machinery (`CuspidalSpan.cuspFormRealized` /
`parabolicPeriodRealized_of_cuspFormRealized`), anchored in the representation family
`arithmeticBinaryRep (n+1) (-1)`; that machinery does not transfer to this branch's own
`levelRep (n+1) (-1)`, with no confirmed bridge between the twist-`(-1)` instances of the two
families. Taken here as an explicit hypothesis. -/
def GoodPlanePeriodsRealizedVanishesOnBad (n : ℕ) (hn : 0 < n) (hodd : Odd n) : Prop :=
  ∀ cl ∈ parabolicCrossedH1 (levelRep (n + 1) (-1)),
    ∃ ξ' ∈ automorphicPlaneSpan n,
      cuspRes n trivialCharacter .plane false ξ' = 0 ∧
      thetaH1 hodd (goodPlaneEdge hn (cuspRes n trivialCharacter .plane true ξ')) = cl

/-- **Odd `n`, bad-line branch of `face_pairing_perfect`, conditional on
`GoodPlanePeriodsRealizedVanishesOnBad`.** For an `InnerBoundary` line class `b` with nonzero
bad-flag cusp residue, the face-pairing conclusion holds for `b`. -/
theorem face_pairing_perfect_odd_badLine {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    {b : StratumH2 n trivialCharacter .line} (inner : InnerBoundary n trivialCharacter .line b)
    (hcuspF : cuspRes n trivialCharacter .line false b ≠ 0)
    (hreal : GoodPlanePeriodsRealizedVanishesOnBad n hn hodd) :
    ∃ ξ' : StratumH2 n trivialCharacter .plane, InnerBoundary n trivialCharacter .plane ξ' ∧
      ∀ z : MaximalCycles n trivialCharacter .line,
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b →
      ∀ w : EdgeCochains n trivialCharacter 1,
        (∀ x e, z.val.val x (endpoint .line e) = differentialOneRaw w.val x e) →
      ∀ y : MaximalCycles n trivialCharacter .plane,
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ' →
      ∀ γ : (Fin 4 → RationalGL3) → Flags .line → ℂ,
        γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 →
        (∀ x F, differentialThreeRaw γ x F =
          dualPairing n (z.val.val ![x 0, x 1, x 2] F)
            (y.val.val ![dualInvolution (x 2), dualInvolution (x 3), dualInvolution (x 4)]
              (dualFlag F))) →
        ¬ BoundaryExact (fun x e =>
          dualPairing n (w.val ![x 0, x 1] e)
            (y.val.val ![dualInvolution (x 1), dualInvolution (x 2), dualInvolution (x 3)]
              (dualFlag (endpoint .line e))) - γ x (endpoint .line e)) := by
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
  exact face_pairing_perfect_of_anchor z₂ hz₂ w₂ hw₂ y_plane hy_plane
    ⟨u_plane, fun x e => hu_plane x e⟩ hsum

end TernaryPeriodPolynomials.Argument.FacePairing
