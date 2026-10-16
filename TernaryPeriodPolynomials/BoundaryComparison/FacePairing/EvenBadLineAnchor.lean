module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.AssembleFromAnchor
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.LineFiberOfInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.XInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineValueFromPlaneBadRes
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.PlanePeriodsRealizedVanishesOnBadProof
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicAssembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenBridge

@[expose] public section


/-!
# Face pairing, even `n`, bad-line branch: unconditional assembly from an `InnerBoundary` line
class with nonzero bad-flag cusp residue

Even-`n` analogue of `OddBadLineAnchor.face_pairing_perfect_odd_badLine`, but **unconditional**:
the odd branch is conditional on the input `GoodPlanePeriodsRealizedVanishesOnBad`, needed
there only because the odd dual class `cl'` lives in `parabolicCrossedH1 (levelRep (n+1) (-1))`
and must be transported across the odd-specific endomorphism `thetaH1` before
`GoodPlaneSpan.goodPlanePeriodsRealized` can be applied to it. In the even branch no such
transport is needed: `LocalPairingCaseL0Even.badGoodPairingEven` pairs
`parabolicCrossedH1 (binaryArithmeticRepresentation n)` directly against
`parabolicCrossedH1 (levelRep (n+1) (-1))` (via `planeTransportPar` on its *second* argument only),
so the dual class `cl'` obtained from nondegeneracy already lives in exactly the space
`goodPlanePeriodsRealized` consumes, and `GoodPlanePeriodsRealizedVanishesOnBadProof
.exists_cutoff_automorphicPlaneSpan` (itself parity-generic)
finishes the realization step with no hypothesis at all.

No further Hecke-projector or `AxiomCodeSeparation` routing is introduced here.

Proof outline (mirrors `OddBadLineAnchor.face_pairing_perfect_odd_badLine` step for step, with the
`parabolicBinaryEquiv` carrier conversion dropped — `badGoodPairingEven`'s first argument is already
typed `parabolicCrossedH1 (binaryArithmeticRepresentation n)` — and Step 3 replaced by the direct,
unconditional realization described above):

1. Anchor the bad-line fiber data at the zero plane class to get a witness `hF₀` for which
   `[badX hF₀]` is nonzero in `parabolicCrossedH1 (binaryArithmeticRepresentation n)`
   (`BadXInnerBoundary.mkQ_badX_ne_zero`, driven by the hypothesis `hcuspF`).
2. By the nondegeneracy of `badGoodPairingEven` (`LocalPairingCaseL0Even
   .badGoodPairingEven_left_nondegenerate`, contrapositive), obtain a dual class `cl'` pairing
   nontrivially against `[badX hF₀]`.
3. Realize `cl'` directly: `cl'`'s own underlying class already lies in `parabolicH1
   (levelRep (n+1) (-1)) (upper 1) (lower 1)` (via `parabolicCrossedH1_eq`), so
   `GoodPlaneSpan.goodPlanePeriodsRealized` produces a good-plane-edge witness `ξ'₀` for it
   directly, with no `thetaH1`-style transport in the way; `exists_cutoff_automorphicPlaneSpan`
   then replaces `ξ'₀` by a span witness `ξ'` with the same good-flag residue and zero bad-flag
   residue, giving an `InnerBoundary` plane witness `y_plane`.
4. Re-anchor the bad-line fiber data at `y_plane` to get `hF₂`; show `[badX hF₀] = [badX hF₂]`
   since both represent the same line class `b` (`BadXInnerBoundary
   .mkQ_badX_eq_neg_badLineEdge_cusp` depends only on the line class), transferring step 2's
   nonvanishing to `hF₂`.
5. Supply the plane-side bridge membership for `hF₂` via the new, Hecke-free
   `badX'_mem_parabolicCrossed_of_innerBoundary` below, and identify the transported class of
   `[badX' hF₂]` with `cl'` via `LocalPairingCaseL0Even.mkQ_badX'_eq_planeTransport` and step 3's
   value equation.
6. Conclude the two-term `lineValue` sum at `(z₂, w₂, y_plane)` is nonzero
   (`LocalPairingCaseL0Even.lineValue_of_classes` for the `v = 0` term,
   `GoodLineValueFromPlaneBadRes.lineValue_one_eq_zero_of_cuspRes_false` killing the `v = 1` term),
   and assemble via `AssembleFromAnchor.face_pairing_perfect_of_anchor`.
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

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **The bad-line plane-side bridge membership `hx'par`, even `n`, for an `InnerBoundary` plane
class (Hecke-free).** Even analogue of `BadXPrimeInnerBoundary
.badXOdd'_mem_parabolicCrossed_of_innerBoundary`: for a bad-line fiber `hF` built from an
`InnerBoundary` plane class `y`, the dual-coordinate cocycle `badX'` is parabolic. Supplies
`LocalPairingCaseL0Even.lineValue_of_classes`'s `hx'` hypothesis unconditionally. -/
theorem badX'_mem_parabolicCrossed_of_innerBoundary {n : ℕ} (hn : 0 < n) (heven : Even n)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (hw : EdgePrimitive z w) (y : MaximalCycles n trivialCharacter .plane)
    (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL0.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀)
    (hθU : ∀ γ ∈ latL0.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter
        ((dualityData n trivialCharacter).φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
        (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₀))
    (hinner : InnerBoundary n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y))
    (hF : BadLineFiber n (levelStabilizer e₀) (fun x => z.val.val x L₀)
        (fun x => y.val.val ![(dualityData n trivialCharacter).φ (x 0),
          (dualityData n trivialCharacter).φ (x 1), (dualityData n trivialCharacter).φ (x 2)]
          ((dualityData n trivialCharacter).dualFlag L₀))
        (fun x => w.val x e₀) ωU θU :=
      fiberHyp_line (dualityData n trivialCharacter) endpoint_line_e₀ latL0_le latL0_le_e₀
        z w y hw ωU hωU hdωU θU hθU hdθU) :
    badX' heven hF ∈ parabolicCrossed (binaryArithmeticRepresentation n) := by
  have hyP := goodPlaneEdgeParabolic n hn
    (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) hinner
  rw [← parabolicCrossedH1_eq (levelRep (n + 1) (-1))] at hyP
  have hη' := hη_flag
    (η := fun x => y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      ((dualityData n trivialCharacter).dualFlag L₀)) y (fun _ => rfl)
  have hycls := mkQ_badX'_eq_planeTransport heven hn hF y hη'
  exact mem_parabolicCrossed_of_class hycls (planeTransportH1_mem heven hyP)

/-- **Even `n`, bad-line branch of `face_pairing_perfect`, unconditional.** For an `InnerBoundary`
line class `b` with nonzero bad-flag cusp residue, the face-pairing conclusion holds for `b`. -/
theorem face_pairing_perfect_even_badLine {n : ℕ} (hn : 0 < n) (heven : Even n)
    {b : StratumH2 n trivialCharacter .line} (inner : InnerBoundary n trivialCharacter .line b)
    (hcuspF : cuspRes n trivialCharacter .line false b ≠ 0) :
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
  exact face_pairing_perfect_of_anchor z₂ hz₂ w₂ hw₂ y_plane hy_plane
    ⟨u_plane, fun x e => hu_plane x e⟩ hsum

end TernaryPeriodPolynomials.Argument.FacePairing
