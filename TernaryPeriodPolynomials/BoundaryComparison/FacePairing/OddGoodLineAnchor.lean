module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.AssembleFromAnchor
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineFiberOfInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.BridgeXInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.BridgeXNonvanishingOfInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.BridgeXPrimeInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.LineValueGoodLineInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.LineValueFromPlaneGoodRes
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.OddCase
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.BadPlaneSupply
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.PlaneInner
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.GoodFlagTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL1TrivialValue

@[expose] public section


/-!
# Face pairing, odd `n`, good-line branch: assembly from an `InnerBoundary` line class with
nonzero good-flag cusp residue

Assembles `face_pairing_perfect_odd_goodLine`: for odd `n` and an `InnerBoundary` line class `b`
whose good-flag (`v = true`) cusp residue is nonzero, the face-pairing conclusion holds for `b`.

Proof outline:

1. Anchor the good-line fiber data at the zero plane class (`exists_goodLineFiber_of_innerBoundary
   hn hodd inner 0`) to get a witness `hF₀` for which `[bridgeX hF₀]` is nonzero in
   `parabolicH1 (arithmeticBinaryRep (n+1) 0)` (`BridgeXNonvanishingOfInnerBoundary
   .projectH1_bridgeX_ne_zero_of_innerBoundary`, driven by the hypothesis `hcuspT`).
2. By the nondegeneracy of the good-line twisted pairing
   (`ParabolicDualityEdgeLevelOne.goodLine_left_nondegenerate_trivial`, contrapositive), obtain a
   dual class `cl'` pairing nontrivially against `[bridgeX hF₀]`.
3. Realize `cl'` as the plane-edge class of an actual cuspidal-span witness `b_plane`
   (`CuspidalSpan.parabolicPeriodRealized_of_cuspFormRealized` fed by `CuspidalSpan
   .cuspFormRealized`), which is automatically `InnerBoundary` and vanishes at the good-plane cusp
   (`CuspidalSpan.automorphicPlaneSpan_subset_innerBoundary`,
   `GoodPlaneSpan.vanishesOnGood_of_cuspRes_good_eq_zero`).
4. Re-anchor the good-line fiber data at `b_plane`'s own `InnerBoundary` plane witness `y_plane`
   to get `hF₂`; show `[bridgeX hF₀] = [bridgeX hF₂]` since both represent the *same* line class `b`
   (`BridgeXNonvanishingOfInnerBoundary.projectH1_bridgeX_eq_neg_phiL_of_mem_ML` depends only on the
   line class, not the particular fiber witness), transferring step 2's nonvanishing to `hF₂`.
5. Supply the plane-side bridge membership `hx'par` for `hF₂` via the Hecke-free
   `BridgeXPrimeInnerBoundary.bridgeX'_mem_parabolicCocycles_of_innerBoundary`, and identify
   `[bridgeX' hF₂]` with (minus) `b_plane`'s own plane-edge class
   (`LocalPairingCaseL1TrivialValue.projectH1_bridgeX'_eq_neg_edge`), matching `cl'` by construction.
6. Conclude the two-term `lineValue` sum at `(z₂, w₂, y_plane)` is nonzero
   (`LineValueGoodLineInnerBoundary.lineValue_goodLine_eq_of_innerBoundary` for the `v = 1` term,
   `BadLineValueFromPlaneGoodRes.lineValue_zero_eq_zero_of_cuspRes_true` killing the `v = 0` term),
   and assemble via `AssembleFromAnchor.face_pairing_perfect_of_anchor`.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspRes)
open TernaryPeriodPolynomials.Spectral.LocalUniqueness (phiL ML)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (bridgeX bridgeX' phiTwist_trivial psiTwist_trivial)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Trivial
  (projectH1_bridgeX'_eq_neg_edge)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)
open TernaryPeriodPolynomials.Argument.CuspidalSpan
open TernaryPeriodPolynomials.Argument.GoodPlaneSpan (vanishesOnGood_of_cuspRes_good_eq_zero)

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **Odd `n`, good-line branch of `face_pairing_perfect`.** For an `InnerBoundary` line class `b`
with nonzero good-flag cusp residue, the face-pairing conclusion holds for `b`. -/
theorem face_pairing_perfect_odd_goodLine {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    {b : StratumH2 n trivialCharacter .line} (inner : InnerBoundary n trivialCharacter .line b)
    (hcuspT : cuspRes n trivialCharacter .line true b ≠ 0) :
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
  -- Step 1: anchor the good-line fiber at the zero plane class.
  have hobtain1 := exists_goodLineFiber_of_innerBoundary hn hodd inner
      (0 : MaximalCycles n trivialCharacter .plane)
  obtain ⟨z₀, w₀, hz₀, hw₀, ωU₀, θU₀, hωU₀, hdωU₀, hθU₀, hdθU₀, hF₀⟩ := hobtain1
  have inner₀ : InnerBoundary n trivialCharacter .line
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀) := by
    rw [hz₀]; exact inner
  have hne₀ : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀) ≠ 0 := by
    rw [hz₀]; exact hcuspT
  have hXp0ne : projectH1 (arithmeticBinaryRep (n + 1) 0)
      (bridgeX hn 0 (phiTwist_trivial n) hF₀) ≠ 0 :=
    projectH1_bridgeX_ne_zero_of_innerBoundary hn z₀ inner₀ hF₀ (fun _ => rfl) hne₀
  have hxpar₀ : bridgeX hn 0 (phiTwist_trivial n) hF₀ ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) 0) :=
    bridgeX_mem_parabolicCocycles_of_innerBoundary hn inner z₀ hz₀ hF₀
  let Xp₀ : parabolicH1 (arithmeticBinaryRep (n + 1) 0) :=
    ⟨projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF₀),
      Submodule.mem_map_of_mem hxpar₀⟩
  have hXp0ne' : Xp₀ ≠ 0 := fun h => hXp0ne (congrArg Subtype.val h)
  -- Step 2: nondegeneracy of the good-line twisted pairing, contrapositive.
  have hexists_cl' : ∃ cl' : parabolicH1 (arithmeticBinaryRep (n + 1) (-1)),
      parabolicPairing (twistedPairing_goodLine_trivial hodd) Xp₀ cl' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hXp0ne' (goodLine_left_nondegenerate_trivial hodd Xp₀ hcon)
  obtain ⟨cl', hcl'ne⟩ := hexists_cl'
  -- Step 3: realize cl' via a cuspidal period on the automorphic plane span.
  have hobtain2 := parabolicPeriodRealized_of_cuspFormRealized n hn hodd (cuspFormRealized n hn hodd)
      cl'.1 cl'.2
  obtain ⟨b_plane, hb_mem, hb_good0, hb_edge⟩ := hobtain2
  have hinner_plane : InnerBoundary n trivialCharacter .plane b_plane :=
    automorphicPlaneSpan_subset_innerBoundary hb_mem
  have hgood_plane : VanishesOnGood n trivialCharacter .plane b_plane :=
    vanishesOnGood_of_cuspRes_good_eq_zero b_plane hb_good0
  obtain ⟨y_plane, hy_plane, u_plane, hu_plane⟩ := hinner_plane
  -- Step 4: re-anchor the good-line fiber at y_plane.
  have hobtain3 := exists_goodLineFiber_of_innerBoundary hn hodd inner y_plane
  obtain ⟨z₂, w₂, hz₂, hw₂, ωU₂, θU₂, hωU₂, hdωU₂, hθU₂, hdθU₂, hF₂⟩ := hobtain3
  have inner₂ : InnerBoundary n trivialCharacter .line
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₂) := by
    rw [hz₂]; exact inner
  have hxpar₂ : bridgeX hn 0 (phiTwist_trivial n) hF₂ ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) 0) :=
    bridgeX_mem_parabolicCocycles_of_innerBoundary hn inner z₂ hz₂ hF₂
  let Xp₂ : parabolicH1 (arithmeticBinaryRep (n + 1) 0) :=
    ⟨projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF₂),
      Submodule.mem_map_of_mem hxpar₂⟩
  have hbridgeval₀ := projectH1_bridgeX_eq_neg_phiL_of_mem_ML hn z₀
    (cuspRes_mem_ML_of_innerBoundary inner₀) hF₀ (fun _ => rfl)
  have hbridgeval₂ := projectH1_bridgeX_eq_neg_phiL_of_mem_ML hn z₂
    (cuspRes_mem_ML_of_innerBoundary inner₂) hF₂ (fun _ => rfl)
  have hval_eq : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀) =
      cuspRes n trivialCharacter .line true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₂) := by
    rw [hz₀, hz₂]
  have hXeq : Xp₀ = Xp₂ := by
    apply Subtype.ext
    calc (Xp₀ : groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0)) =
          -phiL n hn ⟨cuspRes n trivialCharacter .line true
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀),
            cuspRes_mem_ML_of_innerBoundary inner₀⟩ := hbridgeval₀
      _ = -phiL n hn ⟨cuspRes n trivialCharacter .line true
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₂),
            cuspRes_mem_ML_of_innerBoundary inner₂⟩ :=
        congrArg Neg.neg (congrArg (phiL n hn) (Subtype.ext hval_eq))
      _ = (Xp₂ : groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0)) := hbridgeval₂.symm
  have hcl'2 : parabolicPairing (twistedPairing_goodLine_trivial hodd) Xp₂ cl' ≠ 0 := hXeq ▸ hcl'ne
  -- Step 5: the plane-side bridge membership for hF₂, and its identification with cl'.
  have hgood_plane' : VanishesOnGood n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
        y_plane) := by
    rw [hy_plane]; exact hgood_plane
  have hinner_plane' : InnerBoundary n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
        y_plane) := by
    rw [hy_plane]; exact ⟨y_plane, hy_plane, u_plane, hu_plane⟩
  have hx'par : bridgeX' (-1) (psiTwist_trivial hodd) hF₂ ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) (-1)) :=
    bridgeX'_mem_parabolicCocycles_of_innerBoundary hn hodd y_plane hgood_plane' hinner_plane'
      hF₂ (fun _ => rfl)
  let X'p₂ : parabolicH1 (arithmeticBinaryRep (n + 1) (-1)) :=
    ⟨projectH1 (arithmeticBinaryRep (n + 1) (-1)) (bridgeX' (-1) (psiTwist_trivial hodd) hF₂),
      Submodule.mem_map_of_mem hx'par⟩
  have hbridge2' : projectH1 (arithmeticBinaryRep (n + 1) (-1))
      (bridgeX' (-1) (psiTwist_trivial hodd) hF₂) = -cl'.1 := by
    rw [projectH1_bridgeX'_eq_neg_edge hn hodd hF₂ y_plane (fun _ => rfl), hy_plane, hb_edge]
  have hX'p2eq : X'p₂ = -cl' := Subtype.ext hbridge2'
  have hfinal : parabolicPairing (twistedPairing_goodLine_trivial hodd) Xp₂ X'p₂ ≠ 0 := by
    rw [hX'p2eq, map_neg]
    exact neg_ne_zero.mpr hcl'2
  -- Step 6: the lineValue sum is nonzero, and assemble.
  have hfact : (-(-((n + 1).factorial : ℂ))) ≠ 0 := by
    rw [neg_neg]
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))
  have hval1 : lineValue traceDataL2 (dualityData n trivialCharacter) 1 z₂ w₂ y_plane ≠ 0 := by
    rw [lineValue_goodLine_eq_of_innerBoundary hn hodd inner z₂ w₂ hz₂ hw₂ y_plane ωU₂ θU₂
      hωU₂ hdωU₂ hθU₂ hdθU₂ (hx'par := hx'par)]
    exact mul_ne_zero hfact hfinal
  have hval0 : lineValue traceDataL2 (dualityData n trivialCharacter) 0 z₂ w₂ y_plane = 0 :=
    lineValue_zero_eq_zero_of_cuspRes_true n trivialCharacter z₂ w₂ hw₂ y_plane (by
      rw [hy_plane]; exact hb_good0)
  have hsum : ∑ v : Fin 2,
      lineValue traceDataL2 (dualityData n trivialCharacter) v z₂ w₂ y_plane ≠ 0 := by
    rw [Fin.sum_univ_two, hval0]
    simpa using hval1
  exact face_pairing_perfect_of_anchor z₂ hz₂ w₂ hw₂ y_plane hy_plane
    ⟨u_plane, fun x e => hu_plane x e⟩ hsum

end TernaryPeriodPolynomials.Argument.FacePairing
