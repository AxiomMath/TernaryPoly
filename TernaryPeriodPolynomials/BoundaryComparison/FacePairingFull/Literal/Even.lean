module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.EvenBadLineAnchor
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.Independence
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineVacuityEven
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.Dict

@[expose] public section


/-!
# Value formulas for arbitrary inner classes: even `n`

For every even `n > 0` and every pair of inner classes `b` (line), `ξ` (plane),
`⟨b, ξ⟩_Q = ((n+1)!/3) · badGoodPairingEven (badLineParabolic b) (goodPlaneParabolic ξ)`
(`facePairing_even_literal`): the local value at the bad line is the literal level-three parabolic pairing
of the cusp edge classes (`lineValue_zero_even`), and the good-line value vanishes because
the good-flag cusp residue of an inner line class is zero at even `n` (`lineValue_one_eq_zero_of_cuspRes_true`
and `cuspRes_line_true_eq_zero_of_even`). The value formulas of the library
(`LocalPairingCaseL0Even.lineValue_of_classes`) are applied to the fibre packages built from the
`InnerBoundary` witnesses (`exists_badLineFiber_of_innerBoundary`), and moved to arbitrary
representatives by the local independence of `lineValue` (`LocalIndependence`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (e₀ L₀ endpoint_line_e₀)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
open TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2 (goodFlag_L₁)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag cuspFlag_transporter)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers (stabilizerTransportH2_fixedPointH2)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossed)
open TernaryPeriodPolynomials.BoundaryDuality
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossedH1)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers (fixedPointH2 crossedBoundaries)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant (badX badX')
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even
  (badGoodPairingEven planeTransportH1 mkQ_badX'_eq_planeTransport lineValue_of_classes)
open TernaryPeriodPolynomials.Argument.FacePairing
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

section Generic

variable {n : ℕ} {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

theorem mkQ_badX_eq_badLineParabolic (hn : 0 < n)
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (b : innerClasses n .line)
    (z : MaximalCycles n trivialCharacter .line)
    (hζ : ∀ x, ζ x = z.val.val x L₀)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val)
    (hbin : InnerBoundary n trivialCharacter .line
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z)) :
    (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX hn hF) =
      ((badLineParabolic hn b : parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
        CrossedH1 (binaryArithmeticRepresentation n)) := by
  rw [mkQ_badX_eq_neg_badLineEdge_cusp hn hF z hζ, badLineParabolic_coe hn b _ hz hbin]

theorem mkQ_badX'_eq_goodPlaneParabolic (hn : 0 < n) (heven : Even n)
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (ξ : innerClasses n .plane)
    (y : MaximalCycles n trivialCharacter .plane)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane))
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val) :
    (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX' heven hF) =
      planeTransportH1 heven ((goodPlaneParabolic hn ξ :
        parabolicCrossedH1 (levelRep (n + 1) (-1))) : CrossedH1 (levelRep (n + 1) (-1))) := by
  rw [mkQ_badX'_eq_planeTransport heven hn hF y hη, goodPlaneParabolic_coe hn ξ _ hy]

theorem lineValue_zero_even_fiber (hn : 0 < n) (heven : Even n)
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (b : innerClasses n .line) (ξ : innerClasses n .plane)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane) (hw : EdgePrimitive z w)
    (hωU : ∀ γ ∈ latL0.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀)
    (hθU : ∀ γ ∈ latL0.sub, ∀ a b,
      θU ![γ * a, γ * b] =
        rationalCoefficientComponent n trivialCharacter ((dualityData n trivialCharacter).φ γ)
          (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
        (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₀))
    (hζ : ∀ x, ζ x = z.val.val x L₀)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane))
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val)
    (hbin : InnerBoundary n trivialCharacter .line
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z))
    (hxpar : badX hn hF ∈ parabolicCrossed (binaryArithmeticRepresentation n))
    (hx'par : badX' heven hF ∈ parabolicCrossed (binaryArithmeticRepresentation n)) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 0 z w y =
      (((n + 1).factorial : ℂ) / 3) *
        badGoodPairingEven heven (badLineParabolic hn b) (goodPlaneParabolic hn ξ) :=
  lineValue_of_classes heven hn hF z w y hw hωU hdωU hθU hdθU (badLineParabolic hn b)
    (goodPlaneParabolic hn ξ) hxpar hx'par (mkQ_badX_eq_badLineParabolic hn hF b z hζ hz hbin)
    (mkQ_badX'_eq_goodPlaneParabolic hn heven hF ξ y hη hy)

end Generic

theorem lineValue_zero_even {n : ℕ} (hn : 0 < n) (heven : Even n) (b : innerClasses n .line)
    (ξ : innerClasses n .plane) (z : MaximalCycles n trivialCharacter .line)
    (w : EdgeCochains n trivialCharacter 1) (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val)
    (hw : EdgePrimitive z w) (y : MaximalCycles n trivialCharacter .plane)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val)
    (flat : PlaneEdgeExact y) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 0 z w y =
      (((n + 1).factorial : ℂ) / 3) *
        badGoodPairingEven heven (badLineParabolic hn b) (goodPlaneParabolic hn ξ) := by
  have hbin : InnerBoundary n trivialCharacter .line b.val := b.property
  obtain ⟨z₂, w₂, hz₂, hw₂, ωU, θU, hωU, hdωU, hθU, hdθU, hF⟩ :=
    exists_badLineFiber_of_innerBoundary hn hbin y
  have hinner_y : InnerBoundary n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) := by
    rw [hy]; exact ξ.property
  have hinner_z : InnerBoundary n trivialCharacter .line
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₂) := by
    rw [hz₂]; exact hbin
  have hxpar := badX_mem_parabolicCrossed_of_innerBoundary hn hbin z₂ hz₂ w₂ hw₂ y ωU θU hωU hdωU
    hθU hdθU
  have hx'par := badX'_mem_parabolicCrossed_of_innerBoundary hn heven z₂ w₂ hw₂ y ωU θU hωU hdωU
    hθU hdθU hinner_y
  have hη' := hη_flag
    (η := fun x => y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      ((dualityData n trivialCharacter).dualFlag L₀)) y (fun _ => rfl)
  have h1 := lineValue_zero_even_fiber hn heven hF b ξ z₂ w₂ y hw₂ hωU hdωU hθU hdθU (fun _ => rfl)
    hη' hz₂ hy hinner_z hxpar hx'par
  have h2 := LocalIndependence.lineValue_eq_of_line_fixedPointH2_eq traceDataL2
    (dualityData n trivialCharacter) 0 hw hw₂ flat
    (congrArg (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (traceDataL2.lineRep 0)) (hz.trans hz₂.symm))
  exact h2.trans h1

theorem fixedPointH2_eq_zero_of_cuspRes_line {n : ℕ} {good : Bool} {F : Flags .line}
    (hF : ∃ γ : rationalLevel, γ.val • cuspFlag .line good = F)
    {a : StratumH2 n trivialCharacter .line} (ha : cuspRes n trivialCharacter .line good a = 0) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F a = 0 := by
  obtain ⟨γ, hγ⟩ := hF
  rw [← stabilizerTransportH2_fixedPointH2 rationalLevel
    (rationalCoefficientComponent n trivialCharacter) γ (cuspFlag .line good) F hγ a]
  change stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) γ
    (cuspFlag .line good) F hγ (cuspRes n trivialCharacter .line good a) = 0
  rw [ha, map_zero]

theorem lineValue_one_eq_zero_of_cuspRes_true {n : ℕ} (z : MaximalCycles n trivialCharacter .line)
    (w : EdgeCochains n trivialCharacter 1) (hw : EdgePrimitive z w)
    (y : MaximalCycles n trivialCharacter .plane) (flat : PlaneEdgeExact y)
    (hz : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) = 0) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y = 0 := by
  obtain ⟨γ, hγ⟩ := cuspFlag_transporter .line true (traceDataL2.lineRep 1)
    (iff_of_true goodFlag_L₁ rfl)
  have h0 := fixedPointH2_eq_zero_of_cuspRes_line ⟨γ, hγ⟩ hz
  obtain ⟨u, hu_eq, hu⟩ := LocalIndependence.exists_line_exact traceDataL2 1 z h0
  exact LocalIndependence.lineValue_eq_zero_of_line_exact traceDataL2
    (dualityData n trivialCharacter) 1 hw flat u hu_eq hu

theorem exists_line_reps {n : ℕ} (b : innerClasses n .line) :
    ∃ (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1),
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val ∧
      EdgePrimitive z w := by
  have h : InnerBoundary n trivialCharacter .line b.val := b.property
  obtain ⟨z, hz, w, hw⟩ := h
  exact ⟨z, w, hz, fun x e => hw x e⟩

theorem exists_plane_rep {n : ℕ} (ξ : innerClasses n .plane) :
    ∃ y : MaximalCycles n trivialCharacter .plane,
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val ∧
      PlaneEdgeExact y := by
  have h : InnerBoundary n trivialCharacter .plane ξ.val := ξ.property
  obtain ⟨y, hy, s, hs⟩ := h
  exact ⟨y, hy, s, fun x e => hs x e⟩

theorem facePairing_eq_lineValue_add {n : ℕ} (b : innerClasses n .line) (ξ : innerClasses n .plane)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val)
    (hw : EdgePrimitive z w)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val) :
    facePairing n b ξ =
      lineValue traceDataL2 (dualityData n trivialCharacter) 0 z w y +
        lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y :=
  (facePairing_apply_eq (b := b) (ξ := ξ) hz hw hy).trans (Fin.sum_univ_two _)

theorem facePairing_even_literal_of_reps {n : ℕ} (hn : 0 < n) (heven : Even n)
    (b : innerClasses n .line) (ξ : innerClasses n .plane)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val)
    (hw : EdgePrimitive z w)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val)
    (flat : PlaneEdgeExact y) :
    facePairing n b ξ = (((n + 1).factorial : ℂ) / 3) *
      badGoodPairingEven heven (badLineParabolic hn b) (goodPlaneParabolic hn ξ) := by
  have hbin : InnerBoundary n trivialCharacter .line b.val := b.property
  have h1 : lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y = 0 :=
    lineValue_one_eq_zero_of_cuspRes_true z w hw y flat (by
      rw [hz]; exact cuspRes_line_true_eq_zero_of_even hn heven hbin)
  exact (facePairing_eq_lineValue_add b ξ z w y hz hw hy).trans
    ((congrArg₂ (· + ·) (lineValue_zero_even hn heven b ξ z w hz hw y hy flat) h1).trans
      (add_zero _))

/-- **Even `n`: the cochain line pairing is the literal level-three pairing, up to the constant
`(n+1)!/3`.** For every pair of inner classes `b` (line) and `ξ` (plane) and every even `n > 0`,
`⟨b, ξ⟩_Q = ((n+1)!/3) · ⟨-badLineEdge(cuspRes_false b), goodPlaneEdge(cuspRes_true ξ)⟩_{Γ₁'(3)}`. -/
theorem facePairing_even_literal {n : ℕ} (hn : 0 < n) (heven : Even n) (b : innerClasses n .line)
    (ξ : innerClasses n .plane) :
    facePairing n b ξ = (((n + 1).factorial : ℂ) / 3) *
      badGoodPairingEven heven (badLineParabolic hn b) (goodPlaneParabolic hn ξ) :=
  (exists_line_reps b).elim fun _ h1 => h1.elim fun _ h2 =>
    (exists_plane_rep ξ).elim fun _ h3 =>
      facePairing_even_literal_of_reps hn heven b ξ _ _ _ h2.1 h2.2 h3.1 h3.2

end TernaryPeriodPolynomials.Argument.FacePairingFull.Literal
