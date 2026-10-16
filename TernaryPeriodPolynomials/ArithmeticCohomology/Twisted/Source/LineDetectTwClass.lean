module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.LineDetectTwEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineLocalOp
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Global

@[expose] public section


/-!
# The class of a cocycle representing a cup product at the good line

Good-line analogue of `DetectTwClass` for a rank-one character `χ` with `χ(-1_∞) = -1`.  Under the
Kostant law the twisted binary edge cocycle of a cocycle `Z` of the good-line stabilizer `Λ₁`
representing the cup product of the potentials of `D : LineCupDataTw n χ` is `c • φ`, where `φ` is any
one-cocycle of `GL₂(ℤ)` in `arithmeticBinaryRep (n + 1) (-1)` with values
`φ m = a (s m) - a 1` (`LineCupDataTw.edgeCycle_eqTw`); so the edge of the class of `Z` is
`c • [φ]` (`LineCupDataTw.lineCup_edgeTw`).  If `c ≠ 0` and `[φ] ≠ 0` then `Z` is not a coboundary of
`Λ₁` (`LineCupDataTw.lineCup_not_coboundaryTw`).

The Shapiro coordinate `cuspRes n χ .line true` is the fixed-point class at the reference flag of the
good-line cusp, while the edge lives on `Λ₁`, the stabilizer of the good line.  The transport
`stabilizerTransportH2` along `gammaL` intertwines the two (`transport_cuspRes_eq_fixedPointH2`), so
a stratum class whose values at the good line represent the cup product has nonzero coordinate
(`cuspRes_line_true_ne_zeroTw`, `cuspRes_line_true_ne_zero_of_evaluatesTw`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.TwistedSource

section Class

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Twisted
  (goodLineBinaryEdgeCycleT goodLineAmbientBinaryEdgeT goodLineAmbientBinaryEdgeT_apply
    goodLineAmbientBinaryEdgeT_zero_iff goodLineFullBinaryEdgeT_relative)

/-- The values of a one-cocycle of `GL₂(ℤ)` in the binary forms (twist `-1`), as a plain function with
values in `LineQTw n`. -/
def cocyclePhiLineTw (n : ℕ) (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) : LineQTw n := φ m

namespace LineCupDataTw

variable {n : ℕ} {χ : RankOneCharacter} (D : LineCupDataTw n χ)
  {Z : cocycles (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
    (rationalCoefficientComponent n χ)}

/-- The twisted binary edge cocycle of a cocycle representing the cup product. -/
theorem edgeCycle_eqTw (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (pos : 0 < n)
    (hZ : D.Represents Z) {c : ℂ} (hK : LowerKostant n D.lam c)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhiLineTw n φ m = D.a (goodLineLeviSection m).val - D.a 1) :
    goodLineBinaryEdgeCycleT n χ hχ pos (D.lineCupRelative hZ) = c • φ := by
  apply groupCohomology.cocycles₁_ext
  intro m
  apply Subtype.ext
  refine (D.edgeCycle_value hχ pos hZ hK m).trans ?_
  exact congrArg (fun w : LineQTw n => c • w.val) (hφ m).symm

theorem edge_eq_H1Tw (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (pos : 0 < n)
    (hZ : D.Represents Z) :
    goodLineAmbientBinaryEdgeT n χ hχ pos Z =
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1))
        (goodLineBinaryEdgeCycleT n χ hχ pos (D.lineCupRelative hZ)) :=
  (goodLineAmbientBinaryEdgeT_apply n χ hχ pos Z).trans
    (goodLineFullBinaryEdgeT_relative n χ hχ pos (D.lineCupRelative hZ))

/-- **The edge of the class of `Z` is `c` times the class of the Levi cocycle.** -/
theorem lineCup_edgeTw (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (pos : 0 < n)
    (hZ : D.Represents Z) {c : ℂ} (hK : LowerKostant n D.lam c)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhiLineTw n φ m = D.a (goodLineLeviSection m).val - D.a 1) :
    goodLineAmbientBinaryEdgeT n χ hχ pos Z =
      c • groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ := by
  have hsmul : ∀ x : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)),
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) (c • x) =
        c • groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) x :=
    fun x => (groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1))).hom.map_smul c x
  rw [D.edge_eq_H1Tw hχ pos hZ, D.edgeCycle_eqTw hχ pos hZ hK φ hφ, hsmul]

theorem lineCup_edge_ne_zeroTw (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (pos : 0 < n)
    (hZ : D.Represents Z) {c : ℂ} (hK : LowerKostant n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhiLineTw n φ m = D.a (goodLineLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0) :
    goodLineAmbientBinaryEdgeT n χ hχ pos Z ≠ 0 := by
  rw [D.lineCup_edgeTw hχ pos hZ hK φ hφ]
  exact smul_ne_zero hc hφ0

/-- **A cocycle representing the cup product is not a coboundary.** -/
theorem lineCup_not_coboundaryTw (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (pos : 0 < n)
    (hZ : D.Represents Z) {c : ℂ} (hK : LowerKostant n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhiLineTw n φ m = D.a (goodLineLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0) :
    ¬ ∃ primitive : cochains
        (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n χ) 1,
      differentialOne (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n χ) primitive = Z.val := by
  intro h
  exact D.lineCup_edge_ne_zeroTw hχ pos hZ hK hc φ hφ hφ0
    ((goodLineAmbientBinaryEdgeT_zero_iff n χ hχ pos Z).mpr h)

end LineCupDataTw

end Class

section Bridge

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.GoodLineLocalOp
open TernaryPeriodPolynomials.Spectral.LineCoordinates (Λ₁)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (arithmeticBinaryRep goodLineLeviSection rationalGoodLine)

variable {n : ℕ}

/-- **The transport of the good-line Shapiro coordinate to the stabilizer `Λ₁` of the good line is the
fixed-point class at the good line.**  The transport is the one `psiLT n χ` of `AxiomCodeTwisted`. -/
theorem transport_cuspRes_eq_fixedPointH2 (χ : RankOneCharacter) (a : StratumH2 n χ .line) :
    stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n χ) gammaL
        (cuspFlag .line true) (QuotientGroup.mk rationalGoodLine) gammaL_smul
        (cuspRes n χ .line true a) =
      fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
        (QuotientGroup.mk rationalGoodLine) a :=
  stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) gammaL
    (cuspFlag .line true) (QuotientGroup.mk rationalGoodLine) gammaL_smul a

/-- **A stratum class whose restriction to the good line is not a coboundary of `Λ₁` has nonzero
good-line Shapiro coordinate.** -/
theorem cuspRes_line_true_ne_zero_of_not_coboundaryTw (χ : RankOneCharacter)
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line))
    (hz : ¬ ∃ primitive : cochains Λ₁ (rationalCoefficientComponent n χ) 1,
      differentialOne Λ₁ (rationalCoefficientComponent n χ) primitive =
        (fixedPointCycle rationalLevel (rationalCoefficientComponent n χ)
          (QuotientGroup.mk rationalGoodLine) z).val) :
    cuspRes n χ .line true
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z) ≠ 0 := by
  intro h0
  have h1 := transport_cuspRes_eq_fixedPointH2 χ
    (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z)
  rw [h0, map_zero] at h1
  have h2 := h1.trans (fixedPointH2_classOf rationalLevel (rationalCoefficientComponent n χ)
    (QuotientGroup.mk rationalGoodLine) z)
  obtain ⟨primitive, hprim⟩ := (Submodule.Quotient.mk_eq_zero _).mp h2.symm
  exact hz ⟨primitive, congrArg Subtype.val hprim⟩

/-- **The good-line Shapiro coordinate of a stratum class whose values at the good line represent
the cup product of the potentials of `D` is nonzero** when the Levi cocycle has nonzero class in
`H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) (-1))` and the Kostant law holds with `c ≠ 0`. -/
theorem cuspRes_line_true_ne_zeroTw (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (D : LineCupDataTw n χ) {c : ℂ} (hK : LowerKostant n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhiLineTw n φ m = D.a (goodLineLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0)
    (pos : 0 < n)
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line))
    (hz : ∀ g h : LineStabTw, z.val.val ![1, g.val, g.val * h.val]
        (QuotientGroup.mk rationalGoodLine) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1)) :
    cuspRes n χ .line true
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z) ≠ 0 := by
  apply cuspRes_line_true_ne_zero_of_not_coboundaryTw
  have hZ : D.Represents (fixedPointCycle rationalLevel
      (rationalCoefficientComponent n χ) (QuotientGroup.mk rationalGoodLine) z) :=
    fun g h => hz g h
  exact D.lineCup_not_coboundaryTw hχ pos hZ hK hc φ hφ hφ0

/-- The same for a source evaluated in the sense of `Evaluates`: it suffices that the source, at the
adelic argument `rationalGroup rationalGoodLine⁻¹`, restricts on rational vertices to the cup product
of the potentials. -/
theorem cuspRes_line_true_ne_zero_of_evaluatesTw (E : InducingData n)
    (hχ : E.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (D : LineCupDataTw n E.chi) {c : ℂ} (hK : LowerKostant n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhiLineTw n φ m = D.a (goodLineLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0)
    (pos : 0 < n)
    {source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n}
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n E.chi) .line)}
    (hz : Evaluates E .line source z)
    (hsource : ∀ x : Fin 3 → RationalGL3,
      source (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
          (rationalGroup rationalGoodLine⁻¹) =
        (D.l (x 2) - D.l (x 1)) (D.a (x 1) - D.a (x 0))) :
    cuspRes n E.chi .line true
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n E.chi) .line) z) ≠ 0 :=
  cuspRes_line_true_ne_zeroTw E.chi hχ D hK hc φ hφ hφ0 pos z
    (fun g h => (hz ![1, g.val, g.val * h.val] rationalGoodLine).trans
      (hsource ![1, g.val, g.val * h.val]))

end Bridge

end TernaryPeriodPolynomials.TwistedSource
