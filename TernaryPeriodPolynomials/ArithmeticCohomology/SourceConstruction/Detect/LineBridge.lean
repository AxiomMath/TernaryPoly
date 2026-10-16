module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LineClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Global
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.Line

@[expose] public section


/-!
# From a cocycle representing a cup product to the good-line cusp coordinate

The Shapiro coordinate `cuspRes n χ .line true` of a maximal-stratum line class is the class of the
cocycle `fixedPointCycle ... z` of the stabilizer of the reference good-line flag
`cuspFlag .line true = mk (rational referenceIntegral)`.  That stabilizer is conjugate, by a
transporter `γ` of the arithmetic level group with `γ • cuspFlag .line true = mk rationalGoodLine`,
to the stabilizer `Γ_L = flagArithmeticStabilizer .line (mk rationalGoodLine)` of the good line
`⟨e₃⟩` on which the Hochschild–Serre edge `goodLineBinaryEdge` lives, and the transport commutes
with the Shapiro coordinates (`stabilizerTransportH2_fixedPointH2`): the class of `z` at the flag
`mk rationalGoodLine` is the transport of the class at the reference flag.  So if the values of a
stratum cocycle `z` at the flag `mk rationalGoodLine`, on the vertex triples `(1, g, g h)`, are the
cup product of the potentials of `D : LineCupData n`, its good-line coordinate is nonzero as soon as
the Levi cocycle has nonzero class in `H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) 0)` and the Kostant
law holds with `c ≠ 0` (`cuspRes_line_true_ne_zero`).  A source evaluated in the sense of
`Evaluates` whose values at the adelic argument `rationalGroup rationalGoodLine⁻¹` on rational
vertices are the cup cochain has this property (`cuspRes_line_true_ne_zero_of_evaluates`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (arithmeticBinaryRep goodLineLeviSection rationalGoodLine rationalGoodLine_good)

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

variable {n : ℕ}

/-- A transporter of the level group from the reference good-line flag to the good line `⟨e₃⟩`. -/
theorem lineTransporter :
    ∃ γ : rationalLevel, γ.val • cuspFlag .line true =
      (QuotientGroup.mk rationalGoodLine : Flags .line) :=
  cuspFlag_transporter .line true _ ⟨fun _ => rfl, fun _ => rationalGoodLine_good⟩

/-- **The good-line Shapiro coordinate of a stratum class whose values at the flag
`mk rationalGoodLine` represent the cup product of the potentials of `D` is nonzero** when the Levi
cocycle has nonzero class and the Kostant law holds with `c ≠ 0`. -/
theorem cuspRes_line_true_ne_zero (χ : RankOneCharacter) (hχ : χ = trivialCharacter)
    (D : LineCupData n) {c : ℂ} (hK : LineKostantLaw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, lineCocyclePhi n φ m = D.a (goodLineLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0) (pos : 0 < n)
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line))
    (hz : ∀ g h : LineStab,
      z.val.val ![1, g.val, g.val * h.val] (QuotientGroup.mk rationalGoodLine) =
        (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1)) :
    cuspRes n χ .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) .line) z) ≠ 0 := by
  subst hχ
  obtain ⟨γ, hγ⟩ := lineTransporter
  intro h0
  have h1 := stabilizerTransportH2_fixedPointH2 rationalLevel
    (rationalCoefficientComponent n trivialCharacter) γ (cuspFlag .line true)
    (QuotientGroup.mk rationalGoodLine) hγ
    (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z)
  have h2 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (QuotientGroup.mk rationalGoodLine : Flags .line)
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) = 0 := by
    rw [← h1]
    have h3 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (cuspFlag .line true)
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) = 0 := h0
    rw [h3, map_zero]
  have h4 : classOf
      (fixedPointLevel rationalLevel (QuotientGroup.mk rationalGoodLine : Flags .line))
      (rationalCoefficientComponent n trivialCharacter)
      (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (QuotientGroup.mk rationalGoodLine : Flags .line) z) = 0 := h2
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp h4
  obtain ⟨primitive, hprim⟩ := hmem
  have hZ : D.Represents (fixedPointCycle rationalLevel
      (rationalCoefficientComponent n trivialCharacter)
      (QuotientGroup.mk rationalGoodLine : Flags .line) z) :=
    fun g h => hz g h
  exact D.lineCup_not_coboundary hZ pos hK hc φ hφ hφ0 ⟨primitive, congrArg Subtype.val hprim⟩

/-- The same for a source evaluated at the good-line reflection in the sense of `Evaluates`: it
suffices that the source, at the adelic argument `rationalGroup rationalGoodLine⁻¹`, restricts on
rational vertices to the cup product of the potentials. -/
theorem cuspRes_line_true_ne_zero_of_evaluates (E : InducingData n)
    (hχ : E.chi = trivialCharacter)
    (D : LineCupData n) {c : ℂ} (hK : LineKostantLaw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, lineCocyclePhi n φ m = D.a (goodLineLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0) (pos : 0 < n)
    {source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n}
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n E.chi) .line)}
    (hz : Evaluates E .line source z)
    (hsource : ∀ x : Fin 3 → RationalGL3,
      source (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
          (rationalGroup (rationalGoodLine : RationalGL3)⁻¹) =
        (D.l (x 2) - D.l (x 1)) (D.a (x 1) - D.a (x 0))) :
    cuspRes n E.chi .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n E.chi) .line) z) ≠ 0 :=
  cuspRes_line_true_ne_zero E.chi hχ D hK hc φ hφ hφ0 pos z
    (fun g h => (hz ![1, g.val, g.val * h.val] rationalGoodLine).trans
      (hsource ![1, g.val, g.val * h.val]))

end TernaryPeriodPolynomials.SourceConstruction
