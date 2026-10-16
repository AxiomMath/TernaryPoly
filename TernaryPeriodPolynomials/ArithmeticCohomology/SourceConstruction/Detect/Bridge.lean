module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Class
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Global

@[expose] public section


/-!
# From a cocycle representing a cup product to the identity-plane cusp coordinate

The Shapiro coordinate `cuspRes n χ .plane false` of a maximal-stratum plane class is the class of
the cocycle `fixedPointCycle ... z` of the stabilizer of the identity flag `QuotientGroup.mk 1`
(`cuspFlag .plane false`), and that stabilizer is literally
`flagArithmeticStabilizer .plane (mk 1)`.  So if the values of a stratum cocycle `z` at the identity
flag, on the vertex triples `(1, g, g h)`, are the cup product of the potentials of
`D : PlaneCupData n`, its identity-plane coordinate is nonzero as soon as the Levi cocycle has
nonzero class and the Kostant law holds with `c ≠ 0` (`cuspRes_plane_false_ne_zero`).  A source
evaluated in the sense of `Evaluates` whose values at the adelic argument `rationalGroup 1⁻¹` on
rational vertices are the cup cochain has this property
(`cuspRes_plane_false_ne_zero_of_evaluates`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (arithmeticBinaryRep identityPlaneLeviSection)

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

variable {n : ℕ}

/-- **The identity-plane Shapiro coordinate of a stratum class whose values at the identity flag
represent the cup product of the potentials of `D` is nonzero** when the Levi cocycle has nonzero
class and the Kostant law holds with `c ≠ 0`. -/
theorem cuspRes_plane_false_ne_zero (χ : RankOneCharacter) (hχ : χ = trivialCharacter)
    (D : PlaneCupData n) {c : ℂ} (hK : KostantLaw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhi n φ m = D.a (identityPlaneLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0)
    (pos : 0 < n) (odd : Odd n)
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane))
    (hz : ∀ g h : PlaneStab, z.val.val ![1, g.val, g.val * h.val] (QuotientGroup.mk 1) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1)) :
    cuspRes n χ .plane false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) .plane) z) ≠ 0 := by
  subst hχ
  rw [TernaryPeriodPolynomials.Separation.cuspRes_classOf]
  intro h0
  have hZ : D.Represents (fixedPointCycle rationalLevel
      (rationalCoefficientComponent n trivialCharacter) (cuspFlag .plane false) z) :=
    fun g h => hz g h
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp h0
  obtain ⟨primitive, hprim⟩ := hmem
  exact D.planeCup_not_coboundary hZ hK hc φ hφ hφ0 pos odd
    ⟨primitive, congrArg Subtype.val hprim⟩

/-- The same for a source evaluated at the identity flag in the sense of `Evaluates`: it suffices
that the source, at the adelic argument `rationalGroup 1⁻¹`, restricts on rational vertices to the
cup product of the potentials. -/
theorem cuspRes_plane_false_ne_zero_of_evaluates (E : InducingData n)
    (hχ : E.chi = trivialCharacter)
    (D : PlaneCupData n) {c : ℂ} (hK : KostantLaw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhi n φ m = D.a (identityPlaneLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0)
    (pos : 0 < n) (odd : Odd n)
    {source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n}
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n E.chi) .plane)}
    (hz : Evaluates E .plane source z)
    (hsource : ∀ x : Fin 3 → RationalGL3,
      source (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
          (rationalGroup (1 : RationalGL3)⁻¹) =
        (D.l (x 2) - D.l (x 1)) (D.a (x 1) - D.a (x 0))) :
    cuspRes n E.chi .plane false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n E.chi) .plane) z) ≠ 0 :=
  cuspRes_plane_false_ne_zero E.chi hχ D hK hc φ hφ hφ0 pos odd z
    (fun g h => (hz ![1, g.val, g.val * h.val] 1).trans (hsource ![1, g.val, g.val * h.val]))

end TernaryPeriodPolynomials.SourceConstruction
