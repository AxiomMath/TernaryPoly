module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneHecke

@[expose] public section


/-!
# The exact bad-plane edge value of a cocycle representing a cup product

Bad-plane (level-one) analogue of
`Argument.GoodPlaneSpan.PlanePeriodExact.goodPlaneEdge_cuspRes_eq_period`, using
`DetectBridge.cuspRes_plane_false_ne_zero`'s proof pattern (`cuspRes_classOf`, `fixedPointCycle`,
`PlaneCupData.Represents`) together with `IdentityPlaneHecke.edgeH2_classOf` (an `rfl`) and
`DetectClass.PlaneCupData.planeCup_edge` (the exact edge-value identity, already proved) to
conclude an EXACT value, not just nonvanishing.

No conjugation step is needed here (unlike the good-plane case's `psiG`/`ΛG`), because the
bad/identity plane's reference flag is already `QuotientGroup.mk 1`
(`CuspOrbits.cuspFlag .plane false`), so `cuspLevel .plane false` is definitionally
`flagArithmeticStabilizer .plane (QuotientGroup.mk 1)`, which is literally `Λ₀`
(`PlaneCoordinates.Λ₀`); `edgeH2`'s domain `H2 Λ₀ (ρn n)` is thus the same local cohomology group
as `CuspH2 n trivialCharacter .plane false`, and `edgeH2_classOf`'s `rfl` connects `edgeH2` to
`identityPlaneAmbientBinaryEdge` on the nose.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (arithmeticBinaryRep identityPlaneLeviSection)

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

variable {n : ℕ}

/-- **The exact bad-plane edge value of a stratum class represented by a cup product.** If the
values of a stratum cocycle `z` at the identity flag, on the vertex triples `(1, g, g h)`, are the
cup product of the potentials of `D : PlaneCupData n` (`hz`, matching `D.Represents`), and the
Kostant law holds for `D.lam` with constant `c`, then `edgeH2` of the bad-plane Shapiro coordinate
of `z`'s class is exactly `c • H1π φ`, for any `φ` whose `cocyclePhi` matches `D`'s Levi potential
difference. -/
theorem edgeH2_cuspRes_plane_false_eq
    (D : PlaneCupData n) {c : ℂ} (hK : KostantLaw n D.lam c)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhi n φ m = D.a (identityPlaneLeviSection m).val - D.a 1)
    (pos : 0 < n) (odd : Odd n)
    (z : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hz : ∀ g h : PlaneStab, z.val.val ![1, g.val, g.val * h.val] (QuotientGroup.mk 1) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1)) :
    edgeH2 n pos odd
      (cuspRes n trivialCharacter .plane false
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z)) =
      c • groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ := by
  rw [TernaryPeriodPolynomials.Separation.cuspRes_classOf]
  have hZ : D.Represents (fixedPointCycle rationalLevel
      (rationalCoefficientComponent n trivialCharacter) (cuspFlag .plane false) z) :=
    fun g h => hz g h
  exact D.planeCup_edge hZ hK φ hφ pos odd

end TernaryPeriodPolynomials.Argument.CuspidalSpan
