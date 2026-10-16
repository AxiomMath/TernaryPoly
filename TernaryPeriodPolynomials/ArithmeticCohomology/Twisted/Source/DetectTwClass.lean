module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.DetectTwEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Global

@[expose] public section


/-!
# The class of a cocycle representing a cup product, for the odd character

Port of `SourceConstruction.DetectClass` and `DetectBridge` to a rank-one character `χ`
with `χ(-1_∞) = -1`.  Under the Kostant law the twisted binary edge cocycle of a cocycle `Z`
representing the cup product of the potentials of `D : PlaneCupDataTw n χ` is `c • φ`, where `φ` is
any one-cocycle of `GL₂(ℤ)` in `arithmeticBinaryRep (n + 1) 0` with values `φ m = a (s m) - a 1`
(`PlaneCupDataTw.edgeCycle_eqTw`); so the edge of the class of `Z` is `c • [φ]`
(`PlaneCupDataTw.planeCup_edgeTw`).  If `c ≠ 0` and `[φ] ≠ 0` then `Z` is not a coboundary of the
identity-plane stabilizer (`PlaneCupDataTw.planeCup_not_coboundaryTw`), and the identity-plane
Shapiro coordinate `cuspRes n χ .plane false` of a stratum class whose values at the identity flag
represent the cup product is nonzero (`cuspRes_plane_false_ne_zeroTw`,
`cuspRes_plane_false_ne_zero_of_evaluatesTw`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.TwistedSource

section Class

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SourceConstruction (PlaneQ)
open TernaryPeriodPolynomials.Twisted
  (identityPlaneBinaryEdgeCycleT identityPlaneAmbientBinaryEdgeT identityPlaneAmbientBinaryEdgeT_apply
    identityPlaneAmbientBinaryEdgeT_zero_iff identityPlaneFullBinaryEdgeT_relative)

/-- The values of a one-cocycle of `GL₂(ℤ)` in the binary forms (twist `0`), as a plain function with
values in `Q`. -/
def cocyclePhiTw (n : ℕ) (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) : PlaneQ n := φ m

namespace PlaneCupDataTw

variable {n : ℕ} {χ : RankOneCharacter} (D : PlaneCupDataTw n χ)
  {Z : cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
    (rationalCoefficientComponent n χ)}

/-- The twisted binary edge cocycle of a cocycle representing the cup product. -/
theorem edgeCycle_eqTw (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hZ : D.Represents Z)
    {c : ℂ} (hK : KostantLawTw n D.lam c)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, cocyclePhiTw n φ m = D.a (identityPlaneLeviSection m).val - D.a 1) :
    identityPlaneBinaryEdgeCycleT n χ hχ (D.planeCupRelative hZ) = c • φ := by
  apply groupCohomology.cocycles₁_ext
  intro m
  apply Subtype.ext
  refine (D.edgeCycle_value hχ hZ hK m).trans ?_
  exact congrArg (fun w : PlaneQ n => c • w.val) (hφ m).symm

theorem edge_eq_H1Tw (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hZ : D.Represents Z)
    (pos : 0 < n) (odd : Odd n) :
    identityPlaneAmbientBinaryEdgeT n χ hχ pos odd Z =
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0)
        (identityPlaneBinaryEdgeCycleT n χ hχ (D.planeCupRelative hZ)) :=
  (identityPlaneAmbientBinaryEdgeT_apply n χ hχ pos odd Z).trans
    (identityPlaneFullBinaryEdgeT_relative n χ hχ pos odd (D.planeCupRelative hZ))

/-- **The edge of the class of `Z` is `c` times the class of the Levi cocycle.** -/
theorem planeCup_edgeTw (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hZ : D.Represents Z)
    {c : ℂ} (hK : KostantLawTw n D.lam c)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, cocyclePhiTw n φ m = D.a (identityPlaneLeviSection m).val - D.a 1)
    (pos : 0 < n) (odd : Odd n) :
    identityPlaneAmbientBinaryEdgeT n χ hχ pos odd Z =
      c • groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ := by
  have hsmul : ∀ x : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0),
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) (c • x) =
        c • groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) x :=
    fun x => (groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0)).hom.map_smul c x
  rw [D.edge_eq_H1Tw hχ hZ pos odd, D.edgeCycle_eqTw hχ hZ hK φ hφ, hsmul]

theorem planeCup_edge_ne_zeroTw (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hZ : D.Represents Z) {c : ℂ} (hK : KostantLawTw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, cocyclePhiTw n φ m = D.a (identityPlaneLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0)
    (pos : 0 < n) (odd : Odd n) :
    identityPlaneAmbientBinaryEdgeT n χ hχ pos odd Z ≠ 0 := by
  rw [D.planeCup_edgeTw hχ hZ hK φ hφ pos odd]
  exact smul_ne_zero hc hφ0

/-- **A cocycle representing the cup product is not a coboundary.** -/
theorem planeCup_not_coboundaryTw (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hZ : D.Represents Z) {c : ℂ} (hK : KostantLawTw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, cocyclePhiTw n φ m = D.a (identityPlaneLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0)
    (pos : 0 < n) (odd : Odd n) :
    ¬ ∃ primitive : cochains
        (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n χ) 1,
      differentialOne (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n χ) primitive = Z.val := by
  intro h
  exact D.planeCup_edge_ne_zeroTw hχ hZ hK hc φ hφ hφ0 pos odd
    ((identityPlaneAmbientBinaryEdgeT_zero_iff n χ hχ pos odd Z).mpr h)

end PlaneCupDataTw

end Class

section Bridge

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (arithmeticBinaryRep identityPlaneLeviSection)
open TernaryPeriodPolynomials.SourceConstruction (PlaneStab)

variable {n : ℕ}

/-- **The identity-plane Shapiro coordinate of a stratum class whose values at the identity flag
represent the cup product of the potentials of `D` is nonzero** when the Levi cocycle has nonzero
class in `H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) 0)` and the Kostant law holds with `c ≠ 0`. -/
theorem cuspRes_plane_false_ne_zeroTw (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (D : PlaneCupDataTw n χ) {c : ℂ} (hK : KostantLawTw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, cocyclePhiTw n φ m = D.a (identityPlaneLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0)
    (pos : 0 < n) (odd : Odd n)
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane))
    (hz : ∀ g h : PlaneStab, z.val.val ![1, g.val, g.val * h.val] (QuotientGroup.mk 1) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1)) :
    cuspRes n χ .plane false
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) z) ≠ 0 := by
  rw [TernaryPeriodPolynomials.Separation.cuspRes_classOf]
  intro h0
  have hZ : D.Represents (fixedPointCycle rationalLevel
      (rationalCoefficientComponent n χ) (cuspFlag .plane false) z) :=
    fun g h => hz g h
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp h0
  obtain ⟨primitive, hprim⟩ := hmem
  exact D.planeCup_not_coboundaryTw hχ hZ hK hc φ hφ hφ0 pos odd
    ⟨primitive, congrArg Subtype.val hprim⟩

/-- The same for a source evaluated at the identity flag in the sense of `Evaluates`: it suffices that
the source, at the adelic argument `rationalGroup 1⁻¹`, restricts on rational vertices to the cup
product of the potentials. -/
theorem cuspRes_plane_false_ne_zero_of_evaluatesTw (E : InducingData n)
    (hχ : E.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (D : PlaneCupDataTw n E.chi) {c : ℂ} (hK : KostantLawTw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, cocyclePhiTw n φ m = D.a (identityPlaneLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0)
    (pos : 0 < n) (odd : Odd n)
    {source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n}
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n E.chi) .plane)}
    (hz : Evaluates E .plane source z)
    (hsource : ∀ x : Fin 3 → RationalGL3,
      source (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
          (rationalGroup (1 : RationalGL3)⁻¹) =
        (D.l (x 2) - D.l (x 1)) (D.a (x 1) - D.a (x 0))) :
    cuspRes n E.chi .plane false
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n E.chi) .plane) z) ≠ 0 :=
  cuspRes_plane_false_ne_zeroTw E.chi hχ D hK hc φ hφ hφ0 pos odd z
    (fun g h => (hz ![1, g.val, g.val * h.val] 1).trans (hsource ![1, g.val, g.val * h.val]))

end Bridge

end TernaryPeriodPolynomials.TwistedSource
