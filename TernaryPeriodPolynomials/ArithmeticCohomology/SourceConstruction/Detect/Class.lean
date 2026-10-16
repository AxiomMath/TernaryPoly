module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Edge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.ParityBoundary

@[expose] public section


/-!
# The class of a cocycle representing a cup product

Under the Kostant law the binary edge cocycle of a cocycle `Z` representing the cup product of the
potentials of `D` is `c • φ`, where `φ` is any one-cocycle of `GL₂(ℤ)` with values
`φ m = a (s m) - a 1` (`PlaneCupData.edgeCycle_eq`); so the edge of the class of `Z` is `c • [φ]`
(`PlaneCupData.planeCup_edge`).  If `c ≠ 0` and `[φ] ≠ 0` in
`H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) (-1))` then `Z` is not a coboundary of the identity-plane
stabilizer (`PlaneCupData.planeCup_not_coboundary`), and when `φ` is cohomologous to the classical
Eichler cocycle of a nonzero Hecke eigenform of weight `n + 3` this is the classical nonvanishing
theorem (`PlaneCupData.planeCup_not_coboundary_of_classical`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

theorem neg_one_zpow_neg_one_eq : (-1 : ℂ) ^ (-1 : ℤ) = (-1 : ℂ) ^ (1 : Fin 2).val := by
  norm_num

namespace PlaneCupData

variable {n : ℕ} (D : PlaneCupData n)
  {Z : cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
    (rationalCoefficientComponent n trivialCharacter)}

/-- The binary edge cocycle of a cocycle representing the cup product. -/
theorem edgeCycle_eq (hZ : D.Represents Z) {c : ℂ} (hK : KostantLaw n D.lam c)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhi n φ m = D.a (identityPlaneLeviSection m).val - D.a 1) :
    identityPlaneBinaryEdgeCycle n (D.planeCupRelative hZ) = c • φ := by
  apply groupCohomology.cocycles₁_ext
  intro m
  apply Subtype.ext
  refine (D.edgeCycle_value hZ hK m).trans ?_
  exact congrArg (fun w : PlaneQ n => c • w.val) (hφ m).symm

theorem edge_eq_H1 (hZ : D.Represents Z) (pos : 0 < n) (odd : Odd n) :
    identityPlaneAmbientBinaryEdge n pos odd trivialCharacter rfl Z =
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1))
        (identityPlaneBinaryEdgeCycle n (D.planeCupRelative hZ)) :=
  (identityPlaneAmbientBinaryEdge_apply n pos odd Z).trans
    (identityPlaneFullBinaryEdge_relative n pos odd (D.planeCupRelative hZ))

/-- **The edge of the class of `Z` is `c` times the class of the Levi cocycle.** -/
theorem planeCup_edge (hZ : D.Represents Z) {c : ℂ} (hK : KostantLaw n D.lam c)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhi n φ m = D.a (identityPlaneLeviSection m).val - D.a 1)
    (pos : 0 < n) (odd : Odd n) :
    identityPlaneAmbientBinaryEdge n pos odd trivialCharacter rfl Z =
      c • groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ := by
  have hsmul : ∀ x : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)),
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) (c • x) =
        c • groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) x :=
    fun x => (groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1))).hom.map_smul c x
  rw [D.edge_eq_H1 hZ pos odd, D.edgeCycle_eq hZ hK φ hφ, hsmul]

theorem planeCup_edge_ne_zero (hZ : D.Represents Z) {c : ℂ} (hK : KostantLaw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhi n φ m = D.a (identityPlaneLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0)
    (pos : 0 < n) (odd : Odd n) :
    identityPlaneAmbientBinaryEdge n pos odd trivialCharacter rfl Z ≠ 0 := by
  rw [D.planeCup_edge hZ hK φ hφ pos odd]
  exact smul_ne_zero hc hφ0

/-- **A cocycle representing the cup product is not a coboundary.** -/
theorem planeCup_not_coboundary (hZ : D.Represents Z) {c : ℂ} (hK : KostantLaw n D.lam c)
    (hc : c ≠ 0) (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhi n φ m = D.a (identityPlaneLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0)
    (pos : 0 < n) (odd : Odd n) :
    ¬ ∃ primitive : cochains
        (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n trivialCharacter) 1,
      differentialOne (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n trivialCharacter) primitive = Z.val := by
  intro h
  exact D.planeCup_edge_ne_zero hZ hK hc φ hφ hφ0 pos odd
    ((identityPlaneAmbientBinaryEdge_zero_iff n pos odd trivialCharacter rfl Z).mpr h)

/-- **Nonvanishing from the classical Eichler cocycle.**  If the Levi cocycle is cohomologous to the
classical period cocycle of a nonzero Hecke eigenform of weight `n + 3`, `Z` is not a coboundary. -/
theorem planeCup_not_coboundary_of_classical (hZ : D.Represents Z) {c : ℂ}
    (hK : KostantLaw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhi n φ m = D.a (identityPlaneLeviSection m).val - D.a 1)
    {weight : ℤ}
    (form : CuspForm (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (weight_eq : weight = ((n + 1 : ℕ) : ℤ) + 2) (even : Even (n + 1))
    (hcl : groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ =
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1))
        (classicalArithmeticCocycle form (n + 1) weight_eq even (-1) (1 : Fin 2).val
          neg_one_zpow_neg_one_eq))
    (pos : 0 < n) (odd : Odd n) :
    ¬ ∃ primitive : cochains
        (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n trivialCharacter) 1,
      differentialOne (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n trivialCharacter) primitive = Z.val := by
  refine D.planeCup_not_coboundary hZ hK hc φ hφ ?_ pos odd
  rw [hcl]
  exact classicalArithmeticCocycle_H1_ne_zero form nonzero eigenvalues relations (n + 1)
    weight_eq even (-1) 1 neg_one_zpow_neg_one_eq

end PlaneCupData

end TernaryPeriodPolynomials.SourceConstruction
