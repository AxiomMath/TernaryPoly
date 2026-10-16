module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LineEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.ParityBoundary

@[expose] public section


/-!
# The class of a cocycle representing a cup product on the good line

Under the Kostant law the binary edge cocycle of a cocycle `Z` representing the cup product of the
potentials of `D` is `c • φ`, where `φ` is any one-cocycle of `GL₂(ℤ)` in
`arithmeticBinaryRep (n + 1) 0` with values `φ m = a (s m) - a 1` (`LineCupData.edgeCycle_eq`); so
the good-line Hochschild–Serre edge of the class of `Z` is `c • [φ]` (`LineCupData.lineCup_edge`).
The good-line edge is injective in every positive degree (`goodLineBinaryEdge_injective`), so if
`c ≠ 0` and `[φ] ≠ 0` in `H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) 0)` then `Z` is not a coboundary
of the good-line stabilizer (`LineCupData.lineCup_not_coboundary`); when `φ` is cohomologous to the
classical Eichler cocycle of a nonzero Hecke eigenform of weight `n + 3` this is the classical
nonvanishing theorem (`LineCupData.lineCup_not_coboundary_of_classical`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

theorem neg_one_zpow_zero_eq : (-1 : ℂ) ^ (0 : ℤ) = (-1 : ℂ) ^ (0 : Fin 2).val := by
  norm_num

/-- The vanishing of the class of the binary edge cocycle is the vanishing of the relative class,
in every positive degree. -/
theorem goodLineBinaryEdgeCycle_H1_zero_iff_of_pos (degree : ℕ) (positive : 0 < degree)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree)) :
    groupCohomology.H1π (arithmeticBinaryRep (degree + 1) 0)
        (goodLineBinaryEdgeCycle degree positive cycle) = 0 ↔
      groupCohomology.H2π (goodLineCoefficientRep degree) cycle.val = 0 := by
  rw [goodLineBinaryEdgeCycle_H1, LinearMap.map_eq_zero_iff _
    (TernaryPeriodPolynomials.Spectral.ModularH2.goodLineBinaryEdge_injective
      degree positive)]
  constructor
  · intro zero
    exact congrArg Subtype.val zero
  · intro zero
    exact Subtype.ext zero

theorem lineH1π_smul (n : ℕ) (c : ℂ)
    (x : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0)) :
    groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) (c • x) =
      c • groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) x :=
  (groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0)).hom.map_smul c x

namespace LineCupData

variable {n : ℕ} (D : LineCupData n)
  {Z : cocycles (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
    (rationalCoefficientComponent n trivialCharacter)}

/-- The binary edge cocycle of a cocycle representing the cup product. -/
theorem edgeCycle_eq (hZ : D.Represents Z) (pos : 0 < n) {c : ℂ} (hK : LineKostantLaw n D.lam c)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, lineCocyclePhi n φ m = D.a (goodLineLeviSection m).val - D.a 1) :
    goodLineBinaryEdgeCycle n pos (D.lineCupRelative hZ) = c • φ := by
  apply groupCohomology.cocycles₁_ext
  intro m
  refine (D.edgeCycle_value hZ pos hK m).trans ?_
  exact congrArg (fun w : LineQ n => c • w) (hφ m).symm

/-- **The good-line edge of the class of `Z` is `c` times the class of the Levi cocycle.** -/
theorem lineCup_edge (hZ : D.Represents Z) (pos : 0 < n) {c : ℂ} (hK : LineKostantLaw n D.lam c)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, lineCocyclePhi n φ m = D.a (goodLineLeviSection m).val - D.a 1) :
    goodLineBinaryEdge n pos
        (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n)
          (D.lineCupRelative hZ)) =
      c • groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ := by
  rw [← goodLineBinaryEdgeCycle_H1, D.edgeCycle_eq hZ pos hK φ hφ, lineH1π_smul]

theorem lineCup_edge_ne_zero (hZ : D.Represents Z) (pos : 0 < n) {c : ℂ}
    (hK : LineKostantLaw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, lineCocyclePhi n φ m = D.a (goodLineLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0) :
    goodLineBinaryEdge n pos
        (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n)
          (D.lineCupRelative hZ)) ≠ 0 := by
  rw [D.lineCup_edge hZ pos hK φ hφ]
  exact smul_ne_zero hc hφ0

/-- **A cocycle representing the cup product on the good line is not a coboundary.** -/
theorem lineCup_not_coboundary (hZ : D.Represents Z) (pos : 0 < n) {c : ℂ}
    (hK : LineKostantLaw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, lineCocyclePhi n φ m = D.a (goodLineLeviSection m).val - D.a 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0) :
    ¬ ∃ primitive : cochains
        (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n trivialCharacter) 1,
      differentialOne (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n trivialCharacter) primitive = Z.val := by
  rintro ⟨primitive, hprim⟩
  have hzero : groupCohomology.H2π (goodLineCoefficientRep n) (D.lineCupRelative hZ).val = 0 :=
    (ambientCocycle_H2_zero_iff
      (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent n trivialCharacter) Z).mpr ⟨primitive, hprim⟩
  have h1 := (goodLineBinaryEdgeCycle_H1_zero_iff_of_pos n pos (D.lineCupRelative hZ)).mpr hzero
  rw [D.edgeCycle_eq hZ pos hK φ hφ, lineH1π_smul] at h1
  exact smul_ne_zero hc hφ0 h1

/-- **Nonvanishing from the classical Eichler cocycle.**  If the Levi cocycle is cohomologous to the
classical period cocycle of a nonzero Hecke eigenform of weight `n + 3`, `Z` is not a coboundary. -/
theorem lineCup_not_coboundary_of_classical (hZ : D.Represents Z) (pos : 0 < n) {c : ℂ}
    (hK : LineKostantLaw n D.lam c) (hc : c ≠ 0)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, lineCocyclePhi n φ m = D.a (goodLineLeviSection m).val - D.a 1)
    {weight : ℤ}
    (form : CuspForm (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (weight_eq : weight = ((n + 1 : ℕ) : ℤ) + 2) (even : Even (n + 1))
    (hcl : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ =
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0)
        (classicalArithmeticCocycle form (n + 1) weight_eq even 0 (0 : Fin 2).val
          neg_one_zpow_zero_eq)) :
    ¬ ∃ primitive : cochains
        (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n trivialCharacter) 1,
      differentialOne (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n trivialCharacter) primitive = Z.val := by
  refine D.lineCup_not_coboundary hZ pos hK hc φ hφ ?_
  rw [hcl]
  exact classicalArithmeticCocycle_H1_ne_zero form nonzero eigenvalues relations (n + 1)
    weight_eq even 0 0 neg_one_zpow_zero_eq

end LineCupData

end TernaryPeriodPolynomials.SourceConstruction
