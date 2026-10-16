module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFrobeniusL2
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeLiftFormula
public import TernaryPeriodPolynomials.SymmetricSolution.FiniteDifference.SymbolClass

@[expose] public section

/-!
# B1: assembly and Hecke equivariance of the binary duality

Formalized by Claude Sonnet 5.5.

* `bridge_of_L4 p d : L4 p → HomologyHomBridge p d (p^(d+1))`: `bridge_of_interfaces` with `L1_holds` (`BridgeFrobeniusData`),
  `L2_holds` (`BridgeFrobeniusL2`), `L3_holds` (`BridgeLift`) and `L5_holds` (`BridgeLiftFormula`) filled in; `L4` (the transposed dual
  lift covers the identity) is the only hypothesis.
* `hecke2_symbolClass`: granting `HomologyHomBridge p d c`, the homology operator `T₂(p)` is, under the binary duality
  `symbolClass d : PeriodHom d ≃ H₁(GL₂(ℤ), Sym^d)` (`LemmaB1Period.SymbolClass`), the Hom operator `c · T_{diag(p,1)}`:
  `T₂(p)(symbolClass Φ) = symbolClass(c · rationalHecke (diag(p,1)) (ρ_{-1}) Φ)`.
* `hecke2_symbolClass_C1`: with `L4`, `T₂(p)(symbolClass Φ) = symbolClass(p⁻¹ · rationalHecke (C1 p) ρ_{-1} Φ)`, `C1 = diag(1/p, 1)`
  (`BridgeHom.hecke_C1_neg`): the Hecke equivariance of the Farey-edge duality `H₁(Γ, Sym^d) ≃ Hom_Γ(St^δ, Sym^d)` for the
  correspondence of `C1`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

open TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeHomology
open TernaryPeriodPolynomials.Argument.LemmaB1Period
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface

section Assembly

variable (p d : ℕ) [Fact p.Prime]

/-- **B1 from the single remaining interface `L4`**: `L1`, `L2`, `L3`, `L5` are proved. -/
theorem bridge_of_L4 (h4 : L4 p) : HomologyHomBridge p d ((p : ℚ) ^ (d + 1)) :=
  bridge_of_interfaces p d (L1_holds d) (L2_holds p) (L3_holds p) h4 (L5_holds p d)

end Assembly

section SymbolHecke

variable {p d : ℕ} [Fact p.Prime]

/-- **Hecke equivariance of the binary duality** (R4 `R3`), granting the bridge `homologyT2 = c · periodHecke`: for a
period Hom `Φ ∈ Hom_Γ(St, Sym^d)` (exponent `-1`, i.e. `Hom_Γ(St^δ, Sym^d)` for the plain action),
`T₂(p) (symbolClass Φ) = symbolClass (c · T_{diag(p,1)}^{(-1)} Φ)`. -/
theorem hecke2_symbolClass {c : ℚ} (h : HomologyHomBridge p d c) (Φ : PeriodHom d) :
    hecke2 p d (symbolClass d Φ) = symbolClass d (c • BinaryRationalHecke.rationalHecke
      (BinaryRationalHeckePrime.primeDiagonal p) (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) Φ) := by
  apply (periodEquivHomology d).injective
  have e1 : periodEquivHomology d (symbolClass d Φ) = periodEquiv d Φ := periodEquivHomology_symbolClass d Φ
  have e2 : periodEquivHomology d (hecke2 p d (symbolClass d Φ)) = homologyT2 p d (periodEquiv d Φ) := by
    unfold homologyT2
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← e1]
    simp
  rw [e2, h, LinearMap.smul_apply]
  have e3 : periodEquivHomology d (symbolClass d (c • BinaryRationalHecke.rationalHecke
      (BinaryRationalHeckePrime.primeDiagonal p)
      (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) Φ)) =
      periodEquiv d (c • BinaryRationalHecke.rationalHecke (BinaryRationalHeckePrime.primeDiagonal p)
        (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) Φ) :=
    periodEquivHomology_symbolClass d _
  rw [e3, map_smul, ← BinaryRationalHecke.periodHecke_evaluation]

/-- **B1 in symbol form, with `C1 = diag(1/p, 1)`**: `T₂(p)(class Φ) = class(p⁻¹ · T^{(-1)}[C1] Φ)`. -/
theorem hecke2_symbolClass_C1 (h4 : L4 p) (Φ : PeriodHom d) :
    hecke2 p d (symbolClass d Φ) = symbolClass d ((p : ℚ)⁻¹ • BinaryRationalHecke.rationalHecke
      (HeckeHomology.C1 p) (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) Φ) := by
  rw [hecke2_symbolClass (bridge_of_L4 p d h4)]
  congr 1
  apply Subtype.ext
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [Submodule.coe_smul, Submodule.coe_smul, BridgeHom.hecke_C1_neg, smul_smul]
  congr 1
  field_simp
  ring

end SymbolHecke

end TernaryPeriodPolynomials.Argument.HeckeNormalization
