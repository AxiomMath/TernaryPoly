module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeSymbolHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFinal

@[expose] public section


/-!
# Hecke equivariance of the binary duality, unconditionally

Formalized by Claude Sonnet 5.5.

`BridgeSymbolHecke.hecke2_symbolClass` / `hecke2_symbolClass_C1` with the bridge `homologyHomBridge_holds` and `BridgeDegreeCount.L4_holds`
filled in: the homology operator `T₂(p)` on `H₁(GL₂(ℤ), Sym^d)` is, under the Farey-edge duality `symbolClass d : PeriodHom d ≃ H₁`, the
Hom operator `p^{d+1} · T_{diag(p,1)} = p⁻¹ · T[C1]` (exponent `-1`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

open TernaryPoly TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.HeckeHomology TernaryPeriodPolynomials.Argument.LemmaB1Period

/-- `T₂(p) (class Φ) = class (p^{d+1} · T_{diag(p,1)}^{(-1)} Φ)`. -/
theorem hecke2_symbolClass_holds (p d : ℕ) [Fact p.Prime] (Φ : PeriodHom d) :
    hecke2 p d (symbolClass d Φ) = symbolClass d (((p : ℚ) ^ (d + 1)) • BinaryRationalHecke.rationalHecke
      (BinaryRationalHeckePrime.primeDiagonal p) (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) Φ) :=
  hecke2_symbolClass (homologyHomBridge_holds p d) Φ

/-- `T₂(p) (class Φ) = class (p⁻¹ · T^{(-1)}[C1] Φ)` for `C1 = diag(1/p, 1)`. -/
theorem hecke2_symbolClass_C1_holds (p d : ℕ) [Fact p.Prime] (Φ : PeriodHom d) :
    hecke2 p d (symbolClass d Φ) = symbolClass d ((p : ℚ)⁻¹ • BinaryRationalHecke.rationalHecke
      (HeckeHomology.C1 p) (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) Φ) :=
  hecke2_symbolClass_C1 BridgeDegreeCount.L4_holds Φ

end TernaryPeriodPolynomials.Argument.HeckeNormalization
