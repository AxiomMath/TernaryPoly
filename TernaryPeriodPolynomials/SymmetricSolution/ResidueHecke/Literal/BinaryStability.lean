module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Literal.LiftableHomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.BinaryHecke

@[expose] public section


/-!
# Lemma 4.5: from the homology operator `T₃(p,1)` to the binary operator `T₂(p)` on `ℬ_{n+1}`

Formalized by Claude Sonnet 5.5.
Paper: Lemma 4.5 (`lem:residue-period`), proof (`eq:Hecke-formula`: `T₃(p,1) = p T₂(p) + p² I`; "Subtracting `p² I` and dividing by `p` gives binary stability").

`T2B p n` is the binary Hecke operator `T₂(p)` (the homology Hecke operator of `diag(1/p, 1)` on `H₁(GL₂(ℤ), Sym^{n+1})`)
transported to `ℬ_{n+1}` by the standard-edge isomorphism `periodEquivHomology'`.

The two inputs are NOT assumed anywhere in the library; they enter here as the
explicit hypotheses `hP : PHCompat n` (Lemma B.1, the residue comparison square) and `hH : HeckeFormula p n` (the identity
`eq:Hecke-formula` on literal homology, `HeckeHomology.hecke_formula_literal`).  This file proves that they imply the binary stability.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma45Literal

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.SinglePole TernaryPoly.SinglePoleCoordinate
open TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPeriodPolynomials.Argument.HeckeHomology TernaryPeriodPolynomials.Argument.FareyTree

/-- The rational module of binary forms of degree `d` over `GL₂(ℚ)` (trivial determinant twist). -/
def binModL (d : ℕ) : Rep.{0} ℚ TernaryPoly.BinaryModularSymbol.GL2 := Rep.of (BinaryModularSymbolCoefficients.homogeneousAction d 0)

/-- The binary Hecke operator `T₂(p)` on `H₁(GL₂(ℤ), Sym^{n+1})`. -/
def T2 (p : ℕ) [Fact p.Prime] (n : ℕ) :
    groupHomology (Dplain (n + 1)) 1 →ₗ[ℚ] groupHomology (Dplain (n + 1)) 1 :=
  (heckeOp (binDatum p) (binModL (n + 1)) 1).hom

/-- `T₂(p)` on the period space `ℬ_{n+1}`. -/
def T2B (p : ℕ) [Fact p.Prime] (n : ℕ) :
    OrdinaryResiduePeriod.periodSpace (n + 1) →ₗ[ℚ] OrdinaryResiduePeriod.periodSpace (n + 1) :=
  (Statements.BinaryDuality.periodEquivHomology' (n + 1)).toLinearMap ∘ₗ T2 p n ∘ₗ
    (Statements.BinaryDuality.periodEquivHomology' (n + 1)).symm.toLinearMap

/-- **`eq:Hecke-formula`** on literal homology: `κ ∘ Sh ∘ T₃(p,1) = (p T₂(p) + p²) ∘ κ ∘ Sh`. -/
def HeckeFormula (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∀ y : groupHomology (ResRep n) 3,
    kappaLit n (shLit n (T3 p n y)) =
      (p : ℚ) • T2 p n (kappaLit n (shLit n y)) + ((p : ℚ) ^ 2) • kappaLit n (shLit n y)

/-- In the literal residue coordinate, `T₃(p,1) = p T₂(p) + p² I` on `ℬ_{n+1}`. -/
theorem T3B_eq (p : ℕ) [Fact p.Prime] (n : ℕ) (hP : PHCompat n) (hH : HeckeFormula p n)
    (q : OrdinaryResiduePeriod.periodSpace (n + 1)) :
    T3B p n q = (p : ℚ) • T2B p n q + ((p : ℚ) ^ 2) • q := by
  obtain ⟨c, hc, hcomp⟩ := hP
  set x := (resHLitEquiv n).symm q with hx
  have hq : resHLitEquiv n x = q := (resHLitEquiv n).apply_symm_apply q
  have h1 : ∀ y, residuePeriodAlg n y = c • resHLitEquiv n y := fun y => by
    rw [hcomp y, resHLitEquiv_apply]
  have e1 : residuePeriodAlg n (T3 p n x) = c • T3B p n q := by
    rw [h1]
    simp [T3B, hx]
  have e2 : residuePeriodAlg n x = c • q := by rw [h1, hq]
  have e3 : residuePeriodAlg n (T3 p n x) =
      (p : ℚ) • T2B p n (residuePeriodAlg n x) + ((p : ℚ) ^ 2) • residuePeriodAlg n x := by
    have := congrArg (Statements.BinaryDuality.periodEquivHomology' (n + 1)) (hH x)
    simp only [map_add, map_smul] at this
    change _ = _ at this
    simpa [residuePeriodAlg, T2B] using this
  rw [e1, e2, map_smul] at e3
  apply smul_right_injective _ hc
  simp only
  rw [e3, smul_add, smul_comm c (p : ℚ), smul_comm c ((p : ℚ) ^ 2)]

/-- **Lemma 4.5, binary Hecke stability of `𝓛_n`**: `𝓛_n` is stable under the binary Hecke operator `T₂(p)`
(given the residue comparison `hP` and the identity `hH`). -/
theorem LnHom_binary_stable (p : ℕ) [Fact p.Prime] (n : ℕ) (hP : PHCompat n) (hH : HeckeFormula p n)
    (q : OrdinaryResiduePeriod.periodSpace (n + 1)) (hq : q ∈ LnHom n) : T2B p n q ∈ LnHom n := by
  have h3 := LnHom_hecke_stable p n q hq
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have e : T2B p n q = (p : ℚ)⁻¹ • T3B p n q + (-(p : ℚ)) • q := by
    rw [T3B_eq p n hP hH q]
    match_scalars
    · field_simp
    · field_simp
      ring
  rw [e]
  exact (LnHom n).add_mem ((LnHom n).smul_mem _ h3) ((LnHom n).smul_mem _ hq)

end TernaryPeriodPolynomials.Argument.Lemma45Literal
