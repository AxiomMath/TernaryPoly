module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.AssemblyConventions
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.DictionaryTernary
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.DictionaryBinary

@[expose] public section


/-!
# Which normalization of `T₂(p)` do the printed coefficients of `eq:Hecke-formula` force?

Formalized by Claude Sonnet 5.5.
Paper: `eq:Hecke-formula`, "The Hecke transfer".

There are two candidate readings of the binary operator `T₂(p)` in `T₃(p,1) = p T₂(p) + p² I`.

* **Reading A (the paper's, right modules, column lattices):** `T₂(p) = hecke2 p (n+1) = heckeOp (binDatum p) (binMod (n+1)) 1`, the homology
  operator whose chain-level form is `[m ⊗ r] ↦ ∑_c [m·C_c ⊗ …] + [m·C_∞ ⊗ …]` (`DictionaryBinary`).  Then the printed identity is the theorem
  `hecke_formula_literal`.
* **Reading B (left modules, right cosets):** `T₂(p) = hecke2B p (n+1)`, the same cosets but transport by `diag(1,p)` instead of `diag(1/p,1)`.
  `hecke2_usual`: `hecke2 = p^{n+1} · hecke2B`.  `printed_formula_B_iff`: the printed identity with `hecke2B` holds at a class `y` **iff**
  `hecke2B (κ y) = 0`; consequently it holds for all classes iff `hecke2B = 0` (`printed_formula_B_all_iff`).  So the printed coefficients
  `(p, p²)` force Reading A (they are false for Reading B wherever `T₂` does not vanish; the coefficient there would be `p^{n+2}`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open CategoryTheory TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.AppendixBResidue

variable (p : ℕ) [Fact p.Prime]

/-- Reading B of `T₂(p)`: transport by `diag(1,p)` (left-module operator of the double coset of `diag(1,p)`). -/
def hecke2B (d : ℕ) : groupHomology (Dplain d) 1 →ₗ[ℚ] groupHomology (Dplain d) 1 :=
  (heckeOpG (binDatum p) (Cp p) (hf_Cp p) (binMod d) 1).hom

theorem hecke2_eq_hecke2B (d : ℕ) (x : groupHomology (Dplain d) 1) :
    hecke2 p d x = (p : ℚ) ^ d • hecke2B p d x :=
  hecke2_usual p d x

theorem printed_formula_B_iff (n : ℕ) (y : groupHomology (ResRep n) 3) :
    kappaLit n (shLit n ((heckeOp (primeDatum p) (Rep.of (TernaryPoly.SinglePole.residueAction n (-1))) 3).hom y)) =
      (p : ℚ) • hecke2B p (n + 1) (kappaLit n (shLit n y)) + ((p : ℚ) ^ 2) • kappaLit n (shLit n y) ↔
    hecke2B p (n + 1) (kappaLit n (shLit n y)) = 0 := by
  rw [hecke_formula_literal, hecke2_eq_hecke2B, smul_smul]
  have hp : (1 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hne : (p : ℚ) * (p : ℚ) ^ (n + 1) - (p : ℚ) ≠ 0 := by
    have : (p : ℚ) ^ (n + 1) > 1 := one_lt_pow₀ hp (Nat.succ_ne_zero n)
    nlinarith
  constructor
  · intro h
    have h2 : ((p : ℚ) * (p : ℚ) ^ (n + 1) - (p : ℚ)) • hecke2B p (n + 1) (kappaLit n (shLit n y)) = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr (add_right_cancel h)
    exact (smul_eq_zero.mp h2).resolve_left hne
  · intro h
    rw [h]; simp

theorem printed_formula_B_all_iff (n : ℕ) :
    (∀ y : groupHomology (ResRep n) 3,
      kappaLit n (shLit n ((heckeOp (primeDatum p) (Rep.of (TernaryPoly.SinglePole.residueAction n (-1))) 3).hom y)) =
        (p : ℚ) • hecke2B p (n + 1) (kappaLit n (shLit n y)) + ((p : ℚ) ^ 2) • kappaLit n (shLit n y)) ↔
    ∀ x : groupHomology (Dplain (n + 1)) 1, hecke2B p (n + 1) x = 0 := by
  constructor
  · intro h x
    have := (printed_formula_B_iff p n ((shLit n).symm ((kappaLit n).symm x))).mp
      (h ((shLit n).symm ((kappaLit n).symm x)))
    simpa using this
  · intro h y
    exact (printed_formula_B_iff p n y).mpr (h _)

end TernaryPeriodPolynomials.Argument.HeckeHomology
